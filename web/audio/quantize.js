// quantize.js: turn detected note onsets into a 24-slot phrase.
//
// PURE module: no browser APIs, no globals, no randomness, no mutation of
// inputs. It is meant to be easy to port to Lean and prove things about.
//
// Grid (contract with the Lean side):
//   3 slots per beat (shuffle / triplet grid), 4 beats per bar, 2 bars
//   => 24 slots. Slot 0 is beat 1 of bar 1.
//   phrase[i] is null (no note starts in slot i) or a MIDI pitch 40..88.
//
// Algorithm (deliberately simple):
//   1. Sort onsets by time (stable).
//   2. For each onset: corrected = time - latency - phraseStart.
//      slot = round(corrected / slotDuration), ties round up.
//   3. Reject if pitch is missing / not an integer / outside 40..88.
//   4. Reject if slot < 0 or slot >= 24 (outside the 2 bars).
//   5. Reject if the slot is already taken (the FIRST onset wins).
//   6. onGrid = |offset| <= tolerance. With strict=true, off-grid notes are
//      rejected instead of placed (default false: place them anyway and let
//      the feedback say "late"/"early").

export const SLOTS_PER_BEAT = 3;
export const BEATS_PER_BAR = 4;
export const BARS = 2;
export const SLOTS_PER_BAR = SLOTS_PER_BEAT * BEATS_PER_BAR; // 12
export const PHRASE_SLOTS = SLOTS_PER_BAR * BARS; // 24
export const MIDI_MIN = 40; // E2
export const MIDI_MAX = 88; // E6

/** Duration of one triplet slot in seconds. 80 BPM -> 0.25 s. */
export function slotDuration(bpm) {
  return 60 / bpm / SLOTS_PER_BEAT;
}

/** Duration of the whole 2-bar phrase in seconds. */
export function phraseDuration(bpm) {
  return slotDuration(bpm) * PHRASE_SLOTS;
}

/** True if m is an integer MIDI pitch inside the allowed range. */
export function isValidMidi(m) {
  return Number.isInteger(m) && m >= MIDI_MIN && m <= MIDI_MAX;
}

/** True if p satisfies the JSON contract: 24 entries, each null or valid MIDI. */
export function isValidPhrase(p) {
  return (
    Array.isArray(p) &&
    p.length === PHRASE_SLOTS &&
    p.every((x) => x === null || isValidMidi(x))
  );
}

/** Round to 0.01 ms and turn -0 into 0 so the output is tidy. */
function tidyMs(x) {
  return Math.round(x * 100) / 100 || 0;
}

/**
 * Quantize onsets to the 24-slot grid.
 *
 * @param {{time:number, midi:(number|null)}[]} onsets
 *   time: seconds on the same clock as phraseStart (AudioContext time).
 * @param {object} opts
 * @param {number} opts.phraseStart  time of slot 0 (beat 1), seconds
 * @param {number} opts.bpm          tempo in beats per minute (> 0)
 * @param {number} [opts.latency=0]  input latency in seconds, subtracted from every onset
 * @param {number} [opts.toleranceMs=80]  |offset| <= this counts as on-grid
 * @param {boolean} [opts.strict=false]   reject off-grid notes instead of placing them
 * @returns {{
 *   phrase: (number|null)[],
 *   notes: {time:number, midi:number, slot:number, offsetMs:number, onGrid:boolean}[],
 *   rejected: {time:number, midi:(number|null), reason:string, slot?:number, offsetMs?:number}[]
 * }}
 *   notes: kept notes in time order. time is the raw (uncorrected) onset time.
 *   offsetMs: corrected time minus the slot's ideal time; negative = early.
 */
/**
 * Fix pluck-attack misreadings. Right at the pick attack an acoustic guitar's
 * body boom can make the detector read a note 1/3 (or 1/2, 2/3, 1/4) of the
 * real pitch: E4 reads as A2. The real pitch then shows up as a "legato"
 * onset within a few hundred ms. When a legato onset follows a note within
 * `windowMs` and its frequency is 1.5, 2, 3 or 4 times that note's (within 3%),
 * give the note the legato's pitch and drop the legato onset.
 * Returns a new array; the input is not changed.
 */
export function mergeHarmonicPairs(onsets, windowMs = 250) {
  const sorted = [...onsets].sort((a, b) => a.time - b.time);
  const out = [];
  for (const e of sorted) {
    const prev = out[out.length - 1];
    if (e.kind === "legato" && prev && prev.midi != null && e.midi != null && prev.freq > 0 && e.freq > 0 &&
        (e.time - prev.time) * 1000 <= windowMs) {
      const r = e.freq / prev.freq;
      if ([1.5, 2, 3, 4].some((k) => Math.abs(r / k - 1) <= 0.03)) {
        out[out.length - 1] = { ...prev, midi: e.midi, freq: e.freq, fixedFrom: prev.midi };
        continue;
      }
    }
    out.push(e);
  }
  return out;
}

/**
 * Swing-aware slot choice. Blues players swing their eighth notes anywhere
 * from straight (the "and" halfway through the beat) to full triplet (2/3 of
 * the way). So within a beat: near the start -> slot 0; only clearly near 1/3
 * of the beat -> slot 1; from there to 5/6 of the beat -> slot 2 (the "and");
 * after that -> the next beat.
 */
export function swingSlot(slotFloat) {
  const beat = Math.floor(slotFloat / 3);
  const f = slotFloat / 3 - beat; // 0..1 within the beat
  if (f < 0.23) return 3 * beat;
  if (f < 0.43) return 3 * beat + 1;
  if (f < 5 / 6) return 3 * beat + 2;
  return 3 * beat + 3;
}

export function quantize(onsets, opts) {
  const { phraseStart, bpm, latency = 0, toleranceMs = 80, strict = false } = opts ?? {};
  if (!Number.isFinite(phraseStart)) throw new TypeError("phraseStart must be a finite number");
  if (!(Number.isFinite(bpm) && bpm > 0)) throw new TypeError("bpm must be a positive number");
  if (!Number.isFinite(latency)) throw new TypeError("latency must be a finite number");
  if (!(Number.isFinite(toleranceMs) && toleranceMs >= 0)) throw new TypeError("toleranceMs must be >= 0");
  if (!Array.isArray(onsets)) throw new TypeError("onsets must be an array");

  const slotDur = slotDuration(bpm);
  const phrase = new Array(PHRASE_SLOTS).fill(null);
  const notes = [];
  const rejected = [];

  // Stable sort by time; copy so we never mutate the caller's array.
  // Very quiet notes (a string ringing along, the band leaking in) are dropped:
  // anything more than minRelDb below the loudest note of the phrase.
  let kept = opts?.mergeHarmonics === false ? onsets : mergeHarmonicPairs(onsets);
  const minRelDb = opts?.minRelDb ?? 20;
  const loudest = Math.max(0, ...kept.filter((o) => o.midi != null && o.level > 0).map((o) => o.level));
  if (loudest > 0) {
    const floor = loudest * Math.pow(10, -minRelDb / 20);
    kept = kept.filter((o) => {
      if (o.midi != null && o.level > 0 && o.level < floor) {
        rejected.push({ time: o.time, midi: o.midi, reason: "too-quiet" });
        return false;
      }
      return true;
    });
  }
  const sorted = kept
    .map((o, i) => ({ o, i }))
    .sort((a, b) => a.o.time - b.o.time || a.i - b.i)
    .map((x) => x.o);

  for (const { time, midi } of sorted) {
    if (!Number.isFinite(time)) {
      rejected.push({ time, midi: midi ?? null, reason: "bad-time" });
      continue;
    }
    const corrected = time - latency - phraseStart;
    const slotFloat = corrected / slotDur;
    const slot = opts?.swing === false ? Math.floor(slotFloat + 0.5) : swingSlot(slotFloat);
    const offsetMs = tidyMs((corrected - slot * slotDur) * 1000);

    if (!isValidMidi(midi)) {
      rejected.push({ time, midi: midi ?? null, reason: "no-valid-pitch", slot, offsetMs });
      continue;
    }
    if (slot < 0 || slot >= PHRASE_SLOTS) {
      rejected.push({ time, midi, reason: "outside-phrase", slot, offsetMs });
      continue;
    }
    const onGrid = Math.abs(offsetMs) <= toleranceMs;
    if (strict && !onGrid) {
      rejected.push({ time, midi, reason: "off-grid", slot, offsetMs });
      continue;
    }
    if (phrase[slot] !== null) {
      rejected.push({ time, midi, reason: "slot-taken", slot, offsetMs });
      continue;
    }
    phrase[slot] = midi;
    notes.push({ time, midi, slot, offsetMs, onGrid });
  }

  return { phrase, notes, rejected };
}
