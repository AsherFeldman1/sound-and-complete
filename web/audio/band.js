// band.js: a small synthesized blues band (drums, bass, keys) plus a lead
// guitar voice, all in Web Audio. No samples, no dependencies.
//
// Music: 12-bar minor blues in A, shuffle feel. The grid is triplets
// (3 slots per beat, 12 per bar); the swing comes from playing on slots
// 0 and 2 of each beat (long-short).
//
// Layout:
//   songEvents()  PURE: the list of musical events of the backing track
//                 (tested in band.test.mjs).
//   renderPluck() PURE: Karplus-Strong plucked string into a Float32Array.
//   phraseNotes() PURE: turns a 24-slot phrase into notes with durations.
//   Band          turns events into sound. The backing track uses the
//                 lookahead scheduler pattern of metronome.js: a 25 ms timer
//                 wakes up and schedules events ~0.2 s ahead on the
//                 AudioContext clock.
//
// Signal flow:
//   drums/hats/bass/keys/organ busses -> backing (volume) -> glue comp
//   lead: pluck -> drive -> amp/cab EQ -> leadOut -> glue comp
//   sends from every bus -> procedural room reverb -> glue comp
//   glue comp -> limiter -> master -> destination

const LOOKAHEAD_S = 0.2; // schedule this far ahead
const TIMER_MS = 25; // how often the scheduler wakes up

// ---------------------------------------------------------------- chords

// Pitch classes: C=0 ... A=9, B=11.
// `tones` are the keyboard voicing (mid register, smooth voice leading:
// Am7 -> Dm7 moves two voices by a step, Dm7 -> E7 moves every voice by a
// half step). `bassRoot` is the bass player's root. `scale` lists the pitch
// classes the bass may use (Dorian / Mixolydian of the chord root).
const AM7 = Object.freeze({
  name: "Am7", root: 57, bassRoot: 33, // A1
  tones: Object.freeze([57, 60, 64, 67]), // A3 C4 E4 G4
  scale: Object.freeze([9, 11, 0, 2, 4, 6, 7]), // A Dorian
});
const DM7 = Object.freeze({
  name: "Dm7", root: 50, bassRoot: 38, // D2
  tones: Object.freeze([57, 60, 62, 65]), // A3 C4 D4 F4
  scale: Object.freeze([2, 4, 5, 7, 9, 11, 0]), // D Dorian
});
const E7 = Object.freeze({
  name: "E7", root: 52, bassRoot: 40, // E2
  tones: Object.freeze([56, 59, 62, 64]), // G#3 B3 D4 E4
  scale: Object.freeze([4, 6, 8, 9, 11, 1, 2]), // E Mixolydian
});

/** The 12 bars of the progression, bar 1 first. */
export const CHORDS = Object.freeze([
  AM7, AM7, AM7, AM7,
  DM7, DM7, AM7, AM7,
  E7, DM7, AM7, E7,
]);

// ---------------------------------------------------------------- helpers

const clamp = (x, lo, hi) => Math.min(hi, Math.max(lo, x));
const mtof = (m) => 440 * Math.pow(2, (m - 69) / 12);

/** Small seeded PRNG (mulberry32). Returns 0..1. */
function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** Timing facts of a song (all seconds, relative to the count-in start). */
export function songLayout({ bpm = 80, bars = 12, countInBars = 1 } = {}) {
  const beat = 60 / bpm;
  const slot = beat / 3;
  const barDur = 4 * beat;
  const songStart = countInBars * barDur;
  return { beat, slot, barDur, songStart, endTime: songStart + bars * barDur };
}

// ---------------------------------------------------------------- events

// Bass line per bar, in semitones above the bar's bass root.
// Classic shuffle walk: root, 5th, 6th, flat 7th (up), or back down.
const BASS_UP = [0, 7, 9, 10];
const BASS_DOWN = [12, 10, 9, 7];

/**
 * All events of the backing track. Times are seconds from `startTime`
 * (the count-in starts at 0, bar 1 starts at songLayout().songStart).
 * Each event: { time, instrument, vel, bar, midi?, dur? }.
 *   instrument: "sticks" | "hat" | "kick" | "snare" | "crash" | "bass" | "keys" | "organ"
 *   bar: 1..bars for the song, <= 0 for count-in bars.
 * Deterministic: the small humanization uses a fixed seed.
 */
export function songEvents({ bpm = 80, bars = 12, countInBars = 1 } = {}) {
  const { beat, slot, barDur, songStart } = songLayout({ bpm, bars, countInBars });
  const rnd = mulberry32(0xb1e5);
  const jit = (ms) => (rnd() * 2 - 1) * (ms / 1000); // +/- ms
  const vary = (v, amt = 0.08) => clamp(v * (1 + (rnd() * 2 - 1) * amt), 0.05, 1);
  const ev = [];
  const push = (e) => ev.push(e);

  // Count-in: stick clicks on every beat (beat 1 accented) and a soft
  // swung hi-hat on the last triplet so the shuffle feel is set up.
  for (let b = 0; b < countInBars; b++) {
    const bar = b - countInBars + 1;
    for (let k = 0; k < 4; k++) {
      const t = b * barDur + k * beat;
      push({ time: t, instrument: "sticks", vel: k === 0 ? 1 : 0.7, bar });
      push({ time: t + 2 * slot, instrument: "hat", vel: 0.3, dur: 0.05, bar });
    }
  }

  for (let i = 0; i < bars; i++) {
    const bar = i + 1;
    const pos = i % 12; // position in the 12-bar form
    const c = CHORDS[pos];
    const prev = CHORDS[(pos + 11) % 12];
    const t0 = songStart + i * barDur;
    const at = (k, s) => t0 + k * beat + s * slot; // beat k (0..3), slot s (0..2)
    const turnaround = pos === 11;

    // --- drums
    if (pos === 0) push({ time: t0, instrument: "crash", vel: i === 0 ? 0.8 : 0.6, bar });
    push({ time: at(0, 0) + jit(2), instrument: "kick", vel: vary(0.95), bar });
    push({ time: at(1, 2) + jit(3), instrument: "kick", vel: vary(0.4), bar }); // swung pickup into 3
    push({ time: at(2, 0) + jit(2), instrument: "kick", vel: vary(0.8), bar });
    push({ time: at(1, 0) + jit(3), instrument: "snare", vel: vary(0.85), bar });
    push({ time: at(2, 2) + jit(4), instrument: "snare", vel: vary(0.15, 0.3), bar }); // ghost
    push({ time: at(3, 0) + jit(3), instrument: "snare", vel: vary(0.9), bar });
    if (turnaround) {
      // little triplet fill into the top of the form
      push({ time: at(3, 1) + jit(3), instrument: "snare", vel: vary(0.45), bar });
      push({ time: at(3, 2) + jit(3), instrument: "snare", vel: vary(0.6), bar });
    }
    for (let k = 0; k < 4; k++) {
      push({ time: at(k, 0) + jit(4), instrument: "hat", vel: vary(k % 2 ? 0.6 : 0.5), dur: 0.05, bar });
      if (turnaround && k === 3) continue; // the snare fill owns this slot
      const open = k === 3 && pos % 4 === 3; // open hat at the end of each 4-bar line
      push({ time: at(k, 2) + jit(4), instrument: "hat", vel: vary(open ? 0.45 : 0.3), dur: open ? 0.3 : 0.04, bar });
    }

    // --- bass: long note on the beat, short swung repeat on slot 2
    const pattern = c === prev && i % 2 === 1 ? BASS_DOWN : BASS_UP;
    for (let k = 0; k < 4; k++) {
      const midi = c.bassRoot + pattern[k];
      push({ time: at(k, 0) + jit(3), instrument: "bass", midi, dur: 2 * slot * 0.92, vel: vary(k === 0 ? 1 : 0.85, 0.05), bar });
      push({ time: at(k, 2) + jit(3), instrument: "bass", midi, dur: slot * 0.8, vel: vary(0.55, 0.1), bar });
    }

    // --- keys: e-piano stabs (slightly rolled), and a quiet organ pad
    const hits = turnaround
      ? [[0, 0, 1.2, 0.7], [2, 2, 0.35, 0.5], [3, 2, 0.4, 0.6]] // push into bar 1
      : [[0, 0, 1.3, 0.65], [1, 2, 0.35, 0.45], [2, 2, 0.9, 0.5]];
    for (const [k, s, beats, v] of hits) {
      const t = at(k, s) + jit(5);
      const roll = beats > 1 ? 0.012 : 0.004; // long chords are rolled a bit more
      const hv = vary(v);
      c.tones.forEach((midi, j) => {
        push({ time: t + j * roll, instrument: "keys", midi, dur: beats * beat, vel: vary(hv, 0.05), bar });
      });
    }
    for (const midi of c.tones) {
      push({ time: t0, instrument: "organ", midi, dur: barDur, vel: 0.5, bar });
    }
  }

  ev.forEach((e) => { e.time = Math.max(0, e.time); });
  ev.sort((a, b) => a.time - b.time);
  return ev;
}

// ---------------------------------------------------------------- lead

/**
 * Turn a phrase (array of null | MIDI, one entry per triplet slot) into
 * notes. Each note rings until the next note, or 1.5 beats at most.
 * Returns [{ slot, time, midi, dur, cut }]; `cut` = ended by the next note.
 */
export function phraseNotes(phrase, bpm) {
  const beat = 60 / bpm;
  const slot = beat / 3;
  const maxDur = 1.5 * beat;
  const notes = [];
  for (let i = 0; i < phrase.length; i++) {
    const midi = phrase[i];
    if (midi == null) continue;
    let j = i + 1;
    while (j < phrase.length && phrase[j] == null) j++;
    const gap = j < phrase.length ? (j - i) * slot : Infinity;
    notes.push({ slot: i, time: i * slot, midi, dur: Math.min(gap, maxDur), cut: gap <= maxDur });
  }
  return notes;
}

/**
 * Phrase a lick like a guitarist. PURE.
 *
 * Splits the notes into picked groups. Within a quick run (next note at most
 * 2 slots later and at most 4 semitones away), only the first note is picked;
 * the rest are hammer-ons / pull-offs (an instant pitch change on the ringing
 * string), or short slides when there is a little time between them. A repeated
 * pitch is always picked again. Runs are re-picked after 5 notes.
 * The longest held A, D or E (the usual targets in A minor) is bent up into
 * from a whole step below.
 * @returns {Array<{start: object, notes: object[], moves: Array<{time, midi, kind}>, bend: number}>}
 *   groups; `moves` are the pitch changes after the picked note (kind "hammer" or "slide");
 *   `bend` is the bend's starting offset in semitones (0 = no bend).
 */
export function articulate(notes, beat) {
  const slot = beat / 3;
  const groups = [];
  let g = null;
  for (const n of notes) {
    const prev = g?.notes[g.notes.length - 1];
    const legato = prev && n.slot - prev.slot <= 2 && n.midi !== prev.midi &&
      Math.abs(n.midi - prev.midi) <= 4 && g.notes.length < 5;
    if (legato) {
      g.notes.push(n);
      g.moves.push({ time: n.time, midi: n.midi, kind: n.slot - prev.slot >= 2 ? "slide" : "hammer", glide: Math.min(0.07, 0.6 * slot) });
    } else {
      g = { start: n, notes: [n], moves: [], bend: 0 };
      groups.push(g);
    }
  }
  // One bend per phrase: the longest held, picked target note.
  const targets = groups.filter((x) => x.notes.length === 1 && x.start.dur >= 0.5 * beat && [2, 4, 9].includes(((x.start.midi % 12) + 12) % 12));
  if (targets.length) targets.reduce((a, b) => (b.start.dur > a.start.dur ? b : a)).bend = -2;
  return groups;
}

/**
 * Karplus-Strong plucked string. PURE.
 * The delay loop has a period of N - 0.5 samples; the caller plays the
 * buffer at `rate` to land exactly on `freq`.
 * - excitation: lowpassed noise (brighter for higher velocity) through a
 *   pick-position comb filter;
 * - loop filter: two-point average with a loss tuned so the note fades by
 *   60 dB in ~4 s (low strings) to ~1.5 s (high strings);
 * - output: a second comb for the magnetic pickup position ("electric" tone).
 * @returns {{ data: Float32Array, rate: number }}
 */
export function renderPluck(sampleRate, freq, dur, { vel = 1, seed = 1 } = {}) {
  const rnd = mulberry32(seed);
  const period = sampleRate / freq;
  const N = Math.max(4, Math.floor(period + 0.5));
  const rate = (N - 0.5) / period;
  const len = Math.ceil(dur * sampleRate * rate) + N;

  const midi = 69 + 12 * Math.log2(freq / 440);
  const t60 = clamp(4.2 - (midi - 40) * 0.055, 1.2, 4.5);
  const rho = Math.pow(10, -3 / (freq * t60)); // loss per round trip

  // Excitation: smoothed noise, then a pick-position comb.
  const exc = new Float32Array(N);
  const bright = 0.1 + 0.22 * clamp(vel, 0, 1); // soft pick: darker noise burst
  let lp = 0;
  for (let i = 0; i < N; i++) {
    lp += bright * (rnd() * 2 - 1 - lp);
    exc[i] = lp;
  }
  const pp = Math.max(1, Math.round(N * 0.17));
  const line = new Float32Array(N);
  let mean = 0;
  for (let i = 0; i < N; i++) {
    line[i] = exc[i] - exc[(i - pp + N) % N];
    mean += line[i];
  }
  mean /= N;
  for (let i = 0; i < N; i++) line[i] -= mean;

  // The string loop.
  const y = new Float32Array(len);
  let idx = 0;
  for (let n = 0; n < len; n++) {
    const nxt = idx + 1 === N ? 0 : idx + 1;
    const a = line[idx];
    y[n] = a;
    line[idx] = rho * 0.5 * (a + line[nxt]);
    idx = nxt;
  }

  // Neck-pickup comb (gentle), then a lowpass that closes over the first
  // ~0.15 s: a real string loses its highs fast, which keeps it from "pinging".
  const q = Math.max(1, Math.round(N * 0.22));
  const out = new Float32Array(len);
  let peak = 1e-9;
  let lpOut = 0;
  const fStart = Math.min(5200, freq * 9), fEnd = Math.min(2400, freq * 3.2);
  const tau = 0.15 * sampleRate;
  for (let n = 0; n < len; n++) {
    const x = y[n] - 0.2 * (n >= q ? y[n - q] : 0);
    const fc = fEnd + (fStart - fEnd) * Math.exp(-n / tau);
    lpOut += (1 - Math.exp((-2 * Math.PI * fc) / sampleRate)) * (x - lpOut);
    out[n] = lpOut;
    peak = Math.max(peak, Math.abs(out[n]));
  }
  const fade = Math.round(0.004 * sampleRate); // 4 ms: no click on the attack
  const norm = (0.8 * clamp(vel, 0, 1)) / peak;
  for (let n = 0; n < len; n++) out[n] *= norm * (n < fade ? n / fade : 1);
  return { data: out, rate };
}

// ---------------------------------------------------------------- Band

/** Procedural room impulse response: stereo decaying noise that gets darker over time. */
function makeImpulse(ctx, seconds = 2.0, decay = 3.4) {
  const sr = ctx.sampleRate;
  const len = Math.floor(sr * seconds);
  const pre = Math.floor(sr * 0.012); // pre-delay
  const buf = ctx.createBuffer(2, len, sr);
  for (let ch = 0; ch < 2; ch++) {
    const d = buf.getChannelData(ch);
    let lp = 0;
    for (let i = pre; i < len; i++) {
      const t = (i - pre) / sr;
      const a = 0.08 + 0.6 * Math.exp(-t * 2.5); // lowpass closes as the tail decays
      lp += a * (Math.random() * 2 - 1 - lp);
      d[i] = lp * Math.exp(-t * decay) * Math.min(1, t / 0.004);
    }
  }
  return buf;
}

/** Soft-clip curve. `bias` makes it asymmetric (even harmonics, tube-like). */
function makeCurve(drive, bias = 0) {
  const n = 2048;
  const c = new Float32Array(n);
  const norm = Math.tanh(drive + bias) - Math.tanh(bias);
  for (let i = 0; i < n; i++) {
    const x = (i / (n - 1)) * 2 - 1;
    c[i] = (Math.tanh(drive * x + bias) - Math.tanh(bias)) / norm;
  }
  return c;
}

export class Band {
  constructor(ctx, destination = ctx.destination) {
    this.ctx = ctx;
    this.voices = new Set(); // every playing/scheduled note, for stop()
    this.timers = new Set();
    this._seed = 1;

    // Master: gentle glue compressor, then a safety limiter.
    const glue = ctx.createDynamicsCompressor();
    glue.threshold.value = -16;
    glue.knee.value = 12;
    glue.ratio.value = 2.5;
    glue.attack.value = 0.02;
    glue.release.value = 0.25;
    const limiter = ctx.createDynamicsCompressor();
    limiter.threshold.value = -3;
    limiter.knee.value = 0;
    limiter.ratio.value = 20;
    limiter.attack.value = 0.002;
    limiter.release.value = 0.1;
    this.master = ctx.createGain();
    this.master.gain.value = 0.85;
    glue.connect(limiter).connect(this.master).connect(destination);
    this.glue = glue;

    // Room reverb.
    this.reverb = ctx.createConvolver();
    this.reverb.buffer = makeImpulse(ctx);
    const verbReturn = ctx.createGain();
    verbReturn.gain.value = 0.9;
    this.reverb.connect(verbReturn).connect(glue);

    // Backing bus (its gain = volume) and its reverb send (also = volume).
    this._volume = 0.7;
    this.backing = ctx.createGain();
    this.backing.gain.value = this._volume;
    this.backing.connect(glue);
    this.backingSend = ctx.createGain();
    this.backingSend.gain.value = this._volume;
    this.backingSend.connect(this.reverb);

    // Instrument busses.
    this.drumBus = this._bus(ctx.createGain(), { gain: 1, pan: 0, send: 0.18 });
    this.hatBus = this._bus(ctx.createGain(), { gain: 1, pan: 0.3, send: 0.1 });

    // Bass: soft saturation for audible harmonics on small speakers, then lowpass.
    this.bassIn = ctx.createGain();
    const bassSat = ctx.createWaveShaper();
    bassSat.curve = makeCurve(1.8);
    bassSat.oversample = "2x";
    const bassLp = ctx.createBiquadFilter();
    bassLp.type = "lowpass";
    bassLp.frequency.value = 900;
    bassLp.Q.value = 0.6;
    this.bassIn.connect(bassSat).connect(bassLp);
    this._bus(bassLp, { gain: 0.6, pan: 0, send: 0.04 });

    // Keys (e-piano): lowpass, gentle tremolo, panned a little left.
    this.keysIn = ctx.createGain();
    const keysLp = ctx.createBiquadFilter();
    keysLp.type = "lowpass";
    keysLp.frequency.value = 2400;
    keysLp.Q.value = 0.5;
    const trem = ctx.createGain();
    trem.gain.value = 0.88;
    const tremLfo = ctx.createOscillator();
    tremLfo.frequency.value = 4.3;
    const tremDepth = ctx.createGain();
    tremDepth.gain.value = 0.1;
    tremLfo.connect(tremDepth).connect(trem.gain);
    tremLfo.start();
    this.keysIn.connect(keysLp).connect(trem);
    this._bus(trem, { gain: 1, pan: -0.25, send: 0.3 });

    // Organ pad: dark and quiet, panned a little right.
    this.organIn = ctx.createGain();
    const organLp = ctx.createBiquadFilter();
    organLp.type = "lowpass";
    organLp.frequency.value = 1600;
    this.organIn.connect(organLp);
    this._bus(organLp, { gain: 1, pan: 0.2, send: 0.25 });
    // drawbar-like spectrum: fundamental, octave, a bit of 3rd harmonic
    this.organWave = ctx.createPeriodicWave(
      new Float32Array([0, 0, 0, 0, 0]),
      new Float32Array([0, 1, 0.3, 0.12, 0.04]),
    );
    this.bassWave = ctx.createPeriodicWave(
      new Float32Array([0, 0, 0, 0, 0]),
      new Float32Array([0, 1, 0.35, 0.12, 0.05]),
    );

    // Lead guitar: drive -> tube-ish shaper -> amp/cab EQ, slapback delay.
    this.leadIn = ctx.createGain();
    const leadHp = ctx.createBiquadFilter();
    leadHp.type = "highpass";
    leadHp.frequency.value = 90;
    const drive = ctx.createGain();
    drive.gain.value = 1.1;
    const shaper = ctx.createWaveShaper();
    shaper.curve = makeCurve(2.2, 0.25);
    shaper.oversample = "4x";
    const dcBlock = ctx.createBiquadFilter();
    dcBlock.type = "highpass";
    dcBlock.frequency.value = 60;
    const mid = ctx.createBiquadFilter(); // mid hump, sits above the keys
    mid.type = "peaking";
    mid.frequency.value = 650;
    mid.Q.value = 0.7;
    mid.gain.value = 3;
    const presence = ctx.createBiquadFilter();
    presence.type = "peaking";
    presence.frequency.value = 3200;
    presence.Q.value = 0.8;
    presence.gain.value = -3; // tame the "ping" region
    const cab = ctx.createBiquadFilter(); // speaker cabinet rolloff
    cab.type = "lowpass";
    cab.frequency.value = 2900;
    cab.Q.value = 0.6;
    this.leadOut = ctx.createGain();
    this.leadOut.gain.value = 0.55;
    this.leadIn.connect(leadHp).connect(drive).connect(shaper).connect(dcBlock)
      .connect(mid).connect(presence).connect(cab).connect(this.leadOut);
    this.leadOut.connect(glue);
    const leadSend = ctx.createGain();
    leadSend.gain.value = 0.22;
    this.leadOut.connect(leadSend).connect(this.reverb);
    // Subtle tempo-synced echo (kept low so its tail barely reaches the mic).
    this.leadDelay = ctx.createDelay(2);
    this.leadDelay.delayTime.value = 0.5;
    const fb = ctx.createGain();
    fb.gain.value = 0.2;
    const delayLp = ctx.createBiquadFilter();
    delayLp.type = "lowpass";
    delayLp.frequency.value = 2500;
    const delayMix = ctx.createGain();
    delayMix.gain.value = 0.05;
    this.leadOut.connect(this.leadDelay).connect(delayLp).connect(fb).connect(this.leadDelay);
    delayLp.connect(delayMix).connect(glue);

    // 3 s of white noise, shared by all drum voices (random start offsets).
    const nLen = Math.round(3 * ctx.sampleRate);
    this.noise = ctx.createBuffer(1, nLen, ctx.sampleRate);
    const nd = this.noise.getChannelData(0);
    for (let i = 0; i < nLen; i++) nd[i] = Math.random() * 2 - 1;

    // Recorded samples (loadSamples). Until they load, the synth voices play.
    this.samples = null;
    // Each bus: a high-pass so the low end stays clean (bass and kick own it).
    const hp = (freq) => {
      const f = ctx.createBiquadFilter();
      f.type = "highpass";
      f.frequency.value = freq;
      f.Q.value = 0.7;
      return f;
    };
    const into = (node, filt) => { node.connect(filt); return node; };
    const bassHp = hp(38), pianoHp = hp(170), organHp = hp(200), kickHp = hp(35);
    this.sBass = into(ctx.createGain(), bassHp);
    this._bus(bassHp, { gain: 0.55, pan: 0, send: 0.02 });
    this.sPiano = into(ctx.createGain(), pianoHp);
    this._bus(pianoHp, { gain: 0.4, pan: -0.25, send: 0.25 });
    this.sOrgan = into(ctx.createGain(), organHp);
    this._bus(organHp, { gain: 0.1, pan: 0.25, send: 0.2 });
    this.sKick = into(ctx.createGain(), kickHp);
    this._bus(kickHp, { gain: 0.75, pan: 0, send: 0.06 });
    this.sSnare = this._bus(ctx.createGain(), { gain: 0.55, pan: 0.05, send: 0.2 });
    this.sHat = this._bus(ctx.createGain(), { gain: 0.32, pan: 0.3, send: 0.08 });
    // Lead guitar samples are real recordings: skip the synth's drive/EQ, keep
    // a gentle lowpass, the room reverb and the small echo (through leadOut).
    this.leadClean = ctx.createGain();
    const leadWarm = ctx.createBiquadFilter();
    leadWarm.type = "lowpass";
    leadWarm.frequency.value = 5000;
    leadWarm.Q.value = 0.5;
    this.leadClean.connect(leadWarm).connect(this.leadOut);
    // Guitars recorded direct (no amp) go through an amp + speaker cabinet model.
    this.ampClean = this._amp({ drive: 1.3, mid: 2, bright: 1.5 });
    this.ampBlues = this._amp({ drive: 3.2, mid: 4, bright: 0 });
  }

  /** A small guitar amp: tone shaping, soft clipping, then a 1x12 speaker cabinet. */
  _amp({ drive, mid, bright }) {
    const ctx = this.ctx;
    const biquad = (type, f, q, g = 0) => {
      const b = ctx.createBiquadFilter();
      b.type = type; b.frequency.value = f; b.Q.value = q; b.gain.value = g;
      return b;
    };
    const input = ctx.createGain(); // the shaper curve itself holds the drive
    const pre = biquad("highpass", 90, 0.7); // keep the low end tight before clipping
    const midBoost = biquad("peaking", 750, 0.8, mid); // warm, vocal mids
    const shaper = ctx.createWaveShaper();
    shaper.curve = makeCurve(drive);
    shaper.oversample = "4x";
    const post = ctx.createGain();
    post.gain.value = Math.tanh(drive) / drive; // undo the curve's small-signal gain
    const presence = biquad("peaking", 2200, 1, bright);
    const thump = biquad("peaking", 120, 1.2, 2.5); // speaker resonance
    const cab1 = biquad("lowpass", 4800, 0.9); // two lowpasses = steep speaker roll-off
    const cab2 = biquad("lowpass", 5600, 0.6);
    const fizz = biquad("peaking", 3800, 2.5, -4);
    input.connect(pre).connect(midBoost).connect(shaper).connect(post)
      .connect(presence).connect(thump).connect(cab1).connect(cab2).connect(fizz).connect(this.leadOut);
    return input;
  }

  /** Load the recorded instrument samples (web/samples/). Falls back to the
   * synth voices if anything fails. Resolves to true when samples are in use. */
  async loadSamples(choice, base = "samples/") {
    try {
      const { loadBandSamples } = await import("./sampler.js");
      this.samples = await loadBandSamples(this.ctx, choice, base);
      return true;
    } catch (e) {
      console.warn("band: samples unavailable, using synth voices:", e);
      return false;
    }
  }

  /** Master volume of the backing track, 0..1 (lead not affected). */
  set volume(v) {
    this._volume = clamp(Number(v) || 0, 0, 1);
    const t = this.ctx.currentTime;
    this.backing.gain.setTargetAtTime(this._volume, t, 0.03);
    this.backingSend.gain.setTargetAtTime(this._volume, t, 0.03);
  }
  get volume() {
    return this._volume;
  }

  /**
   * Schedule count-in + `bars` bars of backing, starting at `startTime`.
   * @returns {{ songStart: number, endTime: number }} AudioContext times of
   *   bar 1 beat 1 and of the end of the last bar.
   */
  scheduleSong({ startTime, bpm = 80, bars = 12, countInBars = 1, only } = {}) {
    const t0 = startTime ?? this.ctx.currentTime + 0.1;
    let events = songEvents({ bpm, bars, countInBars });
    if (only) events = events.filter((e) => only.includes(e.instrument)); // previews
    const lay = songLayout({ bpm, bars, countInBars });
    let i = 0;
    const tick = () => {
      const now = this.ctx.currentTime;
      const horizon = now + LOOKAHEAD_S;
      while (i < events.length) {
        const e = events[i];
        const t = t0 + e.time;
        if (t > horizon) break;
        i++;
        if (t < now - 0.03) continue; // too late (e.g. tab was asleep): skip
        this._play(e, Math.max(t, now));
      }
      if (i >= events.length) {
        clearInterval(id);
        this.timers.delete(id);
      }
    };
    const id = setInterval(tick, TIMER_MS);
    this.timers.add(id);
    tick();
    return { songStart: t0 + lay.songStart, endTime: t0 + lay.endTime };
  }

  /**
   * Play a 24-slot phrase on the lead guitar, slot i at startTime + i * slotDur.
   * Scheduled all at once (at most 24 notes).
   */
  /** Play notes from a recorded guitar, phrased by articulate(): one pick per
   * group, hammer-ons / slides by moving the ringing note's pitch, one bend. */
  _playArticulated(notes, startTime, beat, gain) {
    const amp = this.samples.guitar.option.amp;
    // The shared amp (amp.js, the Deluxe capture) when the app provides one.
    const dest = this.leadAmpIn ?? (amp === "blues" ? this.ampBlues : amp === "clean" ? this.ampClean : this.leadClean);
    for (const g of articulate(notes, beat)) {
      const first = g.start, last = g.notes[g.notes.length - 1];
      const t = startTime + first.time;
      const end = last.time + last.dur; // group end, relative to the phrase
      const accent = first.slot % 3 === 0 ? 1 : 0.88;
      const vel = clamp(accent * (0.9 + Math.random() * 0.08), 0, 1);
      const held = last.dur >= 0.6 * beat;
      const tail = last.cut ? 0 : Math.max(0, 1.2 * beat - last.dur); // a phrase's last note rings on
      const base = clamp(first.midi, 28, 100);
      const v = this.samples.guitar.play(base, t, dest, {
        dur: end - first.time + tail + (last.cut ? 0.015 : 0), vel, gain: 1.2 * gain, release: last.cut ? 0.05 : 0.35,
        // Vibrato on the held note at the end of the group; wider after a bend, like a singer.
        vibrato: held ? { cents: g.bend ? 26 : 18, rate: 5.4, delay: last.time - first.time + Math.min(0.28, 0.35 * last.dur) + (g.bend ? 0.12 : 0) } : undefined,
      });
      if (!v) continue;
      const det = v.src.detune;
      det.setValueAtTime(g.bend * 100, t);
      if (g.bend) {
        // Pick the note a whole step low, then push the string up to pitch.
        det.setValueAtTime(g.bend * 100, t + 0.03);
        det.setTargetAtTime(0, t + 0.03, 0.045);
      }
      let prevCents = 0;
      for (const m of g.moves) {
        const tm = startTime + m.time, cents = (clamp(m.midi, 28, 100) - base) * 100;
        if (m.kind === "slide") {
          det.setValueAtTime(prevCents, tm - m.glide); // hold, then glide into the note
          det.linearRampToValueAtTime(cents, tm);
        } else {
          det.setValueAtTime(cents, tm); // hammer-on / pull-off: the new pitch at once
        }
        prevCents = cents;
      }
      this._track([v.src, v.env], v.sources, v.env, v.end);
    }
  }

  playPhrase(phrase, startTime, bpm, { gain = 1 } = {}) {
    const ctx = this.ctx;
    const beat = 60 / bpm;
    this.leadDelay.delayTime.setValueAtTime(clamp((2 / 3) * beat, 0.05, 1.9), startTime);
    const notes = phraseNotes(phrase, bpm);
    if (this.samples) {
      this._playArticulated(notes, startTime, beat, gain);
      return;
    }
    for (const n of notes) {
      const t = startTime + n.time;
      const midi = clamp(n.midi, 28, 100);
      const accent = n.slot % 3 === 0 ? 1 : n.slot % 3 === 2 ? 0.86 : 0.8;
      const vel = clamp(accent * (0.93 + Math.random() * 0.07), 0, 1);
      if (this.samples) {
        const held = n.dur >= 0.6 * beat; // long notes get vibrato, like a player would
        const amp = this.samples.guitar.option.amp;
        const dest = amp === "blues" ? this.ampBlues : amp === "clean" ? this.ampClean : this.leadClean;
        const v = this.samples.guitar.play(midi, t, dest, {
          dur: n.cut ? n.dur + 0.015 : Math.max(n.dur, 1.2 * beat), vel, gain: 1.2 * gain, release: n.cut ? 0.04 : 0.3,
          vibrato: held ? { cents: 16, rate: 5.2, delay: Math.min(0.25, 0.3 * n.dur) } : undefined,
        });
        if (v) this._track([v.src, v.env], v.sources, v.env, v.end);
        continue;
      }
      const release = n.cut ? 0.012 : 0.06;
      const { data, rate } = renderPluck(ctx.sampleRate, mtof(midi), n.dur + 0.3, {
        vel, seed: (this._seed = (this._seed * 1103515245 + 12345) >>> 0),
      });
      const buf = ctx.createBuffer(1, data.length, ctx.sampleRate);
      buf.copyToChannel(data, 0);
      const src = ctx.createBufferSource();
      src.buffer = buf;
      src.playbackRate.value = rate;

      const env = ctx.createGain();
      env.gain.setValueAtTime(gain, t);
      env.gain.setTargetAtTime(0, t + n.dur, release);
      src.connect(env).connect(this.leadIn);
      const nodes = [src, env];
      const sources = [src];

      // Finger vibrato on longer notes: fades in after the attack.
      if (n.dur >= 0.45) {
        const lfo = ctx.createOscillator();
        lfo.frequency.value = 5.2 + Math.random() * 0.6;
        const depth = ctx.createGain();
        depth.gain.setValueAtTime(0, t);
        depth.gain.setValueAtTime(0, t + 0.18);
        depth.gain.linearRampToValueAtTime(22, t + Math.min(n.dur, 0.7)); // cents
        lfo.connect(depth).connect(src.detune);
        lfo.start(t);
        nodes.push(lfo, depth);
        sources.push(lfo);
      }
      src.start(t);
      this._track(nodes, sources, env, t + n.dur + release * 8);
    }
  }

  /** Stop everything: cancel timers, fade out and stop every note. */
  stop() {
    for (const id of this.timers) clearInterval(id);
    this.timers.clear();
    const now = this.ctx.currentTime;
    for (const v of [...this.voices]) {
      const g = v.env.gain;
      if (g.cancelAndHoldAtTime) g.cancelAndHoldAtTime(now);
      else { g.cancelScheduledValues(now); g.setValueAtTime(g.value, now); }
      g.linearRampToValueAtTime(0, now + 0.03);
      for (const s of v.sources) {
        try { s.stop(now + 0.04); } catch { /* already stopped */ }
      }
      // Notes scheduled in the future may never fire `ended`; free them anyway.
      setTimeout(() => this._free(v), 200);
    }
  }

  // ---------------------------------------------------------- internals

  /** Connect `input` through gain and pan to the backing bus, plus a reverb send. */
  _bus(input, { gain, pan, send }) {
    const g = this.ctx.createGain();
    g.gain.value = gain;
    const p = this.ctx.createStereoPanner();
    p.pan.value = pan;
    input.connect(g).connect(p).connect(this.backing);
    if (send > 0) {
      const s = this.ctx.createGain();
      s.gain.value = send;
      p.connect(s).connect(this.backingSend);
    }
    return input;
  }

  /** Remember a voice for stop(), stop its sources at `end`, disconnect when done. */
  _track(nodes, sources, env, end) {
    const v = { nodes, sources, env };
    this.voices.add(v);
    for (const s of sources) s.stop(end);
    sources[0].onended = () => this._free(v);
  }

  _free(v) {
    if (!this.voices.delete(v)) return;
    for (const n of v.nodes) {
      try { n.disconnect(); } catch { /* ignore */ }
    }
  }

  _noiseSrc(t, len) {
    const src = this.ctx.createBufferSource();
    src.buffer = this.noise;
    const maxOff = Math.max(0, this.noise.duration - len - 0.05);
    src.start(t, Math.random() * maxOff);
    return src;
  }

  _filter(type, freq, q = 0.7) {
    const f = this.ctx.createBiquadFilter();
    f.type = type;
    f.frequency.value = freq;
    f.Q.value = q;
    return f;
  }

  /** Percussive envelope: fast attack, exponential decay to silence by t + decay. */
  _perc(t, peak, decay, attack = 0.002) {
    const g = this.ctx.createGain();
    g.gain.setValueAtTime(0, t);
    g.gain.linearRampToValueAtTime(peak, t + attack);
    g.gain.exponentialRampToValueAtTime(0.0001, t + decay);
    return g;
  }

  _play(e, t) {
    const S = this.samples;
    if (S) {
      const go = (inst, note, dest, o) => {
        const v = inst.play(note, t, dest, o);
        if (v) this._track([v.src, v.env], [v.src], v.env, v.end);
      };
      const D = S.drums;
      switch (e.instrument) {
        case "kick": return go(D, "kick", this.sKick, { vel: e.vel });
        case "snare": return go(D, "snare", this.sSnare, { vel: e.vel });
        case "hat": {
          const open = (e.dur ?? 0.05) > 0.1 && D.has("hatOpen");
          return go(D, open ? "hatOpen" : "hat", this.sHat, { vel: e.vel, dur: open ? e.dur : undefined, release: 0.08 });
        }
        case "sticks": if (D.has("sticks")) return go(D, "sticks", this.sSnare, { vel: e.vel }); break;
        case "crash": if (D.has("crash")) return go(D, "crash", this.sHat, { vel: e.vel * 0.8 }); break;
        case "bass": return go(S.bass, e.midi, this.sBass, { vel: e.vel, dur: e.dur, release: 0.06 });
        case "keys": if (S.keys.zones.length) go(S.keys, e.midi, this.sPiano, { vel: e.vel, dur: e.dur, release: 0.25 }); return;
        case "organ": return; // the synth pad muddies the real instruments
        default: break;
      }
    }
    switch (e.instrument) {
      case "kick": return this._kick(t, e.vel);
      case "snare": return this._snare(t, e.vel);
      case "hat": return this._hat(t, e.vel, e.dur ?? 0.05);
      case "sticks": return this._sticks(t, e.vel);
      case "crash": return this._crash(t, e.vel);
      case "bass": return this._bass(t, e.midi, e.dur, e.vel);
      case "keys": return this._keys(t, e.midi, e.dur, e.vel);
      case "organ": return this._organ(t, e.midi, e.dur, e.vel);
    }
  }

  _kick(t, vel) {
    const ctx = this.ctx;
    const osc = ctx.createOscillator();
    osc.frequency.setValueAtTime(115, t);
    osc.frequency.exponentialRampToValueAtTime(50, t + 0.12);
    const env = this._perc(t, 0.6 * vel, 0.42, 0.003);
    osc.connect(env).connect(this.drumBus);
    // beater click
    const click = this._noiseSrc(t, 0.02);
    const lp = this._filter("lowpass", 2500);
    const cEnv = this._perc(t, 0.12 * vel, 0.015, 0.001);
    click.connect(lp).connect(cEnv).connect(this.drumBus);
    osc.start(t);
    this._track([osc, env, click, lp, cEnv], [osc, click], env, t + 0.45);
  }

  _snare(t, vel) {
    const ctx = this.ctx;
    // noise = snare wires
    const n = this._noiseSrc(t, 0.25);
    const hp = this._filter("highpass", 1200);
    const bp = this._filter("peaking", 4000, 0.8);
    bp.gain.value = 3;
    const nEnv = this._perc(t, 0.32 * vel, 0.22, 0.001);
    n.connect(hp).connect(bp).connect(nEnv).connect(this.drumBus);
    // body = drum shell
    const body = ctx.createOscillator();
    body.type = "triangle";
    body.frequency.setValueAtTime(200, t);
    body.frequency.exponentialRampToValueAtTime(165, t + 0.06);
    const bEnv = this._perc(t, 0.22 * vel, 0.11, 0.001);
    body.connect(bEnv).connect(this.drumBus);
    body.start(t);
    this._track([n, hp, bp, nEnv, body, bEnv], [n, body], nEnv, t + 0.25);
  }

  _hat(t, vel, dur) {
    const n = this._noiseSrc(t, dur + 0.02);
    const hp = this._filter("highpass", 7000);
    const pk = this._filter("peaking", 10000, 1);
    pk.gain.value = 4;
    const env = this._perc(t, 0.11 * vel, dur, 0.001);
    n.connect(hp).connect(pk).connect(env).connect(this.hatBus);
    this._track([n, hp, pk, env], [n], env, t + dur + 0.02);
  }

  _sticks(t, vel) {
    // two sticks clacking: a narrow band of noise, very short
    const n = this._noiseSrc(t, 0.05);
    const bp = this._filter("bandpass", 2600, 3);
    const hp = this._filter("highpass", 900);
    const env = this._perc(t, 1.6 * vel, 0.04, 0.0008);
    n.connect(bp).connect(hp).connect(env).connect(this.drumBus);
    this._track([n, bp, hp, env], [n], env, t + 0.05);
  }

  _crash(t, vel) {
    const n = this._noiseSrc(t, 2.2);
    const hp = this._filter("highpass", 4500);
    const pk = this._filter("peaking", 7000, 0.8);
    pk.gain.value = 3;
    const env = this._perc(t, 0.09 * vel, 2.0, 0.003);
    n.connect(hp).connect(pk).connect(env).connect(this.hatBus);
    this._track([n, hp, pk, env], [n], env, t + 2.05);
  }

  _bass(t, midi, dur, vel) {
    const osc = this.ctx.createOscillator();
    osc.setPeriodicWave(this.bassWave);
    osc.frequency.value = mtof(midi);
    const env = this.ctx.createGain();
    const peak = 0.38 * vel;
    env.gain.setValueAtTime(0, t);
    env.gain.linearRampToValueAtTime(peak, t + 0.006);
    env.gain.setTargetAtTime(peak * 0.6, t + 0.006, 0.15); // pluck then sustain
    env.gain.setTargetAtTime(0, t + dur, 0.025);
    osc.connect(env).connect(this.bassIn);
    osc.start(t);
    this._track([osc, env], [osc], env, t + dur + 0.15);
  }

  _keys(t, midi, dur, vel) {
    // FM electric piano: sine carrier, sine modulator at the same frequency;
    // the modulation index (brightness) falls fast after the attack.
    const ctx = this.ctx;
    const f = mtof(midi);
    const car = ctx.createOscillator();
    car.frequency.value = f;
    const mod = ctx.createOscillator();
    mod.frequency.value = f;
    const idx = ctx.createGain();
    idx.gain.setValueAtTime(f * (0.4 + 1.3 * vel), t);
    idx.gain.setTargetAtTime(f * 0.2, t, 0.2);
    mod.connect(idx).connect(car.frequency);
    const env = ctx.createGain();
    const peak = 0.06 * vel;
    env.gain.setValueAtTime(0, t);
    env.gain.linearRampToValueAtTime(peak, t + 0.004);
    env.gain.setTargetAtTime(peak * 0.25, t + 0.004, 0.9);
    env.gain.setTargetAtTime(0, t + dur, 0.07);
    car.connect(env).connect(this.keysIn);
    car.start(t);
    mod.start(t);
    this._track([car, mod, idx, env], [car, mod], env, t + dur + 0.5);
  }

  _organ(t, midi, dur, vel) {
    const osc = this.ctx.createOscillator();
    osc.setPeriodicWave(this.organWave);
    osc.frequency.value = mtof(midi);
    osc.detune.value = (Math.random() - 0.5) * 6; // slight chorus between voices
    const env = this.ctx.createGain();
    const level = 0.022 * vel;
    env.gain.setValueAtTime(0, t);
    env.gain.linearRampToValueAtTime(level, t + 0.25); // slow swell
    env.gain.setValueAtTime(level, t + dur - 0.05);
    env.gain.setTargetAtTime(0, t + dur - 0.05, 0.12);
    osc.connect(env).connect(this.organIn);
    osc.start(t);
    this._track([osc, env], [osc], env, t + dur + 0.6);
  }
}
