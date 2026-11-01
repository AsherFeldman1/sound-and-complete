// onsets.js: note-onset detection for a monophonic acoustic guitar.
//
// PURE streaming core (no browser APIs), so it runs in Node tests too.
// Feed it audio with push(samples, startFrame) where startFrame is the
// absolute sample index of samples[0] on the AudioContext clock. In the
// browser the AudioWorklet (capture-worklet.js) supplies that index from its
// `currentFrame` global, so onset times are sample-accurate relative to the
// metronome clicks (both live on the same AudioContext clock). That is the
// reason we use a worklet rather than AnalyserNode + requestAnimationFrame:
// rAF polling only tells you "something happened in the last ~16 ms of
// display time", with extra jitter from the main thread.
//
// How it works, once per hop (default 256 samples ~ 5.3 ms at 48 kHz):
//
//  (a) ATTACK onset: the RMS of the newest hop is above the gate AND at least
//      `energyRatio` times the mean RMS of the hops ~16-43 ms earlier, and we
//      are past the refractory period (~90 ms) since the last onset. A pluck
//      on an acoustic guitar is a very sharp energy rise, so this simple
//      energy-ratio test (a cheap cousin of spectral flux) is robust.
//      The onset time is refined inside the last two hops to the first sample
//      whose amplitude crosses a threshold, so precision is ~1 ms, not 5 ms.
//
//  (b) Pitch for an attack onset: the first ~20-40 ms after a pluck is noisy
//      (pick noise, string settling, pitch slightly sharp), so we only use
//      analysis windows that START at least `attackSkipMs` after the onset,
//      then take the median of the next `pitchVotes` valid estimates.
//      If no clear pitch is found (muted string, knock, click bleed) the onset
//      is still reported, with midi = null.
//
//  (c) LEGATO onset (hammer-on / pull-off / slide arrival): while a note is
//      ringing, if the detected pitch changes by >= 1 semitone and stays at
//      the new value for `legatoStableMs`, report a new onset. Exact octave
//      jumps (+/-12) are ignored because they are almost always detector
//      octave errors on a decaying string, not real playing.
//      Its time is estimated as (end of the first window showing the new
//      pitch) - windowSize/2, i.e. less precise (~+/-20 ms) than attacks.

import { dbToLin, linToDb } from "./pitch.js";

export const DEFAULT_ONSET_PARAMS = {
  gateDb: -45, // hop RMS (dBFS) needed to count as a note at all
  highpassHz: 120, // filter out the guitar body's boom and room rumble below this (0 = off)
  noiseMarginDb: 12, // ...and at least this far above the room's background level
  energyRatio: 1.6, // RMS jump needed for an attack (1.6 = +4 dB); raise if you get false onsets
  refractoryMs: 90, // no new onset within this time of the previous one
  attackSkipMs: 90, // ignore this much of the attack for pitch (the body boom at the pick)
  pitchVotes: 3, // median over this many valid pitch estimates
  maxPitchWaitMs: 200, // ...or give up waiting for votes after this long
  legato: true, // detect pitch-change onsets (hammer-ons etc.)
  scalePcs: null, // e.g. A minor blues [9, 0, 2, 3, 4, 7]: tie-break toward these notes
  scaleSnap: 0.75, // ...when the pitch is within this many semitones of one
  legatoStableMs: 35, // new pitch must hold this long
  noteOffMs: 120, // below gate this long -> the current note has ended
};

/** Window size for pitch analysis: ~43 ms (2048 samples at 44.1/48 kHz). */
export function pitchWindowSize(sampleRate) {
  let n = 512;
  while (n < sampleRate * 0.04) n *= 2;
  return n;
}

/** Coefficients of a 2nd-order high-pass (Butterworth Q) at fc Hz. */
function hpCoefs(fc, sampleRate) {
  const w = (2 * Math.PI * fc) / sampleRate, cs = Math.cos(w), al = Math.sin(w) / (2 * Math.SQRT1_2);
  const a0 = 1 + al;
  return { b0: (1 + cs) / 2 / a0, b1: -(1 + cs) / a0, b2: (1 + cs) / 2 / a0, a1: (-2 * cs) / a0, a2: (1 - al) / a0 };
}

/** Run x through two high-pass biquads in a row (4th order). `st` carries filter state between calls. */
function hpRun(x, c, st) {
  const y = new Float32Array(x.length);
  for (let i = 0; i < x.length; i++) {
    let v = x[i];
    for (const s of st) {
      const out = c.b0 * v + c.b1 * s[0] + c.b2 * s[1] - c.a1 * s[2] - c.a2 * s[3];
      s[1] = s[0]; s[0] = v; s[3] = s[2]; s[2] = out; v = out;
    }
    y[i] = v;
  }
  return y;
}

/** Remove everything below fc Hz from a whole recording (4th-order high-pass). */
export function highpass(x, sampleRate, fc) {
  return hpRun(x, hpCoefs(fc, sampleRate), [[0, 0, 0, 0], [0, 0, 0, 0]]);
}

function median(nums) {
  const s = [...nums].sort((a, b) => a - b);
  return s[Math.floor(s.length / 2)];
}

export class OnsetDetector {
  /**
   * @param {object} o
   * @param {number} o.sampleRate
   * @param {(frame: Float32Array) => {freq:number, clarity:number, rms:number, midi:(number|null)}} o.estimatePitch
   * @param {number} [o.windowSize]  pitch window length (must match the pitch detector)
   * @param {number} [o.hopSize=256]
   * @param {object} [o.params]      mutable params object (UI may edit it live)
   */
  constructor({ sampleRate, estimatePitch, windowSize, hopSize = 256, params }) {
    this.sampleRate = sampleRate;
    this.estimatePitch = estimatePitch;
    this.W = windowSize ?? pitchWindowSize(sampleRate);
    this.hop = hopSize;
    this.params = params ?? { ...DEFAULT_ONSET_PARAMS };
    this.ring = new Float32Array(this.W);
    this.ringF = new Float32Array(this.W); // high-passed copy, for pitch
    this.win = new Float32Array(this.W); // linearized copy of the ring
    this.reset();
  }

  reset() {
    this.ring.fill(0);
    this.ringF.fill(0);
    this.hp = null;
    this.w = 0; // ring write index
    this.nextFrame = null; // expected absolute frame of the next sample
    this.filled = 0; // samples written since reset (until >= W)
    this.hopFill = 0;
    this.hopSumSq = 0;
    this.hopCount = 0;
    this.hist = []; // RMS of recent hops
    this.lastOnsetFrame = -Infinity;
    this.pending = null; // attack onset waiting for its pitch
    this.currentMidi = null; // pitch of the note now ringing (for legato)
    this.currentFloat = null; // same, unrounded (tuning-corrected semitones)
    // How far the player's tuning is from A440, in semitones (-0.45..0.45).
    // Learned from steady notes, so a guitar tuned a bit flat still reads right.
    this.tuning = this.tuning ?? 0;
    this.legatoCand = null;
    this.quietHops = 0;
    this.floor = undefined; // background level (learned)
    this.gaps = 0; // number of discontinuities seen in input frames
    /** Latest analysis values, for meters / displays. */
    this.state = { rms: 0, rmsDb: -Infinity, midi: null, freq: 0, clarity: 0, tuningCents: 0 };
  }

  /**
   * Feed samples. Returns an array of onset events emitted during this call:
   * {time, frame, midi|null, freq, clarity, kind: "attack"|"legato", votes}
   * Events come out ~90 ms after the onset (pitch needs a little audio).
   */
  push(samples, startFrame) {
    const events = [];
    const filtered = this._highpass(samples); // for pitch only; timing uses the raw audio
    if (this.nextFrame !== null && startFrame !== this.nextFrame) {
      // Dropped or overlapping audio: keep going, but count it for debugging.
      this.gaps++;
    }
    let frame = startFrame;
    for (let i = 0; i < samples.length; i++) {
      const x = samples[i];
      this.ring[this.w] = x;
      this.ringF[this.w] = filtered[i];
      this.w = (this.w + 1) % this.W;
      if (this.filled < this.W) this.filled++;
      this.hopSumSq += x * x;
      this.hopFill++;
      frame++;
      if (this.hopFill === this.hop) this._processHop(frame, events);
    }
    this.nextFrame = frame;
    return events;
  }

  /** Flush a pending onset (e.g. at the end of a recording). */
  flush() {
    const events = [];
    if (this.pending) events.push(this._finalize());
    return events;
  }

  // ---- internals -------------------------------------------------------

  /**
   * Remove low rumble before analysis: params.highpassHz (4th order).
   * An acoustic guitar's body booms near 100 Hz with every pluck, and a
   * clip-on mic near the soundhole hears that boom louder than the notes.
   * Low notes (E2 = 82 Hz) still read correctly: their overtones repeat at the
   * note's own rate even without the lowest frequency.
   */
  _highpass(x) {
    const fc = this.params.highpassHz;
    if (!fc) return x; // ringF then holds the raw audio
    if (!this.hp || this.hp.fc !== fc) this.hp = { fc, c: hpCoefs(fc, this.sampleRate), st: [[0, 0, 0, 0], [0, 0, 0, 0]] };
    return hpRun(x, this.hp.c, this.hp.st);
  }

  _ms(ms) {
    return (ms / 1000) * this.sampleRate;
  }

  /** Sample k positions back from the newest (k = 1 is the newest). */
  _back(k) {
    return this.ring[(this.w - k + this.W) % this.W];
  }

  _window() {
    const W = this.W;
    const first = this.ringF.subarray(this.w);
    this.win.set(first, 0);
    this.win.set(this.ringF.subarray(0, this.w), first.length);
    return this.win;
  }

  _processHop(E, events) {
    // E = absolute frame just after the newest sample.
    const p = this.params;
    const hopRms = Math.sqrt(this.hopSumSq / this.hop);
    this.hopSumSq = 0;
    this.hopFill = 0;
    this.hopCount++;

    // Background level of the room: drops quickly to quiet moments, rises slowly
    // (about 1 dB per second), so notes don't count as background but a noisy
    // room does. A note must be noiseMarginDb above it.
    const hopSec = this.hop / this.sampleRate;
    if (this.floor === undefined) this.floor = hopRms;
    if (hopRms < this.floor) this.floor += (hopRms - this.floor) * Math.min(1, hopSec / 0.15);
    else this.floor *= Math.pow(10, (1.0 * hopSec) / 20);
    this.state.floorDb = linToDb(this.floor);
    const gate = Math.max(dbToLin(p.gateDb), this.floor * dbToLin(p.noiseMarginDb ?? 12));
    const h = this.hist;
    // Reference level: mean of hops 3..8 back. The two most recent previous
    // hops are skipped because an attack can take 1-2 hops to reach full level
    // (otherwise a re-pluck over a ringing note looks like a small jump).
    let ref = 0, nRef = 0;
    for (let k = Math.max(0, h.length - 8); k <= h.length - 3; k++) { ref += h[k]; nRef++; }
    ref = nRef ? ref / nRef : 0;
    h.push(hopRms);
    if (h.length > 16) h.shift();

    this.state.rms = hopRms;
    if (this.pending) this.pending.level = Math.max(this.pending.level, hopRms);
    this.state.rmsDb = linToDb(hopRms);

    const pastRefractory = E - this.lastOnsetFrame > this._ms(p.refractoryMs);

    // (a) attack onset
    if (pastRefractory && hopRms >= gate && hopRms >= p.energyRatio * Math.max(ref, 1e-7)) {
      if (this.pending) events.push(this._finalize());
      const onsetFrame = this._refineOnset(E, ref);
      this.pending = { frame: onsetFrame, votes: [], freqs: [], clar: [], firstEligible: null, level: 0 };
      this.lastOnsetFrame = onsetFrame;
      this.legatoCand = null;
    }

    if (this.filled < this.W) return; // not enough audio for pitch yet

    // (b) pitch: every hop while a pending onset collects votes, otherwise
    // every 2nd hop while there is signal (display + legato tracking).
    const windowStart = E - this.W;
    const pend = this.pending;
    const eligible = pend && windowStart >= pend.frame + this._ms(p.attackSkipMs);
    let est = null;
    if (eligible || (this.hopCount % 2 === 0 && hopRms >= gate * 0.5)) {
      est = this.estimatePitch(this._window());
      est = this._tuned(est);
      this.state.midi = est.midi;
      this.state.freq = est.freq;
      this.state.clarity = est.clarity;
    }
    if (hopRms < gate * 0.5) this.state.midi = null;

    if (eligible) {
      if (pend.firstEligible === null) pend.firstEligible = E;
      if (est.midi !== null) {
        pend.votes.push(est.midi);
        pend.freqs.push(est.freq);
        pend.clar.push(est.clarity);
      }
      if (pend.votes.length >= p.pitchVotes || E - pend.firstEligible >= this._ms(p.maxPitchWaitMs)) {
        events.push(this._finalize());
      }
    } else if (!pend && p.legato && est && this.currentMidi !== null && pastRefractory) {
      // (c) legato onset
      const m = est.midi;
      const moved = est.midiFloat != null && this.currentFloat != null &&
        Math.abs(est.midiFloat - this.currentFloat) >= (p.legatoMinSemitones ?? 0.7);
      if (m !== null && hopRms >= gate && moved && m !== this.currentMidi && Math.abs(m - this.currentMidi) !== 12) {
        if (!this.legatoCand || this.legatoCand.midi !== m) {
          this.legatoCand = { midi: m, firstE: E, freqs: [], clar: [] };
        }
        this.legatoCand.freqs.push(est.freq);
        this.legatoCand.clar.push(est.clarity);
        if (E - this.legatoCand.firstE >= this._ms(p.legatoStableMs)) {
          const c = this.legatoCand;
          const frame = Math.max(c.firstE - this.W / 2, this.lastOnsetFrame + this._ms(p.refractoryMs));
          events.push({
            time: frame / this.sampleRate,
            frame,
            midi: m,
            freq: median(c.freqs),
            clarity: Math.max(...c.clar),
            kind: "legato",
            level: Math.max(hopRms, this.currentLevel ?? 0), // continues a picked note: count it as loud as that
            votes: c.freqs.length,
          });
          this.currentMidi = m;
          this.currentFloat = est.midiFloat;
          this.lastOnsetFrame = frame;
          this.legatoCand = null;
        }
      } else if (m === this.currentMidi || m === null) {
        this.legatoCand = null;
        // A steady, clear note: learn the player's tuning from it.
        if (m !== null && est.clarity >= 0.95 && est.midiFloat != null) this._learnTuning(est.rawFloat);
      }
    }

    // note-off tracking (so a note re-appearing after silence is not "legato")
    if (hopRms < gate * 0.5) {
      this.quietHops++;
      if (this.quietHops * this.hop >= this._ms(p.noteOffMs)) {
        this.currentMidi = null;
        this.currentFloat = null;
        this.legatoCand = null;
      }
    } else {
      this.quietHops = 0;
    }
  }

  _float(freq) {
    return 69 + 12 * Math.log2(freq / 440);
  }

  /** Re-round a pitch estimate using the learned tuning offset. */
  _tuned(est) {
    if (est.midi === null || !(est.freq > 0)) return { ...est, midiFloat: null, rawFloat: null };
    const raw = this._float(est.freq);
    const f = raw - this.tuning;
    const m = Math.round(f);
    return { ...est, midi: m >= 40 && m <= 88 ? m : null, midiFloat: f, rawFloat: raw };
  }

  /**
   * Tie-break between two neighbouring notes. If the note heard is outside
   * the song's scale (params.scalePcs) but the pitch is within
   * params.scaleSnap semitones of a neighbour that is in the scale, take the
   * neighbour: a slightly flat A reads as A, not G#.
   */
  _preferScale(midi, f) {
    const pcs = this.params.scalePcs;
    if (!pcs || !Number.isFinite(f) || Math.abs(f - midi) > 0.6) return midi;
    const inScale = (m) => pcs.includes(((m % 12) + 12) % 12);
    if (inScale(midi)) return midi;
    const other = f >= midi ? midi + 1 : midi - 1;
    return inScale(other) && Math.abs(f - other) <= (this.params.scaleSnap ?? 0.75) ? other : midi;
  }

  /** Slowly follow the player's tuning (circular average of the cents offset). */
  _learnTuning(raw) {
    let dev = raw - Math.round(raw) - this.tuning;
    dev -= Math.round(dev); // wrap to -0.5..0.5
    this.tuning = Math.max(-0.45, Math.min(0.45, this.tuning + 0.08 * dev));
    this.state.tuningCents = Math.round(this.tuning * 100);
  }

  /**
   * Find the attack start inside the last two hops: first sample whose
   * magnitude exceeds max(30% of the newest hop's peak, 1.5x the previous
   * level's expected peak). Worst case it is off by about one hop.
   */
  _refineOnset(E, ref) {
    let peak = 0;
    for (let k = 1; k <= this.hop; k++) peak = Math.max(peak, Math.abs(this._back(k)));
    const thr = Math.max(0.3 * peak, 1.5 * Math.SQRT2 * ref);
    const span = Math.min(2 * this.hop, this.filled);
    for (let k = span; k >= 1; k--) {
      if (Math.abs(this._back(k)) >= thr) return E - k;
    }
    return E - this.hop;
  }

  _finalize() {
    const pend = this.pending;
    this.pending = null;
    let midi = pend.votes.length >= 2 ? median(pend.votes) : null;
    if (midi !== null) midi = this._preferScale(midi, this._float(median(pend.freqs)) - this.tuning);
    this.currentLevel = pend.level;
    this.currentMidi = midi; // unpitched hit (muted string) ends the previous note
    this.currentFloat = midi === null ? null : this._float(median(pend.freqs)) - this.tuning;
    return {
      time: pend.frame / this.sampleRate,
      frame: pend.frame,
      midi,
      freq: pend.freqs.length ? median(pend.freqs) : 0,
      clarity: pend.clar.length ? Math.max(...pend.clar) : 0,
      kind: "attack",
      level: pend.level, // loudest hop RMS while the pitch was read
      votes: pend.votes.length,
    };
  }
}
