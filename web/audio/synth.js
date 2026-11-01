// synth.js: render synthetic "plucked guitar" audio into a Float32Array.
//
// PURE (no browser APIs). Used by:
//   - simulate mode in the browser (the buffer is played through an
//     AudioBufferSourceNode into the analysis input instead of the mic), and
//   - the Node pipeline test (pipeline.test.mjs),
// so the browser simulation and the tests exercise the exact same signal.
//
// Model: additive synthesis (6 harmonics, higher harmonics decay faster),
// a 2 ms attack, exponential decay, and a short burst of "pick noise" at the
// attack. Notes are monophonic, as if played on one string: a new attack
// cuts the previous note (5 ms fade). A note with `legato: true` has no new
// attack or pick noise; the frequency just changes (phase-continuous) while
// the amplitude keeps decaying, like a hammer-on / pull-off.

import { midiToFreq } from "./pitch.js";

const HARM_AMPS = [1, 0.6, 0.4, 0.3, 0.2, 0.15];

/** Small deterministic PRNG so tests are reproducible. Returns -1..1. */
function makeNoise(seed) {
  let s = seed >>> 0 || 1;
  return () => {
    s ^= s << 13; s >>>= 0;
    s ^= s >>> 17;
    s ^= s << 5; s >>>= 0;
    return (s / 4294967296) * 2 - 1;
  };
}

/**
 * @param {number} sampleRate
 * @param {{time:number, midi:number|null, legato?:boolean, velocity?:number}[]} notes
 *   time in seconds from buffer start. midi null = unpitched knock (noise burst
 *   only, like a muted-string pluck used for latency calibration).
 * @param {number} duration seconds
 * @param {object} [opts]
 * @param {number} [opts.peak=0.3]        peak amplitude of a note (velocity 1)
 * @param {number} [opts.decay=2.5]       amplitude decay rate of the fundamental (1/s)
 * @param {number} [opts.noiseDb=-70]     constant background noise level (dBFS RMS)
 * @param {number} [opts.humDb=null]      quiet sustained "backing" chord (A2+E3+A3) level, or null
 * @param {number} [opts.seed=1]
 * @returns {Float32Array}
 */
export function renderNotes(sampleRate, notes, duration, opts = {}) {
  const { peak = 0.3, decay = 2.5, noiseDb = -70, humDb = null, seed = 1 } = opts;
  const n = Math.ceil(duration * sampleRate);
  const out = new Float32Array(n);
  const rnd = makeNoise(seed);
  const sorted = [...notes].sort((a, b) => a.time - b.time);

  // Each attack starts a "voice"; legato notes change the voice's pitch.
  let voice = null; // {start, end, phases[], freq, vel, pitched}
  let next = 0;
  const fadeLen = Math.round(0.005 * sampleRate);
  let fadeLeft = 0, fadeVoice = null;

  const voiceSample = (v, i) => {
    const t = (i - v.start) / sampleRate;
    const env = Math.min(1, t / 0.002); // 2 ms attack
    let s = 0;
    if (v.pitched) {
      for (let k = 0; k < HARM_AMPS.length; k++) {
        v.phases[k] += (2 * Math.PI * v.freq * (k + 1)) / sampleRate;
        s += HARM_AMPS[k] * Math.exp(-t * decay * (1 + 0.6 * k)) * Math.sin(v.phases[k]);
      }
      s *= 0.45; // normalize roughly to peak ~1
    }
    // pick noise: ~12 ms burst at the attack (louder for unpitched knocks)
    if (t < 0.012) s += (v.pitched ? 0.25 : 1) * (1 - t / 0.012) * rnd();
    return s * env * v.vel * peak;
  };

  for (let i = 0; i < n; i++) {
    const tNow = i / sampleRate;
    while (next < sorted.length && sorted[next].time <= tNow) {
      const nt = sorted[next++];
      if (nt.legato && voice && voice.pitched && nt.midi != null) {
        voice.freq = midiToFreq(nt.midi);
      } else {
        if (voice) { fadeVoice = voice; fadeLeft = fadeLen; }
        voice = {
          start: i,
          phases: HARM_AMPS.map(() => 0),
          freq: nt.midi != null ? midiToFreq(nt.midi) : 0,
          vel: nt.velocity ?? 1,
          pitched: nt.midi != null,
        };
      }
    }
    let s = 0;
    if (voice) s += voiceSample(voice, i);
    if (fadeLeft > 0) {
      s += voiceSample(fadeVoice, i) * (fadeLeft / fadeLen);
      fadeLeft--;
    }
    if (humDb !== null) {
      const a = Math.pow(10, humDb / 20) * Math.SQRT2 / 3;
      s += a * (Math.sin(2 * Math.PI * 110 * tNow) + Math.sin(2 * Math.PI * 164.81 * tNow) + Math.sin(2 * Math.PI * 220 * tNow));
    }
    s += Math.pow(10, noiseDb / 20) * Math.sqrt(3) * rnd(); // uniform noise, RMS = level
    out[i] = s;
  }
  return out;
}

/**
 * Parse a simulate pattern like "0:64 2:67 3:69 5:67~ 12:-" into notes.
 *   "slot:midi"   pluck midi at slot
 *   "slot:midi~"  legato (hammer-on/pull-off) to midi at slot
 *   "slot:-"      unpitched knock
 * Note names also work: "0:E4 2:G4".
 */
export function parsePattern(text) {
  const out = [];
  for (const tok of text.trim().split(/[\s,]+/).filter(Boolean)) {
    const m = tok.match(/^(\d+):([^~]+)(~?)$/);
    if (!m) throw new Error(`bad pattern token "${tok}" (use slot:midi, e.g. 0:64 or 2:G4~)`);
    const slot = Number(m[1]);
    const midi = m[2] === "-" ? null : parseNote(m[2]);
    out.push({ slot, midi, legato: m[3] === "~" });
  }
  return out;
}

const NAME_TO_PC = { C: 0, D: 2, E: 4, F: 5, G: 7, A: 9, B: 11 };
function parseNote(s) {
  if (/^\d+$/.test(s)) return Number(s);
  const m = s.match(/^([A-Ga-g])([#b]?)(-?\d)$/);
  if (!m) throw new Error(`bad note "${s}"`);
  const pc = NAME_TO_PC[m[1].toUpperCase()] + (m[2] === "#" ? 1 : m[2] === "b" ? -1 : 0);
  return pc + 12 * (Number(m[3]) + 1);
}
