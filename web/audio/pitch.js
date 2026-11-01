// pitch.js: monophonic pitch detection for single guitar notes.
//
// Primary detector: `pitchy` (McLeod Pitch Method), loaded from a pinned CDN
// URL. If the CDN is unreachable (bad hackathon wifi), we fall back to a small
// built-in time-domain McLeod/NSDF implementation with the same interface
// ({ findPitch(frame, sampleRate) -> [freqHz, clarity] }). The fallback is
// slower but fine for one mono input, and it also lets Node tests run offline.
//
// Everything in this module except loadPitchDetector() is pure and works in Node.

import { MIDI_MIN, MIDI_MAX } from "./quantize.js";

// Pinned exact version (verified to exist on jsDelivr). Never a floating tag.
export const PITCHY_URL = "https://cdn.jsdelivr.net/npm/pitchy@4.1.0/+esm";

const NOTE_NAMES = ["C", "C#", "D", "Eb", "E", "F", "F#", "G", "G#", "A", "Bb", "B"];

/** Nearest MIDI note for a frequency (A4 = 440 Hz = 69). */
export function freqToMidi(freq) {
  return Math.round(69 + 12 * Math.log2(freq / 440));
}

/** Fractional MIDI value (useful for "cents off" displays). */
export function freqToMidiFloat(freq) {
  return 69 + 12 * Math.log2(freq / 440);
}

export function midiToFreq(midi) {
  return 440 * Math.pow(2, (midi - 69) / 12);
}

/** 57 -> "A3". Uses flats for Eb/Bb (blues-friendly), sharps otherwise. */
export function midiToName(midi) {
  if (!Number.isInteger(midi)) return "-";
  return NOTE_NAMES[((midi % 12) + 12) % 12] + (Math.floor(midi / 12) - 1);
}

/** Root-mean-square level of a frame (linear, 0..1 for full-scale audio). */
export function rms(frame) {
  let s = 0;
  for (let i = 0; i < frame.length; i++) s += frame[i] * frame[i];
  return Math.sqrt(s / frame.length);
}

export const dbToLin = (db) => Math.pow(10, db / 20);
export const linToDb = (x) => (x > 0 ? 20 * Math.log10(x) : -Infinity);

/**
 * Fallback McLeod pitch detector (normalized square difference function).
 * Same call shape as pitchy's PitchDetector.findPitch.
 * Only lags for 70 Hz .. 1400 Hz are searched (guitar E2 = 82 Hz, E6 = 1319 Hz).
 */
export function createNsdfDetector(inputLength) {
  const nsdf = new Float32Array(inputLength);
  return {
    inputLength,
    findPitch(x, sampleRate) {
      const n = x.length;
      const maxLag = Math.min(n - 1, Math.ceil(sampleRate / 70));
      const minLag = Math.max(2, Math.floor(sampleRate / 1400));
      // m(tau) = sum_{i<n-tau} x[i]^2 + x[i+tau]^2, updated incrementally.
      let m = 0;
      for (let i = 0; i < n; i++) m += 2 * x[i] * x[i];
      if (m === 0) return [0, 0];
      nsdf[0] = 1;
      for (let tau = 1; tau <= maxLag; tau++) {
        m -= x[tau - 1] * x[tau - 1] + x[n - tau] * x[n - tau];
        let acf = 0;
        for (let i = 0; i < n - tau; i++) acf += x[i] * x[i + tau];
        nsdf[tau] = m > 0 ? (2 * acf) / m : 0;
      }
      // Key maxima: the highest point between each positive-going and
      // negative-going zero crossing, skipping the lobe around lag 0.
      const peaks = [];
      let tau = 1;
      while (tau <= maxLag && nsdf[tau] > 0) tau++; // leave the lag-0 lobe
      while (tau <= maxLag) {
        while (tau <= maxLag && nsdf[tau] <= 0) tau++;
        let best = -1;
        while (tau <= maxLag && nsdf[tau] > 0) {
          if (tau >= minLag && (best < 0 || nsdf[tau] > nsdf[best])) best = tau;
          tau++;
        }
        if (best > 0 && best < maxLag) peaks.push(best);
      }
      if (peaks.length === 0) return [0, 0];
      let top = 0;
      for (const p of peaks) top = Math.max(top, nsdf[p]);
      const k = 0.9; // McLeod's constant: first peak within 90% of the highest
      const chosen = peaks.find((p) => nsdf[p] >= k * top);
      // Parabolic interpolation around the chosen peak for sub-sample lag.
      const a = nsdf[chosen - 1], b = nsdf[chosen], c = nsdf[chosen + 1];
      const denom = a - 2 * b + c;
      const shift = denom !== 0 ? (0.5 * (a - c)) / denom : 0;
      const lag = chosen + shift;
      const clarity = denom !== 0 ? b - 0.25 * (a - c) * shift : b;
      return [sampleRate / lag, Math.min(1, clarity)];
    },
  };
}

/**
 * Load pitchy from the CDN; fall back to the built-in detector on failure.
 * Browser-only (dynamic import of an https URL).
 * @returns {Promise<{detector: {findPitch: Function}, source: "pitchy"|"fallback", error?: string}>}
 */
export async function loadPitchDetector(inputLength) {
  try {
    const { PitchDetector } = await import(PITCHY_URL);
    const detector = PitchDetector.forFloat32Array(inputLength);
    return { detector, source: "pitchy" };
  } catch (err) {
    return { detector: createNsdfDetector(inputLength), source: "fallback", error: String(err) };
  }
}

/**
 * Wrap a raw detector with the musical rules we need:
 * clarity >= threshold, RMS >= minimum, frequency mapped to MIDI 40..88.
 * Returns a function frame -> {freq, clarity, rms, midi|null}.
 */
/** Strength of frequency `f` in the frame (Hann-windowed single-bin DFT). */
function magAt(x, sampleRate, f) {
  const n = x.length, w = (2 * Math.PI * f) / sampleRate;
  let re = 0, im = 0;
  for (let i = 0; i < n; i++) {
    const h = 0.5 - 0.5 * Math.cos((2 * Math.PI * i) / (n - 1));
    re += h * x[i] * Math.cos(w * i);
    im -= h * x[i] * Math.sin(w * i);
  }
  return Math.hypot(re, im);
}

/**
 * Fix "too low" pitch errors. A small mic (like a laptop's) in a noisy room
 * can make the detector lock onto a pattern that repeats every 1.5, 2 or 3
 * cycles: a C4 reads as F2. Check the spectrum: if the found note's own
 * frequency is nearly missing but 1.5x, 2x or 3x that frequency is strong,
 * the real note is that higher one. Returns the corrected frequency.
 */
export function fixSubharmonic(x, sampleRate, freq) {
  if (!(freq > 0)) return freq;
  const mag = (f) => (f < sampleRate / 2 ? magAt(x, sampleRate, f) : 0);
  const peak = Math.max(mag(freq), mag(2 * freq), mag(3 * freq), mag(4 * freq));
  if (peak === 0 || mag(freq) >= 0.3 * peak) return freq;
  for (const mult of [1.5, 2, 3]) {
    const f = freq * mult;
    if (f <= 1400 && mag(f) >= 0.5 * peak) return f;
  }
  return freq;
}

export function makePitchEstimator(detector, sampleRate, params) {
  // params is read on every call so the UI can change thresholds live.
  return function estimate(frame) {
    const level = rms(frame);
    if (level < params.minRms) return { freq: 0, clarity: 0, rms: level, midi: null };
    const [rawFreq, clarity] = detector.findPitch(frame, sampleRate);
    const freq = params.fixSubharmonics === false ? rawFreq : fixSubharmonic(frame, sampleRate, rawFreq);
    let midi = null;
    if (clarity >= params.clarityThreshold && freq > 0) {
      const m = freqToMidi(freq);
      if (m >= MIDI_MIN && m <= MIDI_MAX) midi = m;
    }
    return { freq, clarity, rms: level, midi };
  };
}
