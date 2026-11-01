// offline.js: read an answer's notes after the answer ends, from the recorded audio.
//
// The live detector (onsets.js) must decide each note's pitch ~0.2 s after the
// pluck, from the audio heard so far. After the answer we have all of it, so:
//   1. find where each note starts (same onset detector: its timing is good);
//   2. read each note's pitch over its steady part - from just after the pick
//      attack up to where the next note starts - and take the pitch most of
//      those readings agree on;
//   3. drop "notes" that are not new: a pitch-change onset whose pitch equals
//      the note before it.
// The result has the same shape as the live onset events, so quantize() can
// snap it to the grid as before.

import { OnsetDetector, DEFAULT_ONSET_PARAMS, pitchWindowSize, highpass } from "./onsets.js";

const SKIP_S = 0.06; // ignore the first 60 ms of a note (the pick attack and body boom)
const MAX_NOTE_S = 1.2; // read at most this much of a long note
const HOP = 256;
const DOUBLE_S = 0.15; // two onsets this close: one pluck
const LOW_HZ = 125;
const LOW_WEIGHT = 0.35;

const toFloat = (f) => 69 + 12 * Math.log2(f / 440);

/**
 * Pitch of one note from many readings: the rounded MIDI note most readings
 * agree on (weighted by clarity), refined to the median of those readings.
 * Returns {midi, freq, clarity, votes} or null.
 */
export function votePitch(readings, tuning = 0) {
  const ok = readings.filter((r) => r.freq > 0);
  if (ok.length < 2) return null;
  const score = new Map();
  for (const r of ok) {
    const m = Math.round(toFloat(r.freq) - tuning);
    // Readings near the guitar body's boom (below ~125 Hz) ring on under higher
    // notes; they count a third as much. A real low note still wins when it
    // is what was played, since then nothing else competes with it.
    const w = r.freq < LOW_HZ ? LOW_WEIGHT : 1;
    score.set(m, (score.get(m) ?? 0) + w * r.clarity);
  }
  let best = null;
  for (const [m, s] of score) if (best === null || s > score.get(best)) best = m;
  const agree = ok.filter((r) => Math.round(toFloat(r.freq) - tuning) === best);
  if (agree.length < 2) return null;
  const freqs = agree.map((r) => r.freq).sort((a, b) => a - b);
  return {
    midi: best,
    freq: freqs[Math.floor(freqs.length / 2)],
    clarity: Math.max(...agree.map((r) => r.clarity)),
    votes: agree.length,
  };
}

/**
 * Analyze one recorded stretch of audio.
 * @param {object} o
 * @param {Float32Array} o.samples     mono audio
 * @param {number} o.sampleRate
 * @param {number} o.startFrame        AudioContext frame of samples[0]
 * @param {(frame: Float32Array) => {freq:number, clarity:number, midi:(number|null)}} o.estimatePitch
 * @param {object} [o.params]          onset params (DEFAULT_ONSET_PARAMS)
 * @param {number} [o.tuning]          player's tuning offset in semitones (learned live)
 * @returns {Array} onset events {time, frame, midi, freq, clarity, kind, level, votes}
 */
export function analyzeRecording({ samples, sampleRate, startFrame, estimatePitch, voteEstimatePitch, params, tuning = 0 }) {
  // Voting over many readings tolerates less clear ones, so the pitch reading
  // may use a lower clarity cutoff than the live detector.
  const readPitch = voteEstimatePitch ?? estimatePitch;
  const p = { ...DEFAULT_ONSET_PARAMS, ...params, legato: true };
  const W = pitchWindowSize(sampleRate);

  // 1. Note starts (and their loudness), from the live detector run over the recording.
  const det = new OnsetDetector({ sampleRate, estimatePitch, windowSize: W, params: p });
  const onsets = [];
  for (let i = 0; i < samples.length; i += 512) {
    onsets.push(...det.push(samples.subarray(i, Math.min(samples.length, i + 512)), startFrame + i));
  }
  onsets.push(...det.flush());
  onsets.sort((a, b) => a.frame - b.frame);

  // 2. Pitch of each note over its steady part (rumble filtered out, as live).
  const filtered = p.highpassHz ? highpass(samples, sampleRate, p.highpassHz) : samples;
  const frame = new Float32Array(W);
  const out = [];
  for (let k = 0; k < onsets.length; k++) {
    const o = onsets[k];
    const s0 = o.frame - startFrame;
    const next = k + 1 < onsets.length ? onsets[k + 1].frame - startFrame : samples.length;
    const end = Math.min(next, s0 + Math.round(MAX_NOTE_S * sampleRate), samples.length);
    let from = s0 + Math.round(SKIP_S * sampleRate);
    // A short note: use the last full window before the next note, but not before the attack.
    if (end - from < W) from = Math.max(s0 + Math.round(0.02 * sampleRate), end - W);
    const readings = [];
    for (let i = from; i + W <= end; i += HOP) {
      frame.set(filtered.subarray(i, i + W));
      const e = readPitch(frame);
      if (e.midi !== null) readings.push({ freq: e.freq, clarity: e.clarity });
    }
    const v = votePitch(readings, tuning);
    let midi = v ? v.midi : null;
    if (midi !== null && det._preferScale) midi = det._preferScale(midi, toFloat(v.freq) - tuning);
    out.push({
      time: o.time, frame: o.frame, kind: o.kind, level: o.level,
      midi, freq: v ? v.freq : 0, clarity: v ? v.clarity : 0, votes: v ? v.votes : 0,
    });
  }

  // 3. Clean up: one pluck often gives two onsets a few dozen ms apart (the pick
  //    click, then the string). The first is too short to have a pitch: give it
  //    the second's pitch (its timing is the more accurate) and drop the second.
  //    And a pitch-change onset that did not change the pitch is not a new note.
  const notes = [];
  for (let k = 0; k < out.length; k++) {
    const e = out[k], nx = out[k + 1];
    if (e.midi === null && nx && nx.midi !== null && nx.time - e.time <= DOUBLE_S) {
      notes.push({ ...nx, time: e.time, frame: e.frame, kind: e.kind, level: Math.max(e.level ?? 0, nx.level ?? 0) });
      k++;
      continue;
    }
    const prev = notes[notes.length - 1];
    if (e.kind === "legato" && prev && (e.midi === null || e.midi === prev.midi)) continue;
    notes.push(e);
  }
  return notes;
}
