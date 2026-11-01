// End-to-end test of the detection pipeline without a browser or a guitar:
//   synth.js (synthetic plucks) -> OnsetDetector (+ fallback McLeod pitch) -> quantize
// The browser uses pitchy instead of the fallback detector; both implement
// the McLeod pitch method with the same [freq, clarity] interface.
// Run: node --test web/audio/*.test.mjs
import { test } from "node:test";
import assert from "node:assert/strict";
import { renderNotes, parsePattern } from "./synth.js";
import { OnsetDetector, DEFAULT_ONSET_PARAMS, pitchWindowSize } from "./onsets.js";
import { createNsdfDetector, makePitchEstimator, midiToName } from "./pitch.js";
import { quantize, slotDuration, PHRASE_SLOTS } from "./quantize.js";

const SR = 48000;
const BPM = 80;
const SLOT = slotDuration(BPM);

/** Run audio through the detector in 512-sample chunks like the worklet does. */
function detect(audio, { sampleRate = SR, frameOffset = 0, params = {} } = {}) {
  const W = pitchWindowSize(sampleRate);
  const estimatePitch = makePitchEstimator(createNsdfDetector(W), sampleRate, {
    clarityThreshold: 0.9,
    minRms: 0.003,
  });
  const det = new OnsetDetector({
    sampleRate,
    estimatePitch,
    windowSize: W,
    params: { ...DEFAULT_ONSET_PARAMS, ...params },
  });
  const events = [];
  for (let i = 0; i < audio.length; i += 512) {
    events.push(...det.push(audio.subarray(i, i + 512), frameOffset + i));
  }
  events.push(...det.flush());
  return events;
}

/** Build notes from a pattern string with optional per-note timing jitter (ms). */
function notesFrom(pattern, phraseStart, jitterMs = []) {
  return parsePattern(pattern).map((p, i) => ({
    time: phraseStart + p.slot * SLOT + (jitterMs[i] ?? 0) / 1000,
    midi: p.midi,
    legato: p.legato,
  }));
}

function expectedPhrase(pattern) {
  const ph = new Array(PHRASE_SLOTS).fill(null);
  for (const p of parsePattern(pattern)) ph[p.slot] = p.midi;
  return ph;
}

const fmt = (evs) => evs.map((e) => `${e.time.toFixed(3)}:${midiToName(e.midi)}(${e.kind})`).join(" ");

test("plucked blues lick in A minor -> exact phrase and timing offsets", () => {
  const start = 1.0;
  // Includes a repeated same note (slots 14, 15), a low A2, a high A5 and E2.
  const pattern = "0:64 2:67 3:69 5:67 6:64 9:62 12:60 14:57 15:57 18:45 20:40 21:69 23:81";
  const jitter = [0, 15, -20, 30, 0, -10, 5, 0, 5, -25, 10, 0, 12];
  const audio = renderNotes(SR, notesFrom(pattern, start, jitter), start + 6.5, { noiseDb: -65 });
  const events = detect(audio);
  const r = quantize(events, { phraseStart: start, bpm: BPM });
  assert.deepEqual(r.phrase, expectedPhrase(pattern), fmt(events));
  assert.equal(r.notes.length, 13, fmt(events));
  r.notes.forEach((n, i) => {
    assert.ok(Math.abs(n.offsetMs - jitter[i]) <= 3, `note ${i}: offset ${n.offsetMs} vs jitter ${jitter[i]}`);
  });
  assert.equal(r.rejected.length, 0, JSON.stringify(r.rejected));
});

test("hammer-on (legato pitch change, no new attack) is detected as an onset", () => {
  const start = 0.5;
  const pattern = "0:57 2:60~ 3:62 4:64~ 6:62~";
  const audio = renderNotes(SR, notesFrom(pattern, start), start + 2.5, { noiseDb: -65 });
  const events = detect(audio);
  const r = quantize(events, { phraseStart: start, bpm: BPM });
  assert.deepEqual(r.phrase, expectedPhrase(pattern), fmt(events));
  const legato = events.filter((e) => e.kind === "legato");
  assert.equal(legato.length, 3, fmt(events));
  for (const n of r.notes) assert.ok(Math.abs(n.offsetMs) <= 40, `legato timing ${n.offsetMs}`);
});

test("quiet backing hum + noise does not create notes; plucks still detected", () => {
  const start = 1.0;
  const pattern = "0:69 3:72 6:74 9:76 12:69";
  const silenceOnly = renderNotes(SR, [], 3, { noiseDb: -60, humDb: -50 });
  assert.equal(detect(silenceOnly).length, 0, "no onsets from hum/noise alone");
  const audio = renderNotes(SR, notesFrom(pattern, start), start + 4, { noiseDb: -60, humDb: -50 });
  const events = detect(audio);
  const r = quantize(events, { phraseStart: start, bpm: BPM });
  assert.deepEqual(r.phrase, expectedPhrase(pattern), fmt(events));
});

test("muted-string knocks give onsets with midi=null (calibration path)", () => {
  const knocks = [0.5, 1.25, 2.0, 2.75].map((t) => ({ time: t, midi: null }));
  const audio = renderNotes(SR, knocks, 3.2, { noiseDb: -65 });
  const events = detect(audio);
  assert.equal(events.length, 4, fmt(events));
  events.forEach((e, i) => {
    assert.ok(Math.abs(e.time - knocks[i].time) < 0.003, `knock ${i} at ${e.time}`);
  });
  // ...and quantize ignores them for the phrase.
  const r = quantize(events, { phraseStart: 0.5, bpm: BPM });
  assert.ok(r.phrase.every((x) => x === null));
});

test("absolute frame offset + latency: AudioContext clock times are respected", () => {
  // Pretend the context has been running for 100 s and the input path adds 110 ms.
  const ctxStart = 100;
  const latency = 0.11;
  const phraseStart = ctxStart + 1.0;
  const pattern = "0:57 4:60 8:62 12:64 16:67";
  // Audio buffer starts at ctxStart; notes are heard `latency` late.
  const notes = notesFrom(pattern, 1.0 + latency);
  const audio = renderNotes(SR, notes, 6.5, { noiseDb: -65 });
  const events = detect(audio, { frameOffset: ctxStart * SR });
  const r = quantize(events, { phraseStart, bpm: BPM, latency });
  assert.deepEqual(r.phrase, expectedPhrase(pattern), fmt(events));
  for (const n of r.notes) assert.ok(Math.abs(n.offsetMs) <= 3, `offset ${n.offsetMs}`);
});

test("works at 44.1 kHz too", () => {
  const sr = 44100;
  const start = 0.5;
  const pattern = "0:52 2:55 3:57 6:60 9:64";
  const audio = renderNotes(sr, notesFrom(pattern, start), start + 3, { noiseDb: -65 });
  const events = detect(audio, { sampleRate: sr });
  const r = quantize(events, { phraseStart: start, bpm: BPM });
  assert.deepEqual(r.phrase, expectedPhrase(pattern), fmt(events));
});
