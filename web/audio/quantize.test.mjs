// Run: node --test web/audio/
import { test } from "node:test";
import assert from "node:assert/strict";
import {
  quantize,
  slotDuration,
  phraseDuration,
  isValidPhrase,
  PHRASE_SLOTS,
} from "./quantize.js";

const BPM = 80;
const SLOT = slotDuration(BPM); // 0.25 s
const START = 10; // arbitrary phrase start on the AudioContext clock

const at = (slot, ms = 0) => START + slot * SLOT + ms / 1000;
const emptyPhrase = () => new Array(PHRASE_SLOTS).fill(null);

test("grid constants: 80 BPM -> 0.25 s per slot, 6 s per phrase", () => {
  assert.equal(SLOT, 0.25);
  assert.equal(phraseDuration(80), 6);
  assert.equal(PHRASE_SLOTS, 24);
});

test("no onsets -> all-null phrase", () => {
  const r = quantize([], { phraseStart: START, bpm: BPM });
  assert.deepEqual(r.phrase, emptyPhrase());
  assert.deepEqual(r.notes, []);
  assert.ok(isValidPhrase(r.phrase));
});

test("exact on-grid onsets land in their slots with 0 ms offset", () => {
  const onsets = [
    { time: at(0), midi: 69 },
    { time: at(2), midi: 72 },
    { time: at(3), midi: 74 },
    { time: at(12), midi: 76 },
    { time: at(23), midi: 57 },
  ];
  const r = quantize(onsets, { phraseStart: START, bpm: BPM });
  const want = emptyPhrase();
  want[0] = 69; want[2] = 72; want[3] = 74; want[12] = 76; want[23] = 57;
  assert.deepEqual(r.phrase, want);
  assert.equal(r.notes.length, 5);
  for (const n of r.notes) {
    assert.equal(n.offsetMs, 0);
    assert.equal(n.onGrid, true);
  }
  assert.deepEqual(r.notes.map((n) => n.slot), [0, 2, 3, 12, 23]);
  assert.equal(r.notes[0].time, at(0)); // raw time is reported
  assert.ok(isValidPhrase(r.phrase));
});

test("slightly early and late onsets snap to nearest slot with signed offset", () => {
  const onsets = [
    { time: at(4, -30), midi: 64 }, // 30 ms early
    { time: at(6, +45), midi: 67 }, // 45 ms late
    { time: at(9, -124), midi: 69 }, // just under half a slot early -> still slot 9
    { time: at(10, +124), midi: 71 }, // just under half a slot late -> still slot 10
  ];
  const r = quantize(onsets, { phraseStart: START, bpm: BPM, toleranceMs: 80, swing: false });
  assert.deepEqual(
    r.notes.map((n) => [n.slot, n.offsetMs, n.onGrid]),
    [
      [4, -30, true],
      [6, 45, true],
      [9, -124, false],
      [10, 124, false],
    ],
  );
  assert.equal(r.phrase[4], 64);
  assert.equal(r.phrase[9], 69); // off-grid still placed when not strict
});

test("exactly half a slot rounds up to the later slot", () => {
  const r = quantize([{ time: at(5, 125), midi: 60 }], { phraseStart: START, bpm: BPM, swing: false });
  assert.equal(r.notes[0].slot, 6);
  assert.equal(r.notes[0].offsetMs, -125);
});

test("swing grid: a straight or lightly swung 'and' lands on the swung slot", () => {
  const beat = 60 / BPM;
  const inBeat = (b, f) => START + (b + f) * beat; // f = position within beat b
  const onsets = [
    { time: inBeat(0, 0.02), midi: 57 }, // on the beat -> slot 0
    { time: inBeat(0, 0.5), midi: 60 }, // straight eighth "and" -> slot 2, not a coin flip
    { time: inBeat(1, 0.6), midi: 62 }, // light swing -> slot 5
    { time: inBeat(2, 0.33), midi: 64 }, // clearly the middle triplet -> slot 7
    { time: inBeat(2, 0.9), midi: 67 }, // just before beat 4 -> slot 9
  ];
  const r = quantize(onsets, { phraseStart: START, bpm: BPM });
  assert.deepEqual(r.notes.map((n) => n.slot), [0, 2, 5, 7, 9]);
});

test("quiet notes far below the loudest are dropped as too-quiet", () => {
  const onsets = [
    { time: at(0), midi: 69, level: 0.2 },
    { time: at(3), midi: 43, level: 0.01 }, // 26 dB quieter: a string ringing along
    { time: at(6), midi: 72, level: 0.1 },
  ];
  const r = quantize(onsets, { phraseStart: START, bpm: BPM });
  assert.deepEqual(r.notes.map((n) => n.midi), [69, 72]);
  assert.equal(r.rejected[0].reason, "too-quiet");
});

test("strict mode rejects off-grid onsets", () => {
  const onsets = [
    { time: at(1, 20), midi: 60 },
    { time: at(4, 100), midi: 62 },
  ];
  const r = quantize(onsets, { phraseStart: START, bpm: BPM, toleranceMs: 50, strict: true });
  assert.equal(r.phrase[1], 60);
  assert.equal(r.phrase[4], null);
  assert.equal(r.rejected.length, 1);
  assert.equal(r.rejected[0].reason, "off-grid");
});

test("collisions: first onset in a slot wins, even if input is unsorted", () => {
  const onsets = [
    { time: at(7, 40), midi: 65 }, // later, same slot
    { time: at(7, -40), midi: 64 }, // earlier -> wins
    { time: at(8), midi: 67 },
  ];
  const r = quantize(onsets, { phraseStart: START, bpm: BPM });
  assert.equal(r.phrase[7], 64);
  assert.equal(r.phrase[8], 67);
  assert.equal(r.notes.length, 2);
  assert.deepEqual(r.rejected.map((x) => [x.reason, x.midi, x.slot]), [["slot-taken", 65, 7]]);
});

test("quantize does not mutate its input", () => {
  const onsets = [{ time: at(3), midi: 60 }, { time: at(1), midi: 62 }];
  const copy = structuredClone(onsets);
  quantize(onsets, { phraseStart: START, bpm: BPM });
  assert.deepEqual(onsets, copy);
});

test("out-of-range times are dropped (before slot 0 and after slot 23)", () => {
  const onsets = [
    { time: at(-1), midi: 60 }, // count-in bar
    { time: at(0, -126), midi: 61 }, // more than half a slot early for slot 0
    { time: at(0, -100), midi: 62 }, // early beat 1 -> kept in slot 0
    { time: at(23, 120), midi: 63 }, // late slot 23 -> kept
    { time: at(24, -100), midi: 64 }, // rounds to slot 24 (next phrase) -> dropped
    { time: at(30), midi: 65 },
  ];
  const r = quantize(onsets, { phraseStart: START, bpm: BPM });
  assert.equal(r.phrase[0], 62);
  assert.equal(r.phrase[23], 63);
  assert.deepEqual(
    r.rejected.map((x) => [x.midi, x.reason]),
    [[60, "outside-phrase"], [61, "outside-phrase"], [64, "outside-phrase"], [65, "outside-phrase"]],
  );
});

test("invalid pitches are rejected (null, non-integer, outside 40..88)", () => {
  const onsets = [
    { time: at(0), midi: null },
    { time: at(1), midi: 39 },
    { time: at(2), midi: 89 },
    { time: at(3), midi: 60.5 },
    { time: at(4), midi: 40 },
    { time: at(5), midi: 88 },
  ];
  const r = quantize(onsets, { phraseStart: START, bpm: BPM });
  assert.equal(r.notes.length, 2);
  assert.equal(r.phrase[4], 40);
  assert.equal(r.phrase[5], 88);
  assert.equal(r.phrase[0], null); // an unpitched onset does not block its slot
  assert.ok(r.rejected.every((x) => x.reason === "no-valid-pitch"));
  assert.ok(isValidPhrase(r.phrase));
});

test("tempo changes the slot length", () => {
  // 120 BPM -> slot = 1/6 s. Slot 6 (beat 3) at 1.0 s.
  const r120 = quantize([{ time: START + 1.0, midi: 60 }], { phraseStart: START, bpm: 120 });
  assert.equal(r120.notes[0].slot, 6);
  assert.equal(r120.notes[0].offsetMs, 0);
  // The same time at 60 BPM (slot = 1/3 s) is slot 3.
  const r60 = quantize([{ time: START + 1.0, midi: 60 }], { phraseStart: START, bpm: 60 });
  assert.equal(r60.notes[0].slot, 3);
  // At 60 BPM a phrase is 8 s long; 7.8 s is slot 23 (7.667 s) + 133 ms.
  const r60b = quantize([{ time: START + 7.8, midi: 60 }], { phraseStart: START, bpm: 60 });
  assert.equal(r60b.notes[0].slot, 23);
  assert.equal(r60b.notes[0].offsetMs, 133.33);
});

test("latency is subtracted before snapping", () => {
  const latency = 0.12; // 120 ms of input latency
  const onsets = [
    { time: at(0) + latency, midi: 69 },
    { time: at(5) + latency + 0.02, midi: 72 }, // 20 ms late after correction
  ];
  const r = quantize(onsets, { phraseStart: START, bpm: BPM, latency });
  assert.equal(r.phrase[0], 69);
  assert.equal(r.phrase[5], 72);
  assert.deepEqual(r.notes.map((n) => n.offsetMs), [0, 20]);
  // Without latency correction the first looks 120 ms late, and the second
  // (140 ms late) even snaps to the wrong slot (6, 110 ms early).
  const raw = quantize(onsets, { phraseStart: START, bpm: BPM });
  assert.deepEqual(raw.notes.map((n) => n.offsetMs), [120, -110]);
  assert.deepEqual(raw.notes.map((n) => n.slot), [0, 6]);
});

test("large latency can move an onset into the next slot range", () => {
  // 200 ms latency: a raw onset at slot 1 time really belongs to slot 0 (+50 ms).
  const r = quantize([{ time: at(1), midi: 60 }], { phraseStart: START, bpm: BPM, latency: 0.2 });
  assert.equal(r.notes[0].slot, 0);
  assert.equal(r.notes[0].offsetMs, 50);
});

test("bad options throw", () => {
  assert.throws(() => quantize([], { phraseStart: 0, bpm: 0 }), TypeError);
  assert.throws(() => quantize([], { phraseStart: NaN, bpm: 80 }), TypeError);
  assert.throws(() => quantize(null, { phraseStart: 0, bpm: 80 }), TypeError);
});

test("isValidPhrase checks the JSON contract", () => {
  assert.ok(isValidPhrase(emptyPhrase()));
  assert.ok(!isValidPhrase(new Array(23).fill(null)));
  const p = emptyPhrase(); p[3] = 100;
  assert.ok(!isValidPhrase(p));
  const q = emptyPhrase(); q[3] = "A3";
  assert.ok(!isValidPhrase(q));
});
