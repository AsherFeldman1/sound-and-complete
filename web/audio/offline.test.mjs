// Run: node --test web/audio/
import { test } from "node:test";
import assert from "node:assert/strict";
import { votePitch } from "./offline.js";

const hz = (midi, cents = 0) => 440 * Math.pow(2, (midi - 69 + cents / 100) / 12);

test("the pitch most readings agree on wins", () => {
  const r = [...Array(6)].map(() => ({ freq: hz(64), clarity: 0.95 })).concat([{ freq: hz(65), clarity: 0.9 }]);
  assert.equal(votePitch(r).midi, 64);
});

test("the body boom (~100 Hz) ringing under a higher note does not outvote it", () => {
  const boom = [...Array(8)].map(() => ({ freq: 98, clarity: 0.95 })); // G2 resonance
  const note = [...Array(4)].map(() => ({ freq: hz(64), clarity: 0.95 })); // E4 played
  assert.equal(votePitch([...boom, ...note]).midi, 64);
});

test("a real low note still wins when it is what was played", () => {
  const r = [...Array(6)].map(() => ({ freq: hz(45), clarity: 0.95 })); // open A
  assert.equal(votePitch(r).midi, 45);
});

test("too few readings give no pitch", () => {
  assert.equal(votePitch([{ freq: hz(60), clarity: 0.9 }]), null);
});

test("tuning offset is applied before rounding", () => {
  const flat = [...Array(5)].map(() => ({ freq: hz(57, -45), clarity: 0.95 })); // A3, 45 cents flat
  assert.equal(votePitch(flat, -0.4).midi, 57);
});
