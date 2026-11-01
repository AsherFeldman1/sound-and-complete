import { test } from "node:test";
import assert from "node:assert/strict";
import { fingerings, STRINGS } from "./fretboard.js";

const phrase = (pairs) => { const p = new Array(24).fill(null); for (const [s, m] of pairs) p[s] = m; return p; };

test("every fingering plays the right note", () => {
  for (let m = 40; m <= 86; m++) {
    const [f] = fingerings(phrase([[0, m]]));
    assert.equal(STRINGS[f.s] + f.fret, m);
  }
});

test("an A minor box lick stays in one hand position", () => {
  const fs = fingerings(phrase([[2, 67], [3, 69], [4, 72], [5, 71], [9, 69], [14, 64], [16, 57]]));
  const frets = fs.map((f) => f.fret);
  assert.ok(Math.max(...frets) - Math.min(...frets) <= 4, `spread ${frets}`);
  assert.equal(Math.min(...frets), 5);
});

test("no open strings unless the note has nowhere else to go", () => {
  for (let m = 45; m <= 86; m++) assert.notEqual(fingerings(phrase([[0, m]]))[0].fret, 0, `midi ${m}`);
});

test("pentatonic notes in reach of the box are played in the box", () => {
  // A minor pentatonic from A2 to C5: every one has a place at frets 5-8.
  for (const m of [45, 48, 50, 52, 55, 57, 60, 62, 64, 67, 69, 72]) {
    const { fret } = fingerings(phrase([[0, m]]))[0];
    assert.ok(fret >= 5 && fret <= 8, `midi ${m} at fret ${fret}`);
  }
});

test("a lick that climbs high moves up the neck, then the hand stays in one position", () => {
  // A C D E G A up high: past position 1's reach.
  const fs = fingerings(phrase([[0, 69], [3, 72], [6, 74], [9, 76], [12, 79], [15, 81]]));
  assert.ok(fs.slice(2).every((f) => f.fret > 8), JSON.stringify(fs)); // left the home box
  const frets = fs.slice(2).map((f) => f.fret);
  assert.ok(Math.max(...frets) - Math.min(...frets) <= 4, `spread ${frets}`);
});

test("one note just outside the box is a reach, not a position change", () => {
  const fs = fingerings(phrase([[0, 57], [3, 60], [6, 59], [9, 57]])); // B3 = fret 4 on the G string
  assert.ok(fs.every((f) => f.position === 1), JSON.stringify(fs));
});

test("empty phrase has no notes", () => {
  assert.deepEqual(fingerings(new Array(24).fill(null)), []);
  assert.deepEqual(fingerings(null), []);
});
