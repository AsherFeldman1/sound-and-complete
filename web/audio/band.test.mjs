// Run: node --test web/audio/
import { test } from "node:test";
import assert from "node:assert/strict";
import { CHORDS, songEvents, songLayout, phraseNotes, renderPluck } from "./band.js";

const BPM = 80;
const BEAT = 60 / BPM;

test("CHORDS: 12 bars, expected names, voicings in mid register", () => {
  assert.equal(CHORDS.length, 12);
  assert.deepEqual(
    CHORDS.map((c) => c.name),
    ["Am7", "Am7", "Am7", "Am7", "Dm7", "Dm7", "Am7", "Am7", "E7", "Dm7", "Am7", "E7"],
  );
  for (const c of CHORDS) for (const m of c.tones) assert.ok(m >= 55 && m <= 72, `${c.name} ${m}`);
});

test("songStart = countInBars * 4 beats", () => {
  for (const countInBars of [0, 1, 2]) {
    assert.ok(Math.abs(songLayout({ bpm: BPM, countInBars }).songStart - countInBars * 4 * BEAT) < 1e-9);
  }
  // count-in events all happen before bar 1; bar 1 starts with the crash
  const ev = songEvents({ bpm: BPM, bars: 12, countInBars: 1 });
  const start = 4 * BEAT;
  for (const e of ev.filter((e) => e.bar <= 0)) assert.ok(e.time < start);
  assert.ok(ev.filter((e) => e.bar <= 0).every((e) => e.instrument === "sticks" || e.instrument === "hat"));
  assert.ok(ev.some((e) => e.instrument === "crash" && e.time === start));
  assert.equal(ev.filter((e) => e.instrument === "sticks").length, 4);
});

test("event count is sane and events are sorted, non-negative, inside their bar", () => {
  const ev = songEvents({ bpm: BPM, bars: 12, countInBars: 1 });
  assert.ok(ev.length > 300 && ev.length < 800, `count ${ev.length}`);
  const lay = songLayout({ bpm: BPM, bars: 12, countInBars: 1 });
  for (let i = 1; i < ev.length; i++) assert.ok(ev[i].time >= ev[i - 1].time);
  for (const e of ev) {
    assert.ok(e.time >= 0 && Number.isFinite(e.time));
    assert.ok(e.vel > 0 && e.vel <= 1);
    if (e.bar >= 1) {
      const t0 = lay.songStart + (e.bar - 1) * lay.barDur;
      assert.ok(e.time > t0 - 0.01 && e.time < t0 + lay.barDur, `${e.instrument} bar ${e.bar}`);
    }
  }
  for (let bar = 1; bar <= 12; bar++) {
    for (const inst of ["kick", "snare", "hat", "bass", "keys"]) {
      assert.ok(ev.some((e) => e.bar === bar && e.instrument === inst), `${inst} in bar ${bar}`);
    }
  }
  // more bars -> proportionally more events, form repeats
  assert.ok(songEvents({ bpm: BPM, bars: 24, countInBars: 1 }).length > 1.9 * ev.length - 20);
});

test("bass notes belong to the bar's chord scale, in a low octave", () => {
  const ev = songEvents({ bpm: BPM, bars: 24, countInBars: 2 });
  const bass = ev.filter((e) => e.instrument === "bass");
  assert.equal(bass.length, 24 * 8);
  for (const e of bass) {
    const c = CHORDS[(e.bar - 1) % 12];
    assert.ok(c.scale.includes(e.midi % 12), `bar ${e.bar} ${c.name} midi ${e.midi}`);
    assert.ok(e.midi >= 28 && e.midi <= 55);
  }
  // every bar starts on its chord root
  for (let bar = 1; bar <= 24; bar++) {
    const first = bass.find((e) => e.bar === bar);
    assert.equal(first.midi % 12, CHORDS[(bar - 1) % 12].root % 12);
  }
});

test("no backing pitch above MIDI 76; keys play the bar's chord tones", () => {
  const ev = songEvents({ bpm: 120, bars: 12, countInBars: 1 });
  for (const e of ev) if (e.midi != null) assert.ok(e.midi <= 76, `${e.instrument} ${e.midi}`);
  for (const e of ev.filter((e) => e.instrument === "keys" || e.instrument === "organ")) {
    assert.ok(CHORDS[e.bar - 1].tones.includes(e.midi));
  }
});

test("songEvents is deterministic", () => {
  assert.deepEqual(songEvents({ bpm: BPM }), songEvents({ bpm: BPM }));
});

test("phraseNotes: notes ring until the next note, max 1.5 beats", () => {
  const slot = BEAT / 3;
  const p = new Array(24).fill(null);
  p[0] = 57; p[2] = 60; p[12] = 64;
  const n = phraseNotes(p, BPM);
  assert.equal(n.length, 3);
  assert.ok(Math.abs(n[0].dur - 2 * slot) < 1e-9 && n[0].cut);
  assert.ok(Math.abs(n[1].dur - 1.5 * BEAT) < 1e-9 && !n[1].cut);
  assert.ok(Math.abs(n[2].dur - 1.5 * BEAT) < 1e-9 && !n[2].cut);
  assert.ok(Math.abs(n[2].time - 12 * slot) < 1e-9);
});

test("renderPluck: finite, bounded, decaying, and in tune", () => {
  const sr = 48000;
  for (const midi of [40, 57, 69, 88]) {
    const f = 440 * 2 ** ((midi - 69) / 12);
    const { data, rate } = renderPluck(sr, f, 1.0, { vel: 1, seed: 7 });
    let peak = 0;
    for (const x of data) { assert.ok(Number.isFinite(x)); peak = Math.max(peak, Math.abs(x)); }
    assert.ok(peak <= 0.81 && peak > 0.5, `peak ${peak}`);
    // later part is quieter than the start
    const rms = (a, b) => Math.sqrt(data.slice(a, b).reduce((s, x) => s + x * x, 0) / (b - a));
    const w = 2048;
    assert.ok(rms(data.length - w, data.length) < rms(0, w));
    // autocorrelation peak near the expected buffer period, played back at `rate`
    const P = (sr / f) * rate; // period inside the buffer
    const from = 4000;
    let best = 0, bestLag = 0;
    for (let lag = Math.floor(P * 0.8); lag <= Math.ceil(P * 1.25); lag++) {
      let s = 0;
      for (let i = from; i < from + 4096; i++) s += data[i] * data[i + lag];
      if (s > best) { best = s; bestLag = lag; }
    }
    assert.ok(Math.abs(bestLag - P) <= 1, `midi ${midi}: lag ${bestLag} vs ${P}`);
    assert.ok(Math.abs(rate - 1) < 0.05);
  }
});
