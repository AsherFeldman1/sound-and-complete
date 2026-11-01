import test from "node:test";
import assert from "node:assert/strict";
import { generateCalls } from "./callgen.js";
import { notesToPhrase } from "./llm.js";
import { RULES, defaultRule, describeRule } from "./rules.js";

test("built-in calls are 24 slots, have notes, and stay on the guitar", () => {
  for (const call of generateCalls(200, 42)) {
    assert.equal(call.length, 24);
    const notes = call.filter((x) => x !== null);
    assert.ok(notes.length >= 1);
    for (const m of notes) assert.ok(m >= 40 && m <= 88, `pitch ${m}`);
  }
});

test("same seed, same calls", () => {
  assert.deepEqual(generateCalls(5, 7), generateCalls(5, 7));
});

test("LLM notes to phrase: drops bad slots and duplicates, keeps odd pitches for the gate", () => {
  const p = notesToPhrase([{ slot: 0, midi: 64 }, { slot: 0, midi: 60 }, { slot: 30, midi: 60 }, { slot: 5, midi: 100 }]);
  assert.equal(p.length, 24);
  assert.equal(p[0], 64);
  assert.equal(p[5], 100);
  assert.equal(p.filter((x) => x !== null).length, 2);
});

test("every rule has a default and a description", () => {
  for (const r of RULES) assert.match(describeRule(defaultRule(r.rule)), /\w/);
});

test("answer ideas: on the guitar, scale-friendly first", async () => {
  const { answerIdeas } = await import("./callgen.js");
  const call = [64, null, null, 62, null, null, 60, null, 64, ...new Array(15).fill(null)];
  const ideas = answerIdeas(call);
  assert.ok(ideas.length > 50);
  assert.deepEqual(ideas[0], call); // the plain echo comes first
  for (const ph of ideas) assert.ok(ph.every((m) => m === null || (m >= 40 && m <= 88)));
});
