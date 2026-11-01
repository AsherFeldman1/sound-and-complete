// llm.js: ask Claude for blues calls. The LLM is NOT trusted: every call it
// proposes goes through the proven Lean gate before it is played.
//
// Credentials: ANTHROPIC_API_KEY (or any source the Anthropic SDK resolves).
// Without credentials, or on any error, the caller falls back to callgen.js.

import Anthropic from "@anthropic-ai/sdk";
import { describeRule, CHORDS, EXCHANGES } from "./rules.js";

const MODEL = process.env.CLAUDE_MODEL || "claude-opus-5-5";
const PER_EXCHANGE = 4;

export function llmConfigured() {
  return Boolean(process.env.ANTHROPIC_API_KEY || process.env.ANTHROPIC_AUTH_TOKEN || process.env.ANTHROPIC_PROFILE);
}

const SCHEMA = {
  type: "object",
  properties: {
    exchanges: {
      type: "array",
      items: {
        type: "object",
        properties: {
          calls: {
            type: "array",
            items: {
              type: "object",
              properties: {
                notes: {
                  type: "array",
                  items: {
                    type: "object",
                    properties: { slot: { type: "integer" }, midi: { type: "integer" } },
                    required: ["slot", "midi"],
                    additionalProperties: false,
                  },
                },
              },
              required: ["notes"],
              additionalProperties: false,
            },
          },
        },
        required: ["calls"],
        additionalProperties: false,
      },
    },
  },
  required: ["exchanges"],
  additionalProperties: false,
};

function prompt(rules) {
  const ex = EXCHANGES.map(
    (e) => `Call ${e.exchange + 1}: bars ${e.callBars.join("-")} (chords ${e.callBars.map((b) => CHORDS[b - 1]).join(", ")}); ` +
      `the player answers over bars ${e.answerBars.join("-")} (chords ${e.answerBars.map((b) => CHORDS[b - 1]).join(", ")})` +
      (e.exchange === 2 ? " - this is the turnaround." : "."),
  ).join("\n");
  const ruleText = rules.length ? rules.map((r) => `- ${describeRule(r)}`).join("\n") : "- (none)";
  return `You are the lead guitarist in a slow 12-bar blues shuffle in A minor, trading 2-bar phrases ("calls") with a student who answers each one on acoustic guitar.

Timing grid: each call is 2 bars of shuffle triplets = 24 slots. Slot s is beat floor(s/3)+1, triplet s%3 (0 = on the beat, 2 = the swung "let"). Slots 0-11 are bar 1, 12-23 bar 2.
Pitches are MIDI numbers; keep notes between 52 (E3) and 76 (E5), mostly from A minor pentatonic / blues scale (A C D Eb E G), with chord tones on strong beats.

The three calls:
${ex}

The student practices these rules for their answers:
${ruleText}

Write ${PER_EXCHANGE} different candidate calls for each of the 3 exchanges. Make them idiomatic, singable blues licks (3 to 8 notes, call-and-response style, leave some space in bar 2), and make sure a good answer under the rules exists (for example, if the rules ask for a sequence of N notes, the call needs at least N notes; if they ask to play fewer notes than the call, give the call enough notes). Vary rhythm and register across candidates. Each note: {slot, midi}, slots strictly increasing, 0..23.`;
}

/** notes [{slot, midi}] -> 24-slot phrase. Out-of-range slots are dropped;
 * pitches are kept as given (the Lean gate rejects unplayable ones). */
export function notesToPhrase(notes) {
  const phrase = new Array(24).fill(null);
  for (const { slot, midi } of notes ?? []) {
    if (Number.isInteger(slot) && slot >= 0 && slot < 24 && Number.isInteger(midi) && midi >= 0 && phrase[slot] === null) {
      phrase[slot] = midi;
    }
  }
  return phrase;
}

/** Ask Claude for candidate calls: returns [[phrase...] x 3]. Throws on failure. */
export async function proposeCalls(rules, { timeoutMs = 60000 } = {}) {
  const client = new Anthropic({ timeout: timeoutMs, maxRetries: 1 });
  const response = await client.beta.messages.create({
    model: MODEL,
    max_tokens: 16000,
    betas: ["server-side-fallback-2026-07-01"],
    fallbacks: "default",
    output_config: { effort: "low", format: { type: "json_schema", schema: SCHEMA } },
    messages: [{ role: "user", content: prompt(rules) }],
  });
  if (response.stop_reason === "refusal") throw new Error("LLM declined the request");
  const text = response.content.filter((b) => b.type === "text").map((b) => b.text).join("");
  const data = JSON.parse(text);
  const out = [0, 1, 2].map((e) => (data.exchanges?.[e]?.calls ?? []).map((c) => notesToPhrase(c.notes)));
  if (out.every((calls) => calls.length === 0)) throw new Error("LLM returned no calls");
  return out;
}
