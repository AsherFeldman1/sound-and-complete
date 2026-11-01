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

// A different flavour each song, so sessions don't repeat.
const STYLES = [
  "sparse and vocal: few notes, each one sung, with long space (think B.B. King)",
  "punchy repeated-note hooks and big bends (think Albert King)",
  "fluid, fast triplet runs that tumble down the box (think Stevie Ray Vaughan)",
  "low-register, gritty riffs on the wound strings (think Freddie King)",
  "smooth and jazzy, with chromatic passing notes into chord tones (think T-Bone Walker)",
  "call-and-response inside the call: a short question, a rest, a short reply (think Buddy Guy)",
];

function prompt(rules) {
  const style = STYLES[Math.floor(Math.random() * STYLES.length)];
  const ex = EXCHANGES.map(
    (e) => `Call ${e.exchange + 1}: bars ${e.callBars.join("-")} (chords ${e.callBars.map((b) => CHORDS[b - 1]).join(", ")}); ` +
      `the player answers over bars ${e.answerBars.join("-")} (chords ${e.answerBars.map((b) => CHORDS[b - 1]).join(", ")})` +
      (e.exchange === 2 ? " - this is the turnaround." : "."),
  ).join("\n");
  const ruleText = rules.length ? rules.map((r) => `- ${describeRule(r)}`).join("\n") : "- (none)";
  return `You are the lead guitarist in a slow 12-bar blues shuffle in A minor, trading 2-bar phrases ("calls") with a student who answers each one on guitar.

Timing grid: each call is 2 bars of shuffle triplets = 24 slots. Slot s is beat floor(s/3)+1, triplet s%3 (0 = on the beat, 2 = the swung "let"). Slots 0-11 are bar 1, 12-23 bar 2.
Pitches are MIDI numbers; keep notes between 52 (E3) and 76 (E5), mostly from A minor pentatonic / blues scale (A C D Eb E G), with chord tones on strong beats.

The three calls:
${ex}

The student practices these rules for their answers:
${ruleText}

Phrase them like a real blues guitarist, not like an exercise. The most common mistake is spreading the notes out evenly, one per beat: never do that. Instead:
- Group notes into one or two quick bursts: runs of 2-5 notes on consecutive slots (a fast triplet run), then rest.
- Often start off the beat, with a pickup on a "let" (slot 2, 5, 8 or 11) leading into the next beat.
- Land on a strong note (A, C, E or G, often on a beat) and let it ring: leave at least a beat of silence after it, usually most of bar 2.
- Use repeated notes, the blue note Eb sliding to E or D, and falling lines down the pentatonic box.
- 3 to 8 notes in total; real space is part of the lick.

Examples of good rhythm and phrasing (slot:note):
- Pickup and a falling triplet run into a held root: 2:C5 3:A4 4:G4 5:E4 6:G4 9:A4
- Repeated-note hook, then an answer to itself: 1:E5 2:E5 3:D5 4:C5 8:A4 9:C5 10:A4
- Late start, rising run into the blue-note resolution: 8:G4 9:A4 10:C5 11:D5 12:Eb5 13:E5

Write ${PER_EXCHANGE} different candidate calls for each of the 3 exchanges, and make sure a good answer under the rules exists (for example, if the rules ask for a sequence of N notes, the call needs at least N notes; if they ask to play fewer notes than the call, give the call enough notes). Vary rhythm, register and shape across candidates, and make the three exchanges feel different from each other (different starting slots, burst lengths and amounts of space), like a soloist building a story. For this song, lean towards this style: ${style}. Don't copy the examples; invent your own licks. Each note: {slot, midi}, slots strictly increasing, 0..23.`;
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
