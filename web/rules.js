// rules.js: the rule catalog, shared by the browser and the server.
// Each rule's JSON matches `parseRule` in Main.lean. The meaning of each rule
// is defined in SoundAndComplete/Spec.lean; the text here only describes it.

export const NOTE_NAMES = ["C", "C#", "D", "Eb", "E", "F", "F#", "G", "G#", "A", "Bb", "B"];
export const midiName = (m) => `${NOTE_NAMES[m % 12]}${Math.floor(m / 12) - 1}`;

// Param kinds: "int" (with min/max), "tone", "note" (pitch class 0..11), "midi".
export const RULES = [
  { rule: "startNear", group: "Answer the call", label: "Start near",
    params: [{ key: "frets", kind: "int", min: 0, max: 12, def: 2 }],
    text: (p) => `Start within ${p.frets} fret${p.frets === 1 ? "" : "s"} of the call's last note` },
  { rule: "echoSomeRhythm", group: "Answer the call", label: "Echo some rhythm",
    params: [{ key: "k", kind: "int", min: 1, max: 8, def: 2 }],
    text: (p) => `Start at least ${p.k} note${p.k === 1 ? "" : "s"} exactly where the call started one` },
  { rule: "echoRhythm", group: "Answer the call", label: "Echo the rhythm",
    params: [], text: () => "Copy the call's rhythm exactly (notes are free)" },
  { rule: "sequence", group: "Answer the call", label: "Sequence",
    params: [{ key: "n", kind: "int", min: 1, max: 4, def: 3 }],
    text: (p) => `Your first ${p.n} notes repeat the call's first ${p.n}, moved up or down (not an exact copy)` },
  { rule: "sayLess", group: "Answer the call", label: "Say less",
    params: [], text: () => "Play fewer notes than the call" },
  { rule: "maxLeap", group: "Shape", label: "Small steps",
    params: [{ key: "frets", kind: "int", min: 0, max: 12, def: 5 }],
    text: (p) => `No jump bigger than ${p.frets} fret${p.frets === 1 ? "" : "s"} between notes` },
  { rule: "stayBetween", group: "Shape", label: "Stay in position",
    params: [{ key: "low", kind: "midi", def: 52 }, { key: "high", kind: "midi", def: 69 }],
    text: (p) => `Every note between ${midiName(p.low)} and ${midiName(p.high)}` },
  { rule: "avoid", group: "Shape", label: "Avoid a note",
    params: [{ key: "note", kind: "note", def: 9 }],
    text: (p) => `Never play ${NOTE_NAMES[p.note]}` },
  { rule: "chordToneOnBeat", group: "Harmony", label: "Land on a chord tone",
    params: [{ key: "tone", kind: "tone", def: "third" }, { key: "beat", kind: "int", min: 1, max: 8, def: 5 }],
    text: (p) => `Play the chord's ${p.tone} exactly on ${beatName(p.beat)} of your answer` },
  { rule: "maxNotesPerBar", group: "Rhythm", label: "Leave room",
    params: [{ key: "n", kind: "int", min: 0, max: 12, def: 3 }],
    text: (p) => `At most ${p.n} note${p.n === 1 ? "" : "s"} per bar` },
  { rule: "leaveSpace", group: "Rhythm", label: "Wait before answering",
    params: [{ key: "slots", kind: "int", min: 0, max: 23, def: 3 }],
    text: (p) => `Don't play during the first ${p.slots} triplet${p.slots === 1 ? "" : "s"} (${(p.slots / 3).toFixed(1).replace(/\.0$/, "")} beat${p.slots === 3 ? "" : "s"})` },
];

/** Beat 1..8 of a two-bar answer, the way musicians count it. */
export const beatName = (b) => `bar ${b <= 4 ? 1 : 2}, beat ${((b - 1) % 4) + 1}`;

export const RULE_BY_NAME = Object.fromEntries(RULES.map((r) => [r.rule, r]));

/** Plain-English description of one rule JSON. */
export function describeRule(r) {
  const def = RULE_BY_NAME[r.rule];
  return def ? def.text(r) : JSON.stringify(r);
}

/** Default JSON for a rule. */
export function defaultRule(name) {
  const def = RULE_BY_NAME[name];
  return Object.fromEntries([["rule", name], ...def.params.map((p) => [p.key, p.def])]);
}

// The song: three exchanges. The call is 2 bars, then you answer for 2 bars.
export const CHORD_PCS = { Am7: [9, 0, 4, 7], Dm7: [2, 5, 9, 0], E7: [4, 8, 11, 2] };
export const CHORDS = ["Am7", "Am7", "Am7", "Am7", "Dm7", "Dm7", "Am7", "Am7", "E7", "Dm7", "Am7", "E7"];
export const EXCHANGES = [0, 1, 2].map((e) => ({
  exchange: e,
  callBars: [4 * e + 1, 4 * e + 2],
  answerBars: [4 * e + 3, 4 * e + 4],
}));
