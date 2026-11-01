// callgen.js: built-in blues call generator, used when no LLM is available
// (no API key, offline, or the LLM is slow). Pure and seedable, so it can be
// tested. The Lean gate checks these calls exactly like the LLM's.
//
// Phrase = 24 entries (2 bars of shuffle triplets), each null or a MIDI note.

export const PHRASE_SLOTS = 24;

// A minor blues scale, 2 octaves around the guitar's sweet spot: A C D Eb E G.
const SCALE = [52, 55, 57, 60, 62, 63, 64, 67, 69, 72, 74, 75, 76];

// Rhythm cells: note starts within one beat (slots 0,1,2). Shuffle-friendly.
const CELLS = [[0], [0, 2], [2], [], [0], [0, 2], [2], []];

/** Small deterministic random generator (mulberry32). */
export function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** One 2-bar call: busy first bar, sparse second bar, ends on a strong note. */
export function generateCall(rand) {
  const pick = (xs) => xs[Math.floor(rand() * xs.length)];
  const phrase = new Array(PHRASE_SLOTS).fill(null);
  let idx = 2 + Math.floor(rand() * 8); // index into SCALE
  // Bar 1: 3-4 beats of rhythm cells; bar 2: one or two beats, then silence.
  const beats = [0, 1, 2, 3].filter(() => rand() < 0.7);
  while (beats.length < 2) beats.unshift(beats.length ? 0 : 1); // always start in bar 1
  const bar2 = [4, 5].filter(() => rand() < 0.5);
  if (bar2.length === 0) bar2.push(4);
  let count = 0;
  for (const b of [...beats, ...bar2]) {
    for (const off of pick(CELLS)) {
      if (count++ >= 7) break; // calls stay singable: at most 7 notes
      const step = pick([-2, -1, -1, 0, 1, 1, 2]);
      idx = Math.max(0, Math.min(SCALE.length - 1, idx + step));
      phrase[b * 3 + off] = SCALE[idx];
    }
  }
  // Land the last note on a chord-friendly note (A, C, E or G).
  let last = -1;
  for (let i = 0; i < PHRASE_SLOTS; i++) if (phrase[i] !== null) last = i;
  if (last < 0) phrase[0] = 57;
  else phrase[last] = pick([57, 60, 64, 67, 69]);
  return phrase;
}

/** `n` calls from a seed. */
export function generateCalls(n, seed = Date.now()) {
  const rand = rng(seed);
  return Array.from({ length: n }, () => generateCall(rand));
}

// ---------------------------------------------------------------------------
// Answer ideas. The Lean grader decides which of these keep the rules; this
// only proposes musical candidates, most idiomatic first.

const BLUES_PCS = new Set([9, 0, 2, 3, 4, 7]); // A C D Eb E G
const onGuitar = (m) => m >= 40 && m <= 88;
const shiftTime = (ph, k) => ph.map((_, i) => (i - k >= 0 && i - k < PHRASE_SLOTS ? ph[i - k] : null));

/** Candidate answers to `call`, in order of preference.
 * `chordPcs`: pitch classes of the chord under each answer bar, [[...], [...]],
 * used to also try each idea with a chord tone placed on a beat. */
export function answerIdeas(call, seed = 1, chordPcs = null) {
  const ideas = [];
  const add = (ph) => {
    if (ph.some((m) => m !== null) && ph.every((m) => m === null || onGuitar(m))) ideas.push(ph);
  };
  const notes = call.map((m, i) => [i, m]).filter(([, m]) => m !== null);
  // Echo the call, moved by musical intervals (also a "sequence").
  for (const k of [0, -2, 2, -3, 3, -5, 5, -7, 7, -12, 12]) add(call.map((m) => (m === null ? null : m + k)));
  // The start of the call, shortened (fewer notes), then moved.
  for (let n = notes.length - 1; n >= 1; n--) {
    for (const k of [0, -2, 2, -5, 5, -3, 3]) {
      const ph = new Array(PHRASE_SLOTS).fill(null);
      for (const [i, m] of notes.slice(0, n)) ph[i] = m + k;
      add(ph);
    }
  }
  // Echo moved later in time (leaves space, lands off the beat).
  for (const t of [1, 2, 3, 4, 6]) for (const k of [0, -2, 2, -5, 5]) add(shiftTime(call.map((m) => (m === null ? null : m + k)), t));
  // Fresh blues licks.
  const rand = rng(seed);
  for (let i = 0; i < 150; i++) add(generateCall(rand));
  // Chord-tone repairs: each of the first ideas, with one beat set to a chord tone.
  if (chordPcs) {
    const base = ideas.slice(0, 40);
    for (const ph of base) {
      for (let s = 0; s < PHRASE_SLOTS; s += 3) {
        const near = ph[s] ?? ph.find((m) => m !== null) ?? 60;
        for (const pc of chordPcs[s < 12 ? 0 : 1]) {
          // The chord tone closest to the note already there.
          let m = near - ((((near - pc) % 12) + 12) % 12);
          if (near - m > 6) m += 12;
          const fixed = ph.slice();
          fixed[s] = m;
          add(fixed);
        }
      }
    }
  }
  // Ideas that stay in the A minor blues scale first (stable: keeps the order above).
  const outside = (ph) => ph.filter((m) => m !== null && !BLUES_PCS.has(m % 12)).length;
  return ideas.map((ph, i) => [outside(ph), i, ph]).sort((a, b) => a[0] - b[0] || a[1] - b[1]).map((x) => x[2]);
}
