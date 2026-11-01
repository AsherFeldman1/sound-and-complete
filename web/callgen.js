// callgen.js: built-in blues call generator, used when no LLM is available
// (no API key, offline, or the LLM is slow). Pure and seedable, so it can be
// tested. The Lean gate checks these calls exactly like the LLM's.
//
// Phrase = 24 entries (2 bars of shuffle triplets), each null or a MIDI note.

export const PHRASE_SLOTS = 24;

// A minor blues scale, 2 octaves around the guitar's sweet spot: A C D Eb E G.
const SCALE = [52, 55, 57, 60, 62, 63, 64, 67, 69, 72, 74, 75, 76];

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

/**
 * One 2-bar call, phrased like a blues player rather than one note per beat:
 * it often starts off the beat (a pickup), plays one or two quick bursts of
 * triplets, lands on a chord-friendly note it lets ring, and leaves space.
 */
export function generateCall(rand) {
  const pick = (xs) => xs[Math.floor(rand() * xs.length)];
  const phrase = new Array(PHRASE_SLOTS).fill(null);
  let idx = 4 + Math.floor(rand() * 6); // index into SCALE: start mid-neck
  const dir = rand() < 0.65 ? -1 : 1; // blues licks mostly fall
  const place = (slot) => {
    if (slot >= 0 && slot < PHRASE_SLOTS) phrase[slot] = SCALE[idx];
  };
  const step = () => {
    // Mostly scale steps in the lick's direction, sometimes a repeat or a turn back.
    idx = Math.max(0, Math.min(SCALE.length - 1, idx + pick([dir, dir, dir, 0, -dir, 2 * dir])));
  };
  // Burst 1: a pickup on the "let" or just after the beat, then a quick run.
  let slot = pick([2, 2, 1, 0, 5, 3]);
  const burst1 = pick([3, 3, 4, 4, 5]);
  for (let k = 0; k < burst1; k++) { place(slot); step(); slot++; }
  // Sometimes a short rest and a second, shorter burst (call-and-response inside the call).
  if (rand() < 0.55) {
    slot += pick([2, 3, 4]);
    const burst2 = pick([2, 2, 3]);
    for (let k = 0; k < burst2 && slot < 15; k++) { place(slot); step(); slot++; }
  }
  // Land on A, C, E or G, on or just before a beat, and let it ring: nothing after it.
  slot = Math.min(slot + pick([0, 1, 2]), 17);
  const land = pick([57, 60, 64, 67, 69, 72]);
  const lastSet = phrase.findLastIndex((m) => m !== null);
  if (slot <= lastSet) slot = lastSet + 1;
  phrase[Math.min(slot, PHRASE_SLOTS - 1)] = land;
  return phrase;
}

/**
 * How lick-like a call's rhythm is (higher is better). Not part of anything
 * proven: it only decides which of several calls that pass the Lean gate to try
 * first. Rewards quick runs, a pickup, room to breathe and a held last note;
 * penalises notes spread out evenly, one per beat.
 */
export function tasteScore(phrase) {
  const on = phrase.map((m, i) => (m === null ? -1 : i)).filter((i) => i >= 0);
  if (on.length === 0) return -10;
  let score = 0;
  const gaps = on.slice(1).map((s, i) => s - on[i]);
  score += Math.min(4, gaps.filter((g) => g === 1).length); // quick triplet runs
  if (on[0] % 3 !== 0) score += 1; // starts with a pickup / off the beat
  const tail = PHRASE_SLOTS - 1 - on[on.length - 1];
  if (Math.max(tail, ...gaps) >= 6) score += 2; // real space somewhere
  if (tail >= 4) score += 1; // the last note rings
  if (gaps.length >= 2) {
    const mean = gaps.reduce((a, b) => a + b, 0) / gaps.length;
    const sd = Math.sqrt(gaps.reduce((a, g) => a + (g - mean) ** 2, 0) / gaps.length);
    if (sd / mean < 0.35) score -= 3; // evenly spread: sounds like an exercise
  }
  if (on.filter((s) => s % 3 === 0).length / on.length > 0.7) score -= 1; // all on the beat
  if (on.length < 3 || on.length > 9) score -= 2;
  return score;
}

/** Calls sorted most lick-like first (stable). */
export function byTaste(calls) {
  return calls.map((c, i) => [tasteScore(c), i, c]).sort((a, b) => b[0] - a[0] || a[1] - b[1]).map((x) => x[2]);
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
