// fretboard.js: shows a phrase on a guitar neck, the way a player would finger it.
//
// fingerings(phrase) picks a string and fret for each note: it stays in
// position 1 of A minor pentatonic (frets 5-8) as much as it can, and moves to
// another position when the lick needs it.
// renderFretboard(el, phrase, {upTo, now}) draws the neck: notes before slot
// `upTo` are shown, the latest note at or before slot `now` is lit, and a
// thin line joins the notes in the order they are played.

export const STRINGS = [64, 59, 55, 50, 45, 40]; // high E (top) to low E, standard tuning
export const FRETS = 22; // a full neck; the drawing shows 15 frets, more if a lick goes higher
const NAMES = ["C", "C#", "D", "Eb", "E", "F", "F#", "G", "G#", "A", "Bb", "B"];

/** Every (string, fret) that plays `midi`. String 0 is the high E. */
function options(midi) {
  const out = [];
  STRINGS.forEach((open, s) => {
    const fret = midi - open;
    if (fret >= 0 && fret <= FRETS) out.push({ s, fret });
  });
  return out;
}

/** The five positions of A minor pentatonic up the neck, as the frets the
 * hand covers. Position 1 (frets 5-8) is home. */
export const POSITIONS = [
  { name: 1, lo: 5, hi: 8 },
  { name: 2, lo: 7, hi: 10 },
  { name: 3, lo: 9, hi: 13 },
  { name: 4, lo: 12, hi: 15 },
  { name: 5, lo: 2, hi: 5 },
  { name: 1, lo: 17, hi: 20 }, // position 1 again, an octave up
];

// What the hand prefers, as costs (lower is better):
const STRETCH = 2; // reaching 1 fret outside the position
const FAR = 10; // each further fret outside it (a real stretch: avoid)
const AWAY_FROM_HOME = 1; // per note played outside position 1
const MOVE = 4; // moving the hand to another position

/** How far a fret is outside a position (0 inside). */
const away = (fret, pos) => (fret < pos.lo ? pos.lo - fret : fret > pos.hi ? fret - pos.hi : 0);
const reachCost = (d) => (d === 0 ? 0 : STRETCH + (d - 1) * FAR);

/** The best way to play `midi` with the hand in `pos`: {s, fret, cost}. */
function bestIn(midi, pos) {
  let best = null;
  for (const o of options(midi)) {
    const cost = reachCost(away(o.fret, pos)) + (o.fret === 0 ? FAR : 0); // open strings only if nothing else
    if (!best || cost < best.cost || (cost === best.cost && o.fret < best.fret)) best = { ...o, cost };
  }
  return best ?? { s: 0, fret: 0, cost: 1000 };
}

/** [{slot, midi, s, fret, position}] for the notes of a 24-slot phrase (null = rest).
 * The hand stays in position 1 of A minor pentatonic when it can, reaches a
 * fret outside it for a single note, and moves to another position only when
 * the lick goes where position 1 can't comfortably play it. The plan is the
 * cheapest over the whole lick (dynamic programming over positions). */
export function fingerings(phrase) {
  const notes = [];
  (phrase ?? []).forEach((midi, slot) => { if (midi != null) notes.push({ slot, midi }); });
  if (!notes.length) return [];
  const P = POSITIONS.length;
  // cost[i][q]: cheapest way to play notes 0..i ending with the hand in position q.
  const cost = [], from = [];
  notes.forEach((n, i) => {
    cost.push([]); from.push([]);
    for (let q = 0; q < P; q++) {
      const here = bestIn(n.midi, POSITIONS[q]).cost + (q === 0 ? 0 : AWAY_FROM_HOME);
      if (i === 0) { cost[i][q] = here + (q === 0 ? 0 : MOVE); from[i][q] = -1; continue; }
      let b = Infinity, bq = 0;
      for (let r = 0; r < P; r++) {
        const c = cost[i - 1][r] + (r === q ? 0 : MOVE);
        if (c < b) { b = c; bq = r; }
      }
      cost[i][q] = b + here; from[i][q] = bq;
    }
  });
  // Walk back from the cheapest end (ending at home is worth a move back).
  let q = 0, b = Infinity;
  for (let r = 0; r < P; r++) {
    const c = cost[notes.length - 1][r] + (r === 0 ? 0 : MOVE);
    if (c < b) { b = c; q = r; }
  }
  const plan = new Array(notes.length);
  for (let i = notes.length - 1; i >= 0; i--) { plan[i] = q; q = from[i][q]; }
  return notes.map((n, i) => {
    const pos = POSITIONS[plan[i]];
    const o = bestIn(n.midi, pos);
    return { ...n, s: o.s, fret: o.fret, position: pos.name };
  });
}

const W = 760, H = 150, NUT = 34, PAD_Y = 16;
let shownFrets = 15;
const fretX = (f) => NUT + (f / shownFrets) * (W - NUT - 10);
const strY = (s) => PAD_Y + (s * (H - 2 * PAD_Y)) / 5;
/** Centre of the space where fret `f` is played (fret 0 = left of the nut). */
const noteX = (f) => (f === 0 ? NUT - 14 : (fretX(f - 1) + fretX(f)) / 2);

/** Draw `phrase` on the neck inside `el`. Only redraws when something changed. */
export function renderFretboard(el, phrase, { upTo = 24, now = -1 } = {}) {
  const fs = fingerings(phrase);
  const lit = fs.filter((f) => f.slot <= now).at(-1);
  const key = JSON.stringify([phrase, upTo, lit?.slot ?? -1]);
  if (el.dataset.key === key) return;
  el.dataset.key = key;
  shownFrets = Math.max(15, ...fs.map((f) => f.fret + 1));
  const parts = [];
  parts.push(`<rect x="${NUT}" y="${PAD_Y - 8}" width="${W - NUT - 10}" height="${H - 2 * PAD_Y + 16}" rx="3" class="fb-wood"/>`);
  for (const f of [3, 5, 7, 9, 15, 17, 19, 21].filter((f) => f <= shownFrets)) parts.push(`<circle cx="${noteX(f)}" cy="${H / 2}" r="5" class="fb-inlay"/>`);
  parts.push(`<circle cx="${noteX(12)}" cy="${strY(1) + (strY(2) - strY(1)) / 2}" r="5" class="fb-inlay"/><circle cx="${noteX(12)}" cy="${strY(3) + (strY(4) - strY(3)) / 2}" r="5" class="fb-inlay"/>`);
  for (let f = 1; f <= shownFrets; f++) parts.push(`<line x1="${fretX(f)}" x2="${fretX(f)}" y1="${PAD_Y - 8}" y2="${H - PAD_Y + 8}" class="fb-fret"/>`);
  parts.push(`<rect x="${NUT - 4}" y="${PAD_Y - 8}" width="5" height="${H - 2 * PAD_Y + 16}" class="fb-nut"/>`);
  STRINGS.forEach((_, s) => parts.push(`<line x1="${NUT - 26}" x2="${W - 10}" y1="${strY(s)}" y2="${strY(s)}" class="fb-string" stroke-width="${0.8 + s * 0.35}"/>`));
  for (const f of [3, 5, 7, 9, 12, 15, 17, 19, 21].filter((f) => f <= shownFrets)) parts.push(`<text x="${noteX(f)}" y="${H - 1}" class="fb-num">${f}</text>`);
  // Path of the lick: thin line joining the notes played so far, in order.
  const shown = fs.filter((f) => f.slot < upTo);
  if (shown.length > 1) parts.push(`<polyline points="${shown.map((f) => `${noteX(f.fret)},${strY(f.s)}`).join(" ")}" class="fb-path"/>`);
  shown.forEach((f) => {
    const on = lit && f.slot === lit.slot;
    parts.push(`<g class="fb-note${on ? " on" : ""}"><circle cx="${noteX(f.fret)}" cy="${strY(f.s)}" r="${on ? 11 : 9}"/>` +
      `<text x="${noteX(f.fret)}" y="${strY(f.s) + 3.5}">${NAMES[f.midi % 12]}</text></g>`);
  });
  const names = shown.map((f) => NAMES[f.midi % 12]).join(" ");
  el.innerHTML = `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="${names ? `Notes on the neck: ${names}` : "Guitar neck"}">${parts.join("")}</svg>`;
}
