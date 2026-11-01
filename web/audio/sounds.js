// sounds.js: the catalog of recorded instruments the band can use.
// Pure data, shared by the browser (sampler.js) and the downloader
// (samples/fetch.mjs). Each option lists its files: where to download each
// one from, where it is stored under web/samples/, and what it plays:
//   midi  - pitched note (MIDI number), or
//   name  - drum sound: kick | snare | hat | hatOpen | sticks | crash
//   dyn   - loudness layer, 0 (softest) .. 1 (hardest); default 0.5

const GLEITZ = "https://gleitz.github.io/midi-js-soundfonts";
const TONEJS = "https://nbrosowsky.github.io/tonejs-instruments/samples";
const SMPL = "https://smpldsnds.github.io";
const FLAT = ["C", "Db", "D", "Eb", "E", "F", "Gb", "G", "Ab", "A", "Bb", "B"];
const SHARP_S = ["C", "Cs", "D", "Ds", "E", "F", "Fs", "G", "Gs", "A", "As", "B"];
const oct = (m) => Math.floor(m / 12) - 1;
// Takes that the source repos do not have.
const MISSING = new Set(["pizz_bb1_mc", "pizz_bb1_md", "pizz_e3_pd", "A_071__B4_3", "A_076__E5_3", "A_081__A5_3"]);
const range = (lo, hi, step = 1) => Array.from({ length: Math.floor((hi - lo) / step) + 1 }, (_, i) => lo + i * step);

/** A General MIDI soundfont instrument (one MP3 per semitone, MIT/CC-BY-SA). */
function gleitz(id, font, inst, lo, hi) {
  return range(lo, hi).map((m) => {
    const n = `${FLAT[m % 12]}${oct(m)}`;
    return { midi: m, url: `${GLEITZ}/${font}/${inst}-mp3/${n}.mp3`, path: `${id}/${n}.mp3` };
  });
}

/** A tonejs-instruments set (a few notes, named like "Cs4"). */
function tonejs(id, inst, midis) {
  return midis.map((m) => {
    const n = `${SHARP_S[m % 12]}${oct(m)}`;
    return { midi: m, url: `${TONEJS}/${inst}/${n}.mp3`, path: `${id}/${n}.mp3` };
  });
}

const PC = { c: 0, db: 1, d: 2, eb: 3, e: 4, f: 5, gb: 6, g: 7, ab: 8, a: 9, bb: 10, b: 11 };
const nameToMidi = (n) => { const m = /^([a-g]b?)(\d)$/.exec(n); return 12 * (Number(m[2]) + 1) + PC[m[1]]; };

/**
 * A Karoryfer electric guitar (CC0, github.com/sfzinstruments). Only two loudness
 * layers and two takes per note are downloaded, to keep the size down.
 * `file(note, layer, take)` gives the sample's path inside the repo.
 */
function karoryfer(id, repo, notes, layers, file) {
  const R = `https://raw.githubusercontent.com/sfzinstruments/${repo}/master`;
  const out = [];
  for (const n of notes) {
    layers.forEach((layer, li) => {
      for (const take of [1, 2]) {
        const f = file(n, layer, take);
        out.push({ midi: nameToMidi(n), dyn: layers.length > 1 ? 0.3 + (0.6 * li) / (layers.length - 1) : 0.5,
          url: `${R}/${f}`, path: `${id}/${f.split("/").pop()}` });
      }
    });
  }
  return out;
}
const EMILY_NOTES = ["db2", "e2", "gb2", "a2", "c3", "eb3", "gb3", "a3", "c4", "eb4", "gb4", "a4", "c5", "eb5", "gb5", "a5", "c6", "d6"];
const SHINY_NOTES = ["db2", "e2", "gb2", "a2", "c3", "eb3", "gb3", "a3", "c4", "eb4", "gb4", "a4", "c5", "eb5", "gb5", "a5", "c6"];

const emily = (id) => karoryfer(id, "karoryfer.emilyguitar", EMILY_NOTES, ["mf", "f"], (n, l, t) => `notes/${n}_${l}_rr${t}.wav`);
const shiny = (id) => karoryfer(id, "karoryfer.shinyguitar", SHINY_NOTES, ["vl2", "vl3"], (n, l, t) => `Samples/electric/${n}_${l}_rr${t}_2.wav`);

const DYN5 = ["Softest", "Soft", "Med", "Hard", "Hardest"];
const dyn5 = (i) => i / 4;

/** Hydrogen "GM kit": real acoustic drums with 5 loudness layers (GPL-2.0). */
function hydrogenKit(id) {
  const H = `${SMPL}/hydrogen-drum-samples`;
  const out = [];
  const layered = (name, dir, file) => DYN5.forEach((d, i) =>
    out.push({ name, dyn: dyn5(i), url: `${H}/${dir}/${file}-${d}.m4a`, path: `${id}/${file}-${d}.m4a` }));
  layered("kick", "h2ogmbd", "Kick");
  layered("snare", "h2ogmsn", "Snare");
  layered("sticks", "h2ogmsn", "SideStick");
  layered("hat", "h2ogmhh", "HatClosed");
  layered("hatOpen", "h2ogmhh", "HatOpen");
  layered("crash", "h2ogmcy", "Crash");
  return out;
}

/** A Tone.js drum kit (one sample per drum). */
function toneKit(id, kit) {
  const D = `https://tonejs.github.io/audio/drum-samples/${kit}`;
  return [["kick", "kick"], ["snare", "snare"], ["hat", "hihat"]].map(([name, f]) =>
    ({ name, url: `${D}/${f}.mp3`, path: `${id}/${f}.mp3` }));
}

/** Upright bass, plucked (d. smolken, CC0): 3 loudness layers x 4 takes. */
function uprightBass(id) {
  const B = `${SMPL}/sfzinstruments-dsmolken-double-bass/pizz`;
  const notes = { c1: 24, eb1: 27, g1: 31, bb1: 34, d2: 38, f2: 41, a2: 45, c3: 48, e3: 52, g3: 55, a3: 57 };
  const out = [];
  for (const [n, m] of Object.entries(notes)) {
    for (const [d, dyn] of [["p", 0.2], ["m", 0.55], ["f", 0.9]]) {
      for (const rr of ["a", "b", "c", "d"]) {
        if (MISSING.has(`pizz_${n}_${d}${rr}`)) continue;
        out.push({ midi: m, dyn, url: `${B}/pizz_${n}_${d}${rr}.m4a`, path: `${id}/pizz_${n}_${d}${rr}.m4a` });
      }
    }
  }
  return out;
}

/** jRhodes3d electric piano (Jeff Learman; samples CC BY-NC): 5 loudness layers. */
function rhodes(id) {
  const R = `${SMPL}/sfzinstruments-jlearman-jrhodes3d/jRhodes3d-mono`;
  const notes = { 40: "E2", 45: "A2", 50: "D3", 55: "G3", 59: "B3", 62: "D4", 65: "F4", 71: "B4", 76: "E5", 81: "A5" };
  const out = [];
  for (const [m, n] of Object.entries(notes)) {
    for (const layer of [2, 3, 4]) {
      const f = `A_${String(m).padStart(3, "0")}__${n}_${layer}.m4a`;
      if (MISSING.has(f.slice(0, -4))) continue;
      out.push({ midi: Number(m), dyn: (layer - 2) / 2, url: `${R}/${f}`, path: `${id}/${f}` });
    }
  }
  return out;
}

/**
 * The options per part. The first option of each part is the default.
 * `credit` names the source and its license (shown on the sound page and README).
 * `amp` ("clean" | "blues") sends a guitar recorded direct through an amp model.
 * `db` evens out loudness between the options of a part (measured, in decibels).
 */
export const SOUND_OPTIONS = {
  guitar: [
    { id: "gtr-emily-blues", db: 4.5, amp: "blues", label: "Epiphone, blues amp", note: "real guitar, warm and a bit gritty",
      credit: "Karoryfer Emilyguitar (CC0)", files: emily("gtr-emily") },
    { id: "gtr-emily-clean", db: 4.4, amp: "clean", label: "Epiphone, clean amp", note: "real guitar, clean",
      credit: "Karoryfer Emilyguitar (CC0)", files: emily("gtr-emily") },
    { id: "gtr-shiny-clean", db: 3.4, amp: "clean", label: "Archtop, clean amp", note: "real hollow-body jazz guitar",
      credit: "Karoryfer Shinyguitar (CC0)", files: shiny("gtr-shiny") },
    { id: "gtr-shiny-blues", db: 3.6, amp: "blues", label: "Archtop, blues amp", note: "hollow-body, pushed amp",
      credit: "Karoryfer Shinyguitar (CC0)", files: shiny("gtr-shiny") },
    { id: "gtr-jazz", db: 0.7, label: "Jazz guitar", note: "warm hollow-body, neck pickup",
      credit: "MusyngKite soundfont (CC BY-SA 3.0)", files: gleitz("gtr-jazz", "MusyngKite", "electric_guitar_jazz", 40, 88) },
    { id: "gtr-clean", db: 4.2, label: "Clean electric", note: "bright single-coil",
      credit: "MusyngKite soundfont (CC BY-SA 3.0)", files: gleitz("gtr-clean", "MusyngKite", "electric_guitar_clean", 40, 88) },
    { id: "gtr-crunch", db: 0, label: "Crunchy blues", note: "overdriven amp",
      credit: "FluidR3 GM soundfont (MIT)", files: gleitz("gtr-crunch", "FluidR3_GM", "overdriven_guitar", 40, 88) },
    { id: "gtr-fluid-jazz", db: 0.6, label: "Jazz guitar 2", note: "darker, rounder",
      credit: "FluidR3 GM soundfont (MIT)", files: gleitz("gtr-fluid-jazz", "FluidR3_GM", "electric_guitar_jazz", 40, 88) },
    { id: "gtr-tonejs", db: 4.1, label: "Electric (old)", note: "the previous sound",
      credit: "tonejs-instruments", files: tonejs("gtr-tonejs", "guitar-electric", [37, 40, 42, 45, 48, 51, 54, 57, 60, 63, 66, 69, 72, 75, 78, 81, 84]) },
  ],
  bass: [
    { id: "bass-upright", db: 3.7, label: "Upright bass", note: "plucked double bass",
      credit: "d. smolken double bass (CC0)", files: uprightBass("bass-upright") },
    { id: "bass-finger", db: -1.2, label: "Electric bass", note: "fingerstyle",
      credit: "MusyngKite soundfont (CC BY-SA 3.0)", files: gleitz("bass-finger", "MusyngKite", "electric_bass_finger", 28, 60) },
    { id: "bass-tonejs", db: 5.3, label: "Electric bass (old)", note: "the previous sound",
      credit: "tonejs-instruments", files: tonejs("bass-tonejs", "bass-electric", [28, 31, 34, 37, 40, 43, 46, 49, 52, 55]) },
  ],
  keys: [
    { id: "keys-rhodes", db: -1.3, label: "Rhodes", note: "real electric piano",
      credit: "jRhodes3d by Jeff Learman (samples CC BY-NC)", files: rhodes("keys-rhodes") },
    { id: "keys-piano", db: 2.7, label: "Piano", note: "acoustic grand",
      credit: "tonejs-instruments", files: tonejs("keys-piano", "piano", [51, 54, 57, 60, 63, 66, 69, 72]) },
    { id: "keys-organ", db: -6, label: "Organ", note: "drawbar organ",
      credit: "MusyngKite soundfont (CC BY-SA 3.0)", files: gleitz("keys-organ", "MusyngKite", "drawbar_organ", 45, 76) },
    { id: "keys-off", label: "No keys", note: "guitar, bass and drums only", credit: "", files: [] },
  ],
  drums: [
    { id: "drums-hydrogen", db: 4, label: "Studio kit", note: "real kit, 5 loudness layers",
      credit: "Hydrogen GM kit (GPL-2.0)", files: hydrogenKit("drums-hydrogen") },
    { id: "drums-acoustic", db: 2.5, label: "Acoustic kit (old)", note: "the previous sound",
      credit: "Tone.js audio", files: toneKit("drums-acoustic", "acoustic-kit") },
    { id: "drums-kit3", db: -2.8, label: "Kit 3", note: "dry and punchy",
      credit: "Tone.js audio", files: toneKit("drums-kit3", "Kit3") },
  ],
};

export const PARTS = ["guitar", "bass", "keys", "drums"];
export const SOUNDS_KEY = "sound-and-complete.sounds.v1";

/** The default choice: the first option of every part. */
export function defaultSounds() {
  return Object.fromEntries(PARTS.map((p) => [p, SOUND_OPTIONS[p][0].id]));
}

export function findOption(part, id) {
  return SOUND_OPTIONS[part].find((o) => o.id === id) ?? SOUND_OPTIONS[part][0];
}
