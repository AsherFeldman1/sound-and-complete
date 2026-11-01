// sounds-page.js: audition and choose the band's recorded instruments.
import { Band } from "./audio/band.js";
import { SOUND_OPTIONS, PARTS, SOUNDS_KEY, defaultSounds } from "./audio/sounds.js";

const PART_LABELS = { guitar: "Lead guitar (plays the calls)", bass: "Bass", keys: "Keys", drums: "Drums" };
const PREVIEW = { bass: ["bass"], keys: ["keys"], drums: ["kick", "snare", "hat", "crash"] };
// An A minor blues lick on the 24-slot triplet grid (2 bars).
const LICK = [72, null, 69, 67, null, 64, 67, null, 69, 72, null, 74, 75, 76, null, 72, null, 69, null, null, null, null, null, null];
const BPM = 80;

const $ = (id) => document.getElementById(id);
let choice = { ...defaultSounds() };
try { Object.assign(choice, JSON.parse(localStorage.getItem(SOUNDS_KEY) || "{}")); } catch { /* ignore */ }
const save = () => { try { localStorage.setItem(SOUNDS_KEY, JSON.stringify(choice)); } catch { /* ignore */ } };

let ctx, band;
async function ready() {
  if (!ctx) { ctx = new AudioContext({ latencyHint: "interactive", sampleRate: 48000 }); band = new Band(ctx); }
  if (ctx.state !== "running") await ctx.resume();
  band.stop();
  $("status").textContent = "Loading sounds…";
  const ok = await band.loadSamples(choice);
  $("status").textContent = ok ? "" : "Could not load the samples. Run make install.";
  return ok;
}

async function preview(part) {
  if (!(await ready())) return;
  const t = ctx.currentTime + 0.15;
  if (part === "guitar") band.playPhrase(LICK, t, BPM);
  else band.scheduleSong({ startTime: t, bpm: BPM, bars: 2, countInBars: 0, only: PREVIEW[part] });
}

async function full() {
  if (!(await ready())) return;
  const { songStart } = band.scheduleSong({ startTime: ctx.currentTime + 0.15, bpm: BPM, bars: 4, countInBars: 0 });
  band.playPhrase(LICK, songStart, BPM);
  band.playPhrase(LICK.map((m) => m && m - 5), songStart + 2 * 4 * 60 / BPM, BPM);
}

function render() {
  $("parts").innerHTML = "";
  for (const part of PARTS) {
    const card = document.createElement("div");
    card.className = "sound-part";
    card.innerHTML = `<h2>${PART_LABELS[part]}</h2><div class="sound-opts"></div>`;
    for (const o of SOUND_OPTIONS[part]) {
      const b = document.createElement("button");
      b.className = "sound-opt" + (choice[part] === o.id ? " on" : "");
      b.innerHTML = `<b>${o.label}</b><span>${o.note}</span>${o.credit ? `<small>${o.credit}</small>` : ""}`;
      b.onclick = () => { choice[part] = o.id; save(); render(); preview(part); };
      card.querySelector(".sound-opts").append(b);
    }
    $("parts").append(card);
  }
}

render();
$("full").onclick = full;
$("stopAll").onclick = () => band?.stop();
