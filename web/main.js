// main.js: the Sound and Complete app.
//
// Flow: pick rules -> the server asks Claude for calls and the proven Lean
// gate picks ones you can answer -> play the 12-bar song (call, you answer,
// three times) -> the Lean grader checks your answers -> report card.
//
// All decisions (whether the rules are possible, gate, hint answer, grading) come from the
// server, which asks the Lean program. This file is UI, audio and timing.

import { RULES, NOTE_NAMES, midiName, describeRule, defaultRule, CHORDS, EXCHANGES } from "./rules.js";
import { quantize, PHRASE_SLOTS } from "./audio/quantize.js";
import { GuitarInput } from "./audio/input.js";
import { Band } from "./audio/band.js";
import { GuitarAmp } from "./audio/amp.js";
import { SOUNDS_KEY } from "./audio/sounds.js";
import { makeKnob } from "./knob.js";
import { PEDAL_DESIGNS, ART } from "./pedals.js";
import { renderFretboard } from "./fretboard.js";

const $ = (id) => document.getElementById(id);
const el = (tag, cls, text) => {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
};

// ---------------------------------------------------------------------------
// State

const PREFS_KEY = "sound-and-complete.app.v1";
const loadPrefs = () => {
  try { return JSON.parse(localStorage.getItem(PREFS_KEY) || "{}") || {}; } catch { return {}; }
};
const savePrefs = (p) => {
  try { localStorage.setItem(PREFS_KEY, JSON.stringify({ ...loadPrefs(), ...p })); } catch { /* ignore */ }
};

const DEFAULT_ON = ["startNear", "maxLeap", "chordToneOnBeat", "leaveSpace"];
const prefs = loadPrefs();
// ruleState[name] = {on, params}
const ruleState = Object.fromEntries(
  RULES.map((r) => [r.rule, {
    on: prefs.rules ? Boolean(prefs.rules[r.rule]?.on) : DEFAULT_ON.includes(r.rule),
    params: { ...defaultRule(r.rule), ...(prefs.rules?.[r.rule]?.params ?? {}) },
  }]),
);

const S = {
  ctx: null,
  band: null,
  input: null,
  micReady: false,
  session: null, // {exchanges: [{exchange, possible, call, hint, source, claudeRejected}]}
  played: [null, null, null],
  playing: false,
  timers: [],
  raf: 0,
};

const activeRules = () => RULES.filter((r) => ruleState[r.rule].on).map((r) => ({ ...ruleState[r.rule].params, rule: r.rule }));
const mode = () => document.querySelector("input[name=mode]:checked").value;
const bpm = () => Number($("bpm").value);

function show(screen) {
  for (const id of ["setup", "prep", "play", "report"]) $(id).classList.toggle("hidden", id !== screen);
  window.scrollTo(0, 0);
}

async function post(path, body) {
  const r = await fetch(path, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(body) });
  const j = await r.json();
  if (!r.ok || j.error) throw new Error(j.error || `HTTP ${r.status}`);
  return j;
}

async function ensureAudio() {
  if (!S.ctx) {
    S.ctx = new AudioContext({ latencyHint: "interactive", sampleRate: 48000 });
    S.band = new Band(S.ctx);
    S.band.volume = Number($("bandVol").value) / 100;
    S.amp = new GuitarAmp(S.ctx);
    S.amp.set(ampSettings());
    // The AI's guitar plays through its own copy of the same amp, set warm and
    // round, into the band's lead channel (so the Band knob and echo apply).
    S.leadAmp = new GuitarAmp(S.ctx, { output: S.band.leadOut, inputTrim: 0.6, echo: false }); // the band adds its own echo
    S.leadAmp.set({ drive: 0.5, tone: 0.42, reverb: 0.3, volume: 0.95, on: true });
    S.band.leadAmpIn = S.leadAmp.input;
    let sounds = {};
    try { sounds = JSON.parse(localStorage.getItem(SOUNDS_KEY) || "{}"); } catch { /* defaults */ }
    S.samplesReady = S.band.loadSamples(sounds); // recorded instruments (falls back to synth)
  }
  if (S.ctx.state !== "running") await S.ctx.resume();
  await S.samplesReady;
}

// ---------------------------------------------------------------------------
// Rules UI

// A rule's setting is a knob on its pedal. Every kind of setting (a number,
// a chord tone, a note name, a pitch) is a list of positions the knob clicks
// through; the printed label under the knob shows the current one.
const PARAM_LABEL = { frets: "frets", k: "notes", n: "notes", low: "low", high: "high", note: "note", tone: "tone", beat: "bar·beat", slots: "wait" };
function paramOptions(p) {
  if (p.key === "beat") return Array.from({ length: p.max - p.min + 1 }, (_, i) => [p.min + i, `${p.min + i <= 4 ? 1 : 2}·${((p.min + i - 1) % 4) + 1}`]);
  if (p.kind === "int") return Array.from({ length: p.max - p.min + 1 }, (_, i) => [p.min + i, String(p.min + i)]);
  if (p.kind === "tone") return ["root", "third", "fifth", "seventh"].map((t) => [t, t]);
  if (p.kind === "note") return NOTE_NAMES.map((n, i) => [i, n]);
  return Array.from({ length: 49 }, (_, i) => [i + 40, midiName(i + 40)]);
}

function paramControl(r, p, onTurn) {
  const st = ruleState[r.rule];
  const opts = paramOptions(p);
  const wrap = el("span", "pk");
  const input = el("input");
  Object.assign(input, { type: "range", min: 0, max: opts.length - 1, step: 1 });
  input.value = Math.max(0, opts.findIndex(([v]) => v === st.params[p.key]));
  input.setAttribute("aria-label", `${r.label}: ${PARAM_LABEL[p.key] ?? p.key}`);
  const label = el("span", "pk-label");
  const show = () => {
    label.textContent = PARAM_LABEL[p.key] ?? p.key;
    wrap.title = `${PARAM_LABEL[p.key] ?? p.key}: ${opts[Number(input.value)][1]}`;
  };
  wrap.append(input, label);
  makeKnob(input, { numbers: false });
  show();
  input.addEventListener("input", () => {
    st.params[p.key] = opts[Number(input.value)][0];
    show();
    onTurn();
  });
  return wrap;
}

// Each rule is a pedal on the board (looks: pedals.js). Stomp the switch, or
// click the pedal, to turn its rule on; the LED lights. Turn a knob to change
// the rule's setting. The rule in plain English is printed under the pedal.
let saveTimer = 0;
function renderRules() {
  const list = $("ruleList");
  const focused = document.activeElement?.closest?.("[data-rule]")?.dataset.rule;
  list.innerHTML = "";
  for (const r of RULES) {
    const st = ruleState[r.rule];
    const d = PEDAL_DESIGNS[r.rule] ?? PEDAL_DESIGNS.startNear;
    const slot = el("div", `slot t-${d.type}`);
    slot.dataset.rule = r.rule;
    // Real boards are never perfectly square: tilt each pedal and its tape label a little.
    const seed = [...r.rule].reduce((h, ch) => (h * 31 + ch.charCodeAt(0)) % 997, 7);
    slot.style.setProperty("--tilt", `${((seed % 7) - 3) * 0.45}deg`);
    slot.style.setProperty("--tape-tilt", `${((seed % 5) - 2) * 0.8}deg`);
    const pedal = el("div", `pedal t-${d.type} f-${d.finish} k-${d.knob}${d.frame ? " framed" : ""}${st.on ? " on" : ""}`);
    pedal.style.setProperty("--c", d.c);
    pedal.style.setProperty("--print", d.print);
    pedal.style.setProperty("--font", d.font);
    pedal.style.setProperty("--size", `${d.size}px`);
    pedal.style.setProperty("--weight", d.weight ?? 400);
    pedal.style.setProperty("--style", d.style ?? "normal");
    const caption = el("p", "pedal-cap", describeRule(st.params));
    const knobs = el("div", `pk-row n${r.params.length}`);
    for (const p of r.params) {
      knobs.append(paramControl(r, p, () => {
        caption.textContent = describeRule(st.params);
        clearTimeout(saveTimer);
        saveTimer = setTimeout(rulesChanged, 250);
      }));
    }
    const toggle = () => {
      st.on = !st.on;
      renderRules();
      rulesChanged();
    };
    // The switch: a metal stomp switch, or on a treadle pedal the rubber plate.
    const sw = el("button", d.type === "treadle" ? "footswitch treadle" : "footswitch");
    sw.type = "button";
    sw.setAttribute("aria-pressed", String(st.on));
    sw.setAttribute("aria-label", `${r.label}: ${st.on ? "on" : "off"}`);
    if (d.type === "treadle") sw.append(el("span", "treadle-logo", "S&C"));
    sw.addEventListener("click", (e) => { e.stopPropagation(); toggle(); });
    pedal.addEventListener("click", (e) => { if (!e.target.closest(".pk")) toggle(); });
    const name = el("span", "pedal-name", r.label);
    const model = el("span", "pedal-model", d.model);
    const led = el("span", "led");
    if (d.type === "treadle") {
      const top = el("div", "panel-top");
      top.append(el("span", "io", "◂ output"), led, el("span", "io", "input ◂"));
      const label = el("div", "name-band");
      label.append(name, model);
      pedal.append(top, knobs, label, sw);
    } else {
      pedal.append(knobs, led, name, model, el("span", "bypass", "true bypass"), sw, el("span", "maker", "Sound & Complete"));
    }
    pedal.prepend(el("span", "jack in"), el("span", "jack out"));
    if (d.art && ART[d.art]) {
      // Printed artwork (our own static SVG strings from pedals.js).
      const art = el("span", "art");
      art.innerHTML = `<svg viewBox="0 0 64 64" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${ART[d.art]}</svg>`;
      pedal.prepend(art);
    }
    slot.append(pedal, caption);
    list.append(slot);
  }
  if (focused) list.querySelector(`[data-rule="${focused}"] .footswitch`)?.focus();
}

let conflictSeq = 0;
async function rulesChanged() {
  savePrefs({ rules: ruleState });
  const seq = ++conflictSeq;
  const badge = $("conflict");
  try {
    const { possible } = await post("/api/possible", { rules: activeRules() });
    if (seq !== conflictSeq) return;
    badge.classList.remove("hidden", "bad");
    const impossible = possible.map((ok, i) => (ok ? null : i + 1)).filter(Boolean);
    const conflict = impossible.length > 0;
    if (conflict) {
      badge.classList.add("bad");
      badge.textContent = impossible.length === 3
        ? "Proven impossible: no answer could keep all of these"
        : `Proven impossible for answer ${impossible.join(" and ")}`;
      badge.title = "Lean proved that no call, by anyone, can be answered while keeping all of these rules"
        + (impossible.length === 3 ? "." : ` at answer ${impossible.join(" and ")} of the song.`);
    } else {
      const n = activeRules().length;
      badge.textContent = n ? `${n} of ${RULES.length} on` : "All off: free play";
      badge.title = "";
    }
    $("start").disabled = conflict;
  } catch (e) {
    badge.classList.remove("hidden");
    badge.className = "status bad";
    badge.textContent = `Can't reach the Lean server: ${e.message}`;
  }
}

// ---------------------------------------------------------------------------
// Mic

async function enableMic() {
  await ensureAudio();
  if (!S.input) {
    S.input = new GuitarInput(S.ctx);
    await S.input.init();
  }
  try {
    const sel = $("device");
    const prefs = loadPrefs();
    // Use the input the player picked from the list, if any.
    let chosen = sel.value || (prefs.deviceManual ? prefs.deviceId : undefined) || undefined;
    let label = await S.input.enableMic(chosen);
    // Device names are only visible after mic permission. Now list them, and if
    // the player has not picked one, prefer a guitar audio interface, then the
    // DJI wireless mic, over the laptop's built-in mic.
    const devices = await S.input.listDevices();
    const iface = devices.find((d) => /irig|scarlett|focusrite|audient|\bid\d|motu|presonus|steinberg|\bur\d|umc|behringer|apollo|universal audio|ssl \d|arturia|minifuse|guitar|instrument|line 6|helix|boss|katana|zoom|tascam|roland/i.test(d.label));
    const dji = devices.find((d) => /dji|wireless mic|mic rx|mic 3/i.test(d.label));
    const auto = iface || dji;
    if (!sel.value && !prefs.deviceManual && auto && auto.deviceId !== S.input.stream.getAudioTracks()[0]?.getSettings?.().deviceId) {
      chosen = auto.deviceId;
      label = await S.input.enableMic(chosen);
    }
    sel.innerHTML = "";
    for (const d of devices) {
      const o = el("option", "", d.label || "Microphone");
      o.value = d.deviceId;
      sel.append(o);
    }
    const active = S.input.stream.getAudioTracks()[0]?.getSettings?.().deviceId;
    sel.value = active || chosen || sel.value;
    savePrefs({ deviceId: sel.value });
    S.micReady = true;
    $("micInfo").innerHTML = "";
    $("micInfo").append(`Listening on ${label}.`);
    if (!S.input.calibrated) {
      const a = el("a", "", "Calibrate timing");
      a.href = "lab.html";
      $("micInfo").append(" ", a, " once for best results.");
    }
    // A Bluetooth headset as the Mac's default mic drops the headphones into
    // 16 kHz "phone call" mode: the band sounds awful and timing gets worse.
    const def = devices.find((d) => d.deviceId === "default");
    if (def && /bose|qc ?\d|airpods|beats|headset|buds|wh-|wf-|jabra|bluetooth/i.test(def.label)) {
      $("micInfo").innerHTML = `<b>Fix your headphones first.</b> Your Mac's default microphone is “${def.label.replace(/^Default - /, "")}”. ` +
        `That puts the headphones in phone-call mode (muffled, low quality). Open System Settings → Sound → Input and pick “${label}”, ` +
        `then switch the headphones off and on again.`;
      $("micInfo").classList.add("warn");
    } else {
      $("micInfo").classList.remove("warn");
    }
    $("enableMic").textContent = "Mic on";
    $("pilot").classList.add("on");
    if (!S.meterOn) { S.meterOn = true; meterLoop(); }
    S.lostInput = null;
    // Play the guitar out loud through the amp. Only for an audio interface:
    // with a microphone, the speakers would feed back into it and howl.
    S.amp.attach(S.input.source);
    S.ampAllowed = IFACE_RE.test(label);
    S.amp.set(ampSettings());
    if (!S.ampAllowed) $("micInfo").append(" The amp stays silent on a microphone so it can't feed back.");
    // If the input is unplugged (or its USB connection drops), say so plainly,
    // and reconnect by itself when it comes back (see watchInputs).
    const track = S.input.stream.getAudioTracks()[0];
    if (track) track.onended = () => inputLost(label);
  } catch (e) {
    $("micInfo").textContent = `Mic error: ${e.message}`;
  }
}

/** The input disappeared: the cable came out, or the Mac lost the USB device. */
function inputLost(label) {
  S.micReady = false;
  S.lostInput = label;
  $("pilot").classList.remove("on");
  $("enableMic").textContent = "Enable mic";
  $("micInfo").classList.add("warn");
  $("micInfo").innerHTML = "";
  $("micInfo").append(el("b", "", `${label} was disconnected.`),
    " Check its cable (and any adapter or hub). It reconnects by itself when your Mac sees it again.");
}

/** When devices change, reconnect a lost input as soon as it is back. */
async function watchInputs() {
  if (!S.lostInput || !S.input) return;
  const back = (await S.input.listDevices()).find((d) => d.label === S.lostInput);
  if (!back) return;
  const sel = $("device");
  if (![...sel.options].some((o) => o.value === back.deviceId)) sel.append(Object.assign(el("option", "", back.label), { value: back.deviceId }));
  sel.value = back.deviceId;
  await enableMic();
}
navigator.mediaDevices?.addEventListener?.("devicechange", () => watchInputs().catch(() => {}));

/** Names of guitar audio interfaces (a direct line in, so the amp can't feed back). */
const IFACE_RE = /irig|scarlett|focusrite|audient|\bid\d|motu|presonus|steinberg|\bur\d|umc|behringer|apollo|universal audio|ssl \d|arturia|minifuse|guitar|instrument|line 6|helix|boss|katana|zoom|tascam|roland/i;

/** The amp knobs (0..100) as amp settings (0..1). */
function ampSettings() {
  return {
    drive: Number($("ampDrive").value) / 100,
    tone: Number($("ampTone").value) / 100,
    volume: Number($("ampVol").value) / 100,
    reverb: Number($("ampVerb").value) / 100,
    on: Boolean(S.ampAllowed),
  };
}

let tunerFreq = 0;
function meterLoop() {
  const db = Math.max(-70, S.input?.level ?? -70);
  $("meterFill").style.width = `${((db + 70) / 70) * 100}%`;
  // Tuner: against A440 (not the learned offset), smoothed a little.
  const st = S.input?.detector?.state;
  if (st && st.freq > 0 && st.clarity >= 0.9 && st.rmsDb > -55) {
    tunerFreq = tunerFreq > 0 && Math.abs(Math.log2(st.freq / tunerFreq)) < 0.05 ? tunerFreq * 0.7 + st.freq * 0.3 : st.freq;
    const f = 69 + 12 * Math.log2(tunerFreq / 440);
    const m = Math.round(f);
    const cents = Math.round((f - m) * 100);
    $("tunerNote").textContent = midiName(m).replace(/\d+$/, "");
    $("tunerNeedle").style.left = `${50 + cents}%`;
    $("tunerCents").textContent = Math.abs(cents) <= 5 ? "In tune" : `${Math.abs(cents)}¢ ${cents > 0 ? "sharp" : "flat"}`;
    $("tuner").classList.toggle("ok", Math.abs(cents) <= 5);
  }
  requestAnimationFrame(meterLoop);
}

// ---------------------------------------------------------------------------
// Grids

function renderGrid(container, phrase, { you = false, now = -1, upTo = 24, levels = null } = {}) {
  container.innerHTML = "";
  for (let i = 0; i < PHRASE_SLOTS; i++) {
    const c = el("div", "cell");
    if (i % 3 === 0) c.classList.add("beat");
    if (levels && i < upTo) {
      c.classList.add("past");
      if (levels[i] > 0.02) {
        const bar = el("span", "lvl");
        bar.style.height = `${Math.round(Math.min(1, levels[i]) * 100)}%`;
        c.append(bar);
      }
    }
    const m = phrase?.[i];
    if (m != null && i < upTo) {
      c.classList.add("note");
      if (you) c.classList.add("you");
      c.textContent = midiName(m).replace(/\d+$/, "");
      c.title = midiName(m);
    }
    if (i === now) c.classList.add("now");
    container.append(c);
  }
}

function miniGrid(phrase, you) {
  const g = el("div", "grid small");
  renderGrid(g, phrase, { you });
  return g;
}

// ---------------------------------------------------------------------------
// Prep: LLM proposes, Lean gate chooses

async function prepare() {
  const rules = activeRules();
  show("prep");
  $("go").classList.add("hidden");
  $("prepList").innerHTML = "";
  $("prepMsg").textContent = "Writing your calls";
  $("prepSource").textContent = "";
  let session;
  try {
    session = await post("/api/session", { rules });
  } catch (e) {
    $("prepMsg").textContent = `Could not get calls: ${e.message}`;
    return;
  }
  S.session = session;
  $("prepMsg").textContent = "Your calls are ready";
  // Proof first: if some exchange can't be answered by any call, say so and stop.
  if (session.exchanges.some((x) => !x.possible)) {
    $("prepMsg").textContent = "These rules can't be kept";
    $("prepSource").textContent = "Lean proved that no call, by Claude or anyone, has an answer that keeps all of these rules where marked. Turn a rule off or loosen one, then try again.";
    for (const x of session.exchanges) {
      const item = el("div", "prep-item");
      const left = el("div");
      left.append(el("div", "what", `Answer ${x.exchange + 1}`));
      left.append(x.possible
        ? el("div", "note check", "Possible")
        : el("div", "note bad", "Proven impossible: no call can be answered here"));
      item.append(left);
      $("prepList").append(item);
    }
    return;
  }
  const fromProof = session.exchanges.filter((x) => x.source === "proof").length;
  $("prepSource").textContent = !session.llm
    ? "No Claude API key is set, so each call is the one Lean's proof found."
    : session.llmError ? "Claude couldn't be reached, so each call is the one Lean's proof found."
    : fromProof ? "Claude wrote these calls, except where marked." : "Claude wrote these calls.";
  for (const x of session.exchanges) {
    const item = el("div", "prep-item");
    const left = el("div");
    left.append(el("div", "what", `Call ${x.exchange + 1}${x.exchange === 2 ? ": turnaround" : ""}`));
    left.append(el("div", "note check", "Lean found an answer"));
    if (x.claudeRejected) left.append(el("div", "note", `Lean turned down ${x.claudeRejected} of Claude's calls: they had no answer`));
    if (x.source === "proof" && session.llm && !session.llmError) left.append(el("div", "note", "This call comes from Lean's proof"));
    item.append(left, miniGrid(x.call));
    $("prepList").append(item);
  }
  $("go").classList.remove("hidden");
}

// ---------------------------------------------------------------------------
// The orb

const pulse = (x) => Math.exp(-4 * Math.max(0, x));

/** 0..1 loudness for a phrase at fractional slot position `pos`. */
function noteLevel(phrase, pos) {
  let best = 0;
  for (let i = 0; i < PHRASE_SLOTS; i++) {
    if (phrase?.[i] == null || i > pos) continue;
    best = Math.max(best, pulse((pos - i) / 2.5));
  }
  return best;
}

function setOrb(state, level) {
  const orb = $("stageOrb");
  if (!orb) return;
  if (!orb.classList.contains(state)) orb.className = `light ${state}`;
  orb.style.setProperty("--level", level.toFixed(3));
}

// ---------------------------------------------------------------------------
// The song

function stopSong() {
  S.playing = false;
  S.band?.stop();
  for (const t of S.timers) clearTimeout(t);
  S.timers = [];
  cancelAnimationFrame(S.raf);
}

// The neck: shows the AI's notes as it plays them. On by default; the switch
// under the stage hides it, and the choice is remembered.
const fretOn = () => $("showFret").checked;
$("showFret").checked = prefs.showFret ?? true;
$("fretboard").classList.toggle("hidden", !fretOn());
$("showFret").addEventListener("change", () => {
  $("fretboard").classList.toggle("hidden", !fretOn());
  savePrefs({ showFret: fretOn() });
});

/** Empty play screen: blank lanes, no bar, no chord, no message. */
function clearStage() {
  renderFretboard($("fretboard"), null);
  renderGrid($("gridCall"), null);
  renderGrid($("gridYou"), null);
  $("laneNote").textContent = "";
  $("barNum").textContent = "-";
  $("chordName").textContent = "Am7";
  $("who").textContent = "Count in";
  $("who").className = "who";
  for (const b of $("barStrip").children) b.classList.remove("now");
}

async function playSong() {
  await ensureAudio();
  const isDemo = mode() === "demo";
  if (!isDemo && !S.micReady) {
    show("setup");
    $("startMsg").textContent = "Enable the mic first, or choose the demo.";
    return;
  }
  stopSong();
  clearStage(); // don't show the last song's notes and loudness while counting in
  show("play");
  S.playing = true;
  S.played = [null, null, null];
  const tempo = bpm();
  const slotDur = 60 / tempo / 3;
  const barDur = 4 * 60 / tempo;
  const { songStart } = S.band.scheduleSong({ startTime: S.ctx.currentTime + 0.4, bpm: tempo, bars: 12, countInBars: 1 });
  const ex = S.session.exchanges;

  // Bar strip and rule chips.
  const strip = $("barStrip");
  strip.innerHTML = "";
  for (let b = 1; b <= 12; b++) {
    const role = EXCHANGES.find((e) => e.callBars.includes(b)) ? "call" : "answer";
    const d = el("div", `bar ${role}`, `${b} ${CHORDS[b - 1]}`);
    strip.append(d);
  }
  $("playRules").innerHTML = "";
  for (const r of activeRules()) $("playRules").append(el("li", "", describeRule(r)));

  // Debug: record the mic and every onset during the song (mic mode only).
  S.debug = null;
  if (!isDemo) {
    S.input.startRecording();
    S.debug = { songStart, bpm: tempo, latency: S.input.latency, calibrated: S.input.calibrated,
      outputLatency: S.ctx.outputLatency || 0, baseLatency: S.ctx.baseLatency || 0,
      sampleRate: S.ctx.sampleRate, device: $("device").selectedOptions[0]?.textContent ?? "",
      all: S.input.collect(songStart - 4 * 60 / tempo, songStart + 12 * barDur + 2), windows: [] };
  }

  // Calls, answers and listening windows.
  const windows = [];
  for (const e of EXCHANGES) {
    const callStart = songStart + 4 * e.exchange * barDur;
    const answerStart = callStart + 2 * barDur;
    const answerEnd = answerStart + 2 * barDur;
    S.band.playPhrase(ex[e.exchange].call, callStart, tempo);
    const w = { e: e.exchange, callStart, answerStart, answerEnd, live: new Array(24).fill(null), levels: new Array(24).fill(0) };
    if (isDemo) {
      S.band.playPhrase(ex[e.exchange].hint, answerStart, tempo, { gain: 0.9 });
      w.live = ex[e.exchange].hint.slice();
    } else {
      const lat = S.input.latency;
      w.collector = S.input.collect(answerStart - slotDur / 2 + lat, answerEnd + lat + 0.4);
    }
    windows.push(w);
  }

  // Finish each answer window: snap the heard notes to the grid.
  S.answersDone = [];
  for (const w of windows) {
    const finish = async () => {
      if (isDemo) {
        S.played[w.e] = ex[w.e].hint;
        return;
      }
      w.collector.stop();
      const opts = { phraseStart: w.answerStart, bpm: tempo, latency: S.input.latency };
      const live = quantize(w.collector.events, opts);
      // Read the answer again from the recorded audio, with every note heard in
      // full (more accurate than the live reading). Fall back to the live one.
      let r = live, method = "live";
      try {
        const lat = S.input.latency;
        const ev = await S.input.analyze(w.answerStart - 1.0 + lat, w.answerEnd + lat + 0.6);
        if (ev) {
          r = quantize(ev.filter((e) => e.time >= w.answerStart - slotDur / 2 + lat && e.time <= w.answerEnd + lat + 0.4), opts);
          method = "recording";
        }
      } catch (err) {
        console.warn("after-the-answer analysis failed, using the live reading:", err);
      }
      S.played[w.e] = r.phrase;
      S.debug?.windows.push({ exchange: w.e, answerStart: w.answerStart, call: ex[w.e].call, quantized: r, live, method });
    };
    let done;
    S.answersDone.push(new Promise((r) => (done = r)));
    S.timers.push(setTimeout(() => finish().finally(done), (w.answerEnd + 0.6 - S.ctx.currentTime) * 1000));
  }
  const songEnd = songStart + 12 * barDur;
  S.timers.push(setTimeout(() => finishSong(), (songEnd + 0.9 - S.ctx.currentTime) * 1000));

  // Animation.
  const draw = () => {
    if (!S.playing) return;
    const t = S.ctx.currentTime;
    const rel = t - songStart;
    const bar = Math.floor(rel / barDur) + 1;
    const bars = strip.children;
    for (let i = 0; i < bars.length; i++) bars[i].classList.toggle("now", i + 1 === bar);
    if (rel < 0) {
      $("barNum").textContent = "-";
      $("chordName").textContent = "Am7";
      const beat = Math.floor((rel + barDur) / (barDur / 4)) + 1;
      $("who").textContent = `${Math.max(1, Math.min(4, beat))}`;
      $("who").className = "who";
      $("laneNote").textContent = "";
      renderGrid($("gridCall"), null);
      renderGrid($("gridYou"), null);
      setOrb("idle", 0.5 * pulse(((rel + barDur) % (barDur / 4)) / (barDur / 4)));
    } else if (bar <= 12) {
      $("barNum").textContent = bar;
      $("chordName").textContent = CHORDS[bar - 1];
      const e = Math.floor((bar - 1) / 4);
      const w = windows[e];
      const inCall = (bar - 1) % 4 < 2;
      $("who").textContent = inCall ? "The band plays" : isDemo ? "The computer answers" : "Your turn";
      $("who").className = `who ${inCall ? "listen" : "you"}`;
      // The orb breathes with the music: the call's notes, then your playing.
      let level;
      if (inCall) level = noteLevel(ex[e].call, (t - w.callStart) / slotDur);
      else if (isDemo) level = noteLevel(w.live, (t - w.answerStart) / slotDur);
      else level = Math.max(0, Math.min(1, ((S.input.level ?? -80) + 55) / 40));
      // Listening lane: remember how loud you played in each slot.
      if (!isDemo && !inCall) {
        const k = Math.floor((t - w.answerStart - S.input.latency) / slotDur);
        if (k >= 0 && k < PHRASE_SLOTS) w.levels[k] = Math.max(w.levels[k], level);
      }
      setOrb(inCall ? "listen" : "you", level);
      const slotInCall = Math.floor((t - w.callStart) / slotDur);
      const slotInAnswer = Math.floor((t - w.answerStart) / slotDur);
      renderGrid($("gridCall"), ex[e].call, { now: inCall ? slotInCall : -1, upTo: inCall ? slotInCall + 1 : 24 });
      // The neck shows the AI's notes as they sound: the call, and in the demo
      // the computer's answer too. On your turn the whole call stays up, unlit.
      if (fretOn()) {
        if (inCall) renderFretboard($("fretboard"), ex[e].call, { upTo: slotInCall + 1, now: slotInCall });
        else if (isDemo) renderFretboard($("fretboard"), w.live, { upTo: slotInAnswer + 1, now: slotInAnswer });
        else renderFretboard($("fretboard"), ex[e].call, { upTo: 24, now: -1 });
      }
      // While you play, the "You" lane shows how loud you played in each slot,
      // not note names: notes are read in full when the answer ends and shown
      // on the report card. Demo mode shows the computer's notes.
      if (isDemo) {
        renderGrid($("gridYou"), inCall ? null : w.live, { you: true, now: inCall ? -1 : slotInAnswer, upTo: inCall ? 0 : slotInAnswer + 1 });
        $("laneNote").textContent = inCall ? "" : "The computer plays an answer that keeps every rule.";
      } else {
        renderGrid($("gridYou"), null, { now: inCall ? -1 : slotInAnswer, upTo: inCall ? 0 : slotInAnswer + 1, levels: inCall ? null : w.levels });
        $("laneNote").textContent = inCall
          ? "Answer in the next two bars."
          : "Listening. Your notes show up on the report card.";
      }
    }
    S.raf = requestAnimationFrame(draw);
  };
  S.raf = requestAnimationFrame(draw);
}

async function finishSong() {
  if (!S.playing) return;
  S.playing = false;
  cancelAnimationFrame(S.raf);
  $("who").textContent = "Reading your answers…";
  await Promise.all(S.answersDone ?? []); // the last answer may still be being analysed
  const rules = activeRules();
  const exchanges = S.session.exchanges.map((x, i) => ({ call: x.call, played: S.played[i] ?? new Array(24).fill(null) }));
  let results;
  try {
    ({ results } = await post("/api/grade", { rules, exchanges }));
  } catch (e) {
    alert(`Grading failed: ${e.message}`);
    show("setup");
    return;
  }
  renderReport(rules, exchanges, results);
  show("report");
  uploadDebug(rules, results);
}

/** Save this song's mic audio and detected notes on the server (web/debug/),
 * so detection problems can be measured. Local only. */
async function uploadDebug(rules, results) {
  if (!S.debug) return;
  const d = S.debug;
  S.debug = null;
  d.all.stop();
  const rec = S.input.stopRecording();
  const meta = { ...d, all: d.all.events, rules, results, recording: rec && { sampleRate: rec.sampleRate, startFrame: rec.startFrame, startTime: rec.startFrame / rec.sampleRate, length: rec.samples.length } };
  try {
    const { id } = await post("/api/debug/meta", meta);
    if (rec) {
      const pcm = new Int16Array(rec.samples.length);
      for (let i = 0; i < pcm.length; i++) pcm[i] = Math.max(-1, Math.min(1, rec.samples[i])) * 32767;
      await fetch(`/api/debug/audio?id=${id}&rate=${rec.sampleRate}`, { method: "POST", body: pcm.buffer });
    }
  } catch (e) {
    console.warn("debug upload failed", e);
  }
}

// ---------------------------------------------------------------------------
// Report card

function renderReport(rules, exchanges, results) {
  const list = $("reportList");
  list.innerHTML = "";
  let pass = 0;
  let total = 0;
  exchanges.forEach((x, i) => {
    const box = el("div", "ex");
    const h = el("h3", "", `Answer ${i + 1} `);
    h.append(el("span", "", `${i === 2 ? "turnaround, " : ""}bars ${EXCHANGES[i].answerBars.join("–")}`));
    box.append(h);
    const r1 = el("div", "lane");
    r1.append(el("span", "lane-label", "Band"), miniGrid(x.call));
    const r2 = el("div", "lane");
    r2.append(el("span", "lane-label", "You"), miniGrid(x.played, true));
    const heard = x.played.some((m) => m != null);
    box.append(r1, r2);
    if (!heard) box.append(el("p", "lane-note", "No notes heard in these two bars."));
    const ul = el("ul", "results");
    (results[i] ?? []).forEach((ok, k) => {
      pass += ok ? 1 : 0;
      total += 1;
      const li = el("li", ok ? "pass" : "fail");
      li.append(el("span", "mark", ok ? "✓" : "✗"), el("span", "", describeRule(rules[k])));
      ul.append(li);
    });
    if (!rules.length) ul.append(el("li", "", "No rules: free play."));
    box.append(ul);
    const tools = el("div", "tools");
    const hear = (label, phrase) => {
      const b = el("button", "play-link", label);
      b.addEventListener("click", async () => {
        await ensureAudio();
        S.band.stop();
        S.band.playPhrase(phrase, S.ctx.currentTime + 0.1, bpm());
      });
      return b;
    };
    tools.append(hear("▶ The call", x.call), hear("▶ What you played", x.played), hear("▶ An answer that keeps every rule", S.session.exchanges[i].hint));
    box.append(tools);
    list.append(box);
  });
  $("score").textContent = total ? `${pass} of ${total}` : "";
}

// ---------------------------------------------------------------------------
// Wiring

function init() {
  renderRules();
  rulesChanged();
  if (prefs.bpm) $("bpm").value = prefs.bpm;
  $("bpmVal").textContent = $("bpm").value;
  $("bpm").addEventListener("input", () => {
    $("bpmVal").textContent = $("bpm").value;
    savePrefs({ bpm: bpm() });
  });
  if (prefs.bandVol !== undefined) $("bandVol").value = prefs.bandVol;
  $("bandVolVal").textContent = $("bandVol").value;
  $("bandVol").addEventListener("input", () => {
    $("bandVolVal").textContent = $("bandVol").value;
    savePrefs({ bandVol: Number($("bandVol").value) });
    if (S.band) S.band.volume = Number($("bandVol").value) / 100;
  });
  if (prefs.mode) document.querySelector(`input[name=mode][value=${prefs.mode}]`).checked = true;
  const syncMode = () => {
    $("micBox").classList.toggle("hidden", mode() !== "mic");
    savePrefs({ mode: mode() });
  };
  for (const r of document.querySelectorAll("input[name=mode]")) r.addEventListener("change", syncMode);
  makeKnob($("bpm"));
  makeKnob($("bandVol"));
  for (const id of ["ampDrive", "ampTone", "ampVerb", "ampVol"]) {
    if (prefs[id] !== undefined) $(id).value = prefs[id];
    const show = () => { $(`${id}Val`).textContent = String(Math.round(Number($(id).value)) / 10); };
    show();
    $(id).addEventListener("input", () => {
      show();
      savePrefs({ [id]: Number($(id).value) });
      S.amp?.set(ampSettings());
    });
    makeKnob($(id));
  }
  syncMode();
  $("enableMic").addEventListener("click", enableMic);
  $("device").addEventListener("change", () => {
    savePrefs({ deviceManual: true }); // the player picked this input: keep it
    if (S.micReady) enableMic();
  });
  $("start").addEventListener("click", async () => {
    $("startMsg").textContent = "";
    if (mode() === "mic" && !S.micReady) {
      $("startMsg").textContent = "Enable the mic first, or choose the demo.";
      return;
    }
    await ensureAudio();
    prepare();
  });
  $("go").addEventListener("click", playSong);
  $("stop").addEventListener("click", () => { stopSong(); show("setup"); });
  $("again").addEventListener("click", () => { stopSong(); prepare(); });
  $("change").addEventListener("click", () => { stopSong(); show("setup"); });
}

init();
