// app.js: UI + audio graph wiring for the guitar-input prototype.
//
// Audio graph:
//
//   mic (MediaStreamSource) --\
//                              >-- inputBus (gain) --> capture worklet --> silent --> destination
//   simulate (BufferSource) --/                               |
//                                                             '--> port messages {frame, samples}
//                                                                  --> OnsetDetector (onsets.js)
//                                                                  --> onset events
//   metronome clicks ---------------------------------------------------> destination
//
// All times are AudioContext times (seconds). Onset times come from the
// worklet's frame counter, click times are what we scheduled, so comparing
// them is exact apart from real-world input/output latency, which the
// calibration step measures.

import { quantize, slotDuration, phraseDuration, PHRASE_SLOTS, isValidPhrase } from "./audio/quantize.js";
import { loadPitchDetector, makePitchEstimator, midiToName, dbToLin, PITCHY_URL } from "./audio/pitch.js";
import { OnsetDetector, DEFAULT_ONSET_PARAMS, pitchWindowSize } from "./audio/onsets.js";
import { Metronome } from "./audio/metronome.js";
import { renderNotes, parsePattern } from "./audio/synth.js";

const $ = (id) => document.getElementById(id);

// ---------------------------------------------------------------------------
// Settings (persisted per browser; storage may be unavailable -> defaults)

const STORE_KEY = "sound-and-complete.guitar-input.v1";
function loadStore() {
  try {
    return JSON.parse(localStorage.getItem(STORE_KEY) || "{}") || {};
  } catch {
    return {};
  }
}
/** Save the mic latency, both as the current value and for this input by name,
 * so each input (wireless mic, audio interface...) keeps its own calibration. */
function saveMicLatency(ms) {
  const label = S.stream?.getAudioTracks()[0]?.label;
  const byDevice = { ...(loadStore().latencyByDevice || {}) };
  if (label) byDevice[label] = ms;
  saveStore({ latencyMicMs: ms, latencyByDevice: byDevice });
}

function saveStore(patch) {
  try {
    localStorage.setItem(STORE_KEY, JSON.stringify({ ...loadStore(), ...patch }));
  } catch {
    /* private mode / blocked storage: ignore */
  }
}

const stored = loadStore();
const onsetParams = { ...DEFAULT_ONSET_PARAMS };
const pitchParams = { clarityThreshold: 0.9, minRms: dbToLin(DEFAULT_ONSET_PARAMS.gateDb - 6) };

const S = {
  ctx: null,
  inputBus: null,
  simBus: null,
  simMonitor: null,
  worklet: null,
  micSource: null,
  stream: null,
  detector: null,
  pitchSource: "",
  metronome: null,
  collectors: new Set(), // callbacks receiving every onset event
  busy: false, // recording or calibrating
  // Latency is kept separately for the real mic (persisted) and simulate mode.
  latencyMs: { mic: Number(stored.latencyMicMs) || 0, sim: 0 },
  lastResult: null,
};

const isSim = () => $("simulate").checked;
const activeLatencyKey = () => (isSim() ? "sim" : "mic");

// ---------------------------------------------------------------------------
// Status + log helpers

function status(msg, kind = "") {
  const el = $("status");
  el.innerHTML = msg;
  el.className = "status " + kind;
}

const logLines = [];
function log(text, cls = "") {
  const el = $("log");
  const div = document.createElement("div");
  div.textContent = text;
  if (cls) div.className = cls;
  el.prepend(div);
  logLines.push(div);
  if (logLines.length > 200) logLines.shift().remove();
}

// ---------------------------------------------------------------------------
// Audio setup

async function ensureAudio() {
  if (S.ctx) {
    if (S.ctx.state !== "running") await S.ctx.resume();
    return;
  }
  const ctx = new AudioContext({ latencyHint: "interactive", sampleRate: 48000 });
  await ctx.resume();
  await ctx.audioWorklet.addModule("audio/capture-worklet.js");

  const inputBus = ctx.createGain();
  inputBus.gain.value = dbToLin(Number($("inputGain").value));

  // Mono analysis: stereo inputs are averaged (L+R)/2 by the explicit downmix.
  const worklet = new AudioWorkletNode(ctx, "capture-processor", {
    numberOfInputs: 1,
    numberOfOutputs: 1,
    channelCount: 1,
    channelCountMode: "explicit",
    channelInterpretation: "speakers",
  });
  const silent = ctx.createGain();
  silent.gain.value = 0; // keep the worklet pulled by the graph, output nothing
  inputBus.connect(worklet).connect(silent).connect(ctx.destination);

  // Simulation path: buffers go into simBus -> inputBus (analysis) and to a
  // monitor gain so you can hear what is being analysed.
  const simBus = ctx.createGain();
  const simMonitor = ctx.createGain();
  simMonitor.gain.value = Number($("simMonitor").value);
  simBus.connect(simMonitor).connect(ctx.destination);

  const W = pitchWindowSize(ctx.sampleRate);
  const { detector: pd, source, error } = await loadPitchDetector(W);
  S.pitchSource = source;
  if (error) log(`pitchy failed to load from ${PITCHY_URL} (${error}); using built-in fallback detector`);
  const estimatePitch = makePitchEstimator(pd, ctx.sampleRate, pitchParams);
  const detector = new OnsetDetector({ sampleRate: ctx.sampleRate, estimatePitch, windowSize: W, params: onsetParams });

  worklet.port.onmessage = ({ data }) => {
    const events = detector.push(data.samples, data.frame);
    for (const ev of events) handleOnset(ev);
  };

  Object.assign(S, { ctx, inputBus, simBus, simMonitor, worklet, detector, metronome: new Metronome(ctx) });
  S.metronome.volume = Number($("clickVol").value);
  S.metronome.tripletClick = $("tripletClick").checked;
  applySimRouting();
  $("pitchSource").textContent = `${ctx.sampleRate} Hz · pitch: ${source} · base latency ${(ctx.baseLatency * 1000 || 0).toFixed(1)} ms`;
  requestAnimationFrame(drawLive);
}

async function enableMic(deviceId) {
  await ensureAudio();
  if (S.stream) S.stream.getTracks().forEach((t) => t.stop());
  if (S.micSource) S.micSource.disconnect();
  S.micSource = null;
  try {
    S.stream = await navigator.mediaDevices.getUserMedia({
      audio: {
        deviceId: deviceId ? { exact: deviceId } : undefined,
        // Browser "voice" processing destroys music: turn it all off.
        echoCancellation: false,
        noiseSuppression: false,
        autoGainControl: false,
      },
    });
  } catch (err) {
    status(`Mic error: ${err.name}: ${err.message}`, "err");
    throw err;
  }
  S.micSource = S.ctx.createMediaStreamSource(S.stream);
  applySimRouting();
  const track = S.stream.getAudioTracks()[0];
  const st = track.getSettings ? track.getSettings() : {};
  $("trackInfo").textContent =
    `Using: ${track.label || "default input"} · ` +
    `channels ${st.channelCount ?? "?"} · ` +
    `echoCancellation ${st.echoCancellation} · noiseSuppression ${st.noiseSuppression} · autoGainControl ${st.autoGainControl}`;
  await refreshDevices(st.deviceId);
  // First time: device names only appear after permission. If we opened the
  // default input but a guitar interface or DJI receiver is plugged in, switch to it.
  if (!deviceId) {
    const inputs = (await navigator.mediaDevices.enumerateDevices()).filter((d) => d.kind === "audioinput");
    const pick = preferredInput(inputs);
    if (pick && pick.deviceId !== st.deviceId) return enableMic(pick.deviceId);
  }
  status(`Mic on: <b>${track.label || "default"}</b>. Pluck a note and check the note display.`, "ok");
}

/** The input to use when the player has not picked one: a guitar audio
 * interface first, then the DJI wireless mic. Same rule as the main app. */
function preferredInput(inputs) {
  return inputs.find((d) => /irig|scarlett|focusrite|audient|\bid\d|motu|presonus|steinberg|\bur\d|umc|behringer|apollo|universal audio|ssl \d|arturia|minifuse|guitar|instrument|line 6|helix|boss|katana|zoom|tascam|roland/i.test(d.label))
    || inputs.find((d) => /dji|wireless mic|mic rx|mic 3/i.test(d.label));
}

async function refreshDevices(selectedId) {
  const devices = await navigator.mediaDevices.enumerateDevices();
  const inputs = devices.filter((d) => d.kind === "audioinput");
  const sel = $("deviceSelect");
  const keep = selectedId ?? sel.value;
  sel.innerHTML = "";
  inputs.forEach((d, i) => {
    const o = document.createElement("option");
    o.value = d.deviceId;
    o.textContent = d.label || `Input ${i + 1}`;
    sel.append(o);
  });
  if (keep && inputs.some((d) => d.deviceId === keep)) sel.value = keep;
  // Hint: preselect the DJI receiver if present and nothing chosen yet.
  if (!keep) {
    const pick = preferredInput(inputs);
    if (pick) sel.value = pick.deviceId;
  }
}

/** Route either the mic or the simulator into the analysis input. */
function applySimRouting() {
  if (!S.ctx) return;
  try { S.simBus.disconnect(S.inputBus); } catch { /* not connected */ }
  if (S.micSource) { try { S.micSource.disconnect(); } catch { /* ok */ } }
  if (isSim()) {
    S.simBus.connect(S.inputBus);
  } else if (S.micSource) {
    S.micSource.connect(S.inputBus);
  }
  S.detector.reset();
  updateLatencyUI();
}

// ---------------------------------------------------------------------------
// Live display

let flashUntil = 0;
let lastOnsetName = "-";

function handleOnset(ev) {
  const name = ev.midi === null ? "(no pitch)" : midiToName(ev.midi);
  const t = ev.time.toFixed(3);
  const extra = ev.midi === null ? "" : ` ${ev.freq.toFixed(1)} Hz clarity ${ev.clarity.toFixed(2)} votes ${ev.votes}`;
  log(`${t}s  ${ev.kind.padEnd(6)} ${name.padEnd(10)}${extra}`, ev.midi === null ? "unp" : ev.kind === "legato" ? "leg" : "");
  if (ev.midi !== null) {
    lastOnsetName = name;
    flashUntil = performance.now() + 250;
  }
  for (const c of S.collectors) c(ev);
}

function drawLive() {
  const st = S.detector.state;
  const db = Math.max(-80, st.rmsDb);
  $("meterFill").style.width = `${((db + 80) / 80) * 100}%`;
  $("gateMark").style.left = `${((onsetParams.gateDb + 80) / 80) * 100}%`;
  $("levelText").textContent = `${Number.isFinite(st.rmsDb) ? st.rmsDb.toFixed(1) : "-inf"} dBFS`;
  const noteEl = $("liveNote");
  if (st.midi !== null) {
    noteEl.textContent = midiToName(st.midi);
    $("liveFreq").textContent = `${st.freq.toFixed(1)} Hz · clarity ${st.clarity.toFixed(2)}`;
  } else {
    noteEl.textContent = lastOnsetName === "-" ? "-" : lastOnsetName;
    noteEl.style.opacity = "0.35";
  }
  if (st.midi !== null) noteEl.style.opacity = "1";
  noteEl.classList.toggle("flash", performance.now() < flashUntil);
  drawNowCursor();
  requestAnimationFrame(drawLive);
}

// ---------------------------------------------------------------------------
// Phrase grid rendering

function buildGrid() {
  const g = $("grid");
  g.innerHTML = "";
  for (let s = 0; s < PHRASE_SLOTS; s++) {
    const c = document.createElement("div");
    c.className = "cell" + (s % 3 === 0 ? " beat" : "");
    c.id = `cell${s}`;
    const bar = Math.floor(s / 12) + 1;
    const beat = Math.floor((s % 12) / 3) + 1;
    const lbl = s % 3 === 0 ? `${bar}.${beat}` : s % 3 === 1 ? "trip" : "let";
    c.innerHTML = `<span class="lbl">${s} ${lbl}</span><span class="nm">&nbsp;</span><span class="off">&nbsp;</span>`;
    g.append(c);
  }
}

function showResult(result) {
  const bySlot = new Map(result.notes.map((n) => [n.slot, n]));
  for (let s = 0; s < PHRASE_SLOTS; s++) {
    const c = $(`cell${s}`);
    const n = bySlot.get(s);
    c.classList.toggle("has", !!n);
    c.classList.toggle("offgrid", !!n && !n.onGrid);
    c.querySelector(".nm").textContent = n ? midiToName(n.midi) : " ";
    const off = c.querySelector(".off");
    off.textContent = n ? `${n.offsetMs > 0 ? "+" : ""}${Math.round(n.offsetMs)}` : " ";
    off.className = "off" + (n ? (n.offsetMs < 0 ? " early" : n.offsetMs > 0 ? " late" : "") : "");
  }
  $("jsonOut").textContent = JSON.stringify(result.phrase);
  const tb = $("notesTable").querySelector("tbody");
  tb.innerHTML = "";
  result.notes.forEach((n, i) => {
    const tr = document.createElement("tr");
    const beat = `${Math.floor(n.slot / 12) + 1}.${Math.floor((n.slot % 12) / 3) + 1}.${(n.slot % 3) + 1}`;
    for (const v of [i + 1, midiToName(n.midi), n.midi, n.slot, beat, n.offsetMs.toFixed(1), n.onGrid ? "yes" : "NO", n.kind ?? "", n.time.toFixed(4)]) {
      const td = document.createElement("td");
      td.textContent = v;
      tr.append(td);
    }
    tb.append(tr);
  });
  $("rejected").textContent = result.rejected.length
    ? "Ignored: " + result.rejected.map((r) => `${r.midi === null ? "unpitched" : midiToName(r.midi)}@slot ${r.slot ?? "?"} (${r.reason})`).join(", ")
    : "";
}

// Moving highlight of the current slot while recording.
let recordWindow = null; // {phraseStart, bpm}
function drawNowCursor() {
  document.querySelectorAll(".cell.now").forEach((c) => c.classList.remove("now"));
  if (!recordWindow || !S.ctx) return;
  const s = Math.floor((S.ctx.currentTime - recordWindow.phraseStart) / slotDuration(recordWindow.bpm));
  if (s >= 0 && s < PHRASE_SLOTS) $(`cell${s}`).classList.add("now");
}

// ---------------------------------------------------------------------------
// Simulation

/**
 * Schedule synthetic notes into the analysis input.
 * @param {{time:number, midi:number|null, legato?:boolean}[]} notes  absolute AudioContext times
 */
function scheduleSim(notes) {
  const ctx = S.ctx;
  if (!notes.length) return;
  const first = Math.min(...notes.map((n) => n.time));
  const last = Math.max(...notes.map((n) => n.time));
  const bufStart = Math.max(ctx.currentTime + 0.05, first - 0.1);
  const rel = notes.map((n) => ({ ...n, time: n.time - bufStart }));
  const data = renderNotes(ctx.sampleRate, rel, last - bufStart + 1.2, { noiseDb: -70, seed: (Math.random() * 1e9) | 0 });
  const buf = ctx.createBuffer(1, data.length, ctx.sampleRate);
  buf.copyToChannel(data, 0);
  const src = ctx.createBufferSource();
  src.buffer = buf;
  src.connect(S.simBus);
  src.start(bufStart);
}

/** Pattern -> absolute-time notes for a phrase starting at phraseStart. */
function simNotesForPhrase(phraseStart, bpm) {
  const pat = parsePattern($("simPattern").value);
  const jitter = Number($("simJitter").value) / 1000;
  const lat = Number($("simLatency").value) / 1000;
  const slot = slotDuration(bpm);
  return pat.map((p) => ({
    time: phraseStart + p.slot * slot + (Math.random() * 2 - 1) * jitter + lat,
    midi: p.midi,
    legato: p.legato,
  }));
}

function showSimExpected() {
  try {
    const ph = new Array(PHRASE_SLOTS).fill(null);
    for (const p of parsePattern($("simPattern").value)) if (p.slot < PHRASE_SLOTS && !ph[p.slot]) ph[p.slot] = p.midi;
    $("simExpected").textContent = "Expected phrase: " + JSON.stringify(ph);
  } catch (e) {
    $("simExpected").textContent = String(e.message);
  }
}

// ---------------------------------------------------------------------------
// Waiting helper: resolve when the AudioContext clock passes `t`.

function waitUntil(t) {
  return new Promise((resolve) => {
    const check = () => (S.ctx.currentTime >= t ? resolve() : setTimeout(check, 30));
    check();
  });
}

function setBusy(b) {
  S.busy = b;
  for (const id of ["record", "calibrate", "bpm", "simulate", "metroToggle"]) $(id).disabled = b;
}

// ---------------------------------------------------------------------------
// Record answer: 1 bar count-in, then 2 bars recorded.

async function recordAnswer() {
  await ensureAudio();
  if (!isSim() && !S.micSource) {
    status("Enable the mic first (or tick Simulate).", "err");
    return null;
  }
  if (S.busy) return null;
  setBusy(true);
  stopMetronomeUI();
  try {
    const bpm = clampBpm();
    const beat = 60 / bpm;
    const t0 = S.ctx.currentTime + 0.3;
    const phraseStart = t0 + 4 * beat;
    const phraseEnd = phraseStart + phraseDuration(bpm);
    const latency = S.latencyMs[activeLatencyKey()] / 1000;
    const toleranceMs = Number($("tolerance").value);
    const strict = $("strict").checked;

    const events = [];
    const collect = (ev) => {
      if (ev.time >= t0 && ev.time <= phraseEnd + latency + 0.5) events.push(ev);
    };
    S.collectors.add(collect);
    log(`--- recording: count-in at ${t0.toFixed(3)}, phrase ${phraseStart.toFixed(3)}..${phraseEnd.toFixed(3)} (latency ${(latency * 1000).toFixed(0)} ms)`);

    S.metronome.start(t0, {
      bpm,
      beats: 12,
      onBeat: (b) => {
        $("countIn").textContent = b < 4 ? `count ${b + 1}` : `bar ${Math.floor((b - 4) / 4) + 1} beat ${((b - 4) % 4) + 1}`;
      },
    });
    if (isSim()) scheduleSim(simNotesForPhrase(phraseStart, bpm));
    recordWindow = { phraseStart, bpm }; // visual cursor follows the clicks
    status("Recording... count in, then play your 2-bar answer.");

    // Wait past the end, plus time for the last onset's pitch decision (~0.1 s).
    await waitUntil(phraseEnd + latency + 0.5);
    S.collectors.delete(collect);
    recordWindow = null;
    $("countIn").innerHTML = "&nbsp;";

    const result = quantize(events, { phraseStart, bpm, latency, toleranceMs, strict });
    // Carry the onset kind (attack/legato) through for display/debugging.
    for (const n of result.notes) n.kind = events.find((e) => e.time === n.time)?.kind;
    if (!isValidPhrase(result.phrase)) throw new Error("internal error: phrase violates contract");
    S.lastResult = { ...result, bpm, phraseStart, latencyMs: latency * 1000 };
    showResult(result);
    status(`Recorded ${result.notes.length} note(s). ${result.rejected.length} onset(s) ignored.`, "ok");
    log(`--- phrase ${JSON.stringify(result.phrase)}`);
    window.dispatchEvent(new CustomEvent("guitar-phrase", { detail: S.lastResult }));
    return S.lastResult;
  } catch (err) {
    status(`Recording failed: ${err.message}`, "err");
    throw err;
  } finally {
    setBusy(false);
  }
}

// ---------------------------------------------------------------------------
// Latency calibration: 1 bar count-in, then pluck a muted string on 8 clicks.
// latency = median(onset time - click time). Unpitched onsets count here.

async function calibrate() {
  await ensureAudio();
  if (!isSim() && !S.micSource) {
    status("Enable the mic first (or tick Simulate).", "err");
    return;
  }
  if (S.busy) return;
  setBusy(true);
  stopMetronomeUI();
  try {
    const bpm = clampBpm();
    const beat = 60 / bpm;
    const t0 = S.ctx.currentTime + 0.3;
    const clicks = Array.from({ length: 8 }, (_, i) => t0 + (4 + i) * beat);
    const events = [];
    const collect = (ev) => events.push(ev);
    S.collectors.add(collect);
    const wasTriplet = S.metronome.tripletClick;
    S.metronome.tripletClick = false;
    S.metronome.start(t0, {
      bpm,
      beats: 12,
      onBeat: (b) => {
        $("countIn").textContent = b < 4 ? `count ${b + 1}` : `pluck ${b - 3}/8`;
      },
    });
    if (isSim()) {
      const lat = Number($("simLatency").value) / 1000;
      scheduleSim(clicks.map((c) => ({ time: c + lat + (Math.random() * 2 - 1) * 0.008, midi: null })));
    }
    status("Calibrating... mute the strings and pluck on each of the 8 clicks after the count-in.");
    await waitUntil(clicks[7] + 0.6);
    S.collectors.delete(collect);
    S.metronome.tripletClick = wasTriplet;
    $("countIn").innerHTML = "&nbsp;";

    // Match each click with the first unused onset in a window around it.
    const before = Math.min(0.1, beat * 0.3);
    const after = Math.min(0.45, beat * 0.65);
    const used = new Set();
    const offsets = [];
    for (const c of clicks) {
      const ev = events.find((e) => !used.has(e) && e.time >= c - before && e.time <= c + after);
      if (ev) {
        used.add(ev);
        offsets.push(ev.time - c);
      }
    }
    if (offsets.length < 5) {
      $("calibResult").textContent = `Only ${offsets.length}/8 plucks detected. Lower the noise gate or raise input gain, then retry.`;
      status("Calibration failed (not enough plucks detected).", "err");
      return;
    }
    const sorted = [...offsets].sort((a, b) => a - b);
    const med = sorted[Math.floor(sorted.length / 2)];
    const mad = [...offsets.map((o) => Math.abs(o - med))].sort((a, b) => a - b)[Math.floor(offsets.length / 2)];
    const ms = Math.round(med * 1000);
    S.latencyMs[activeLatencyKey()] = ms;
    if (activeLatencyKey() === "mic") saveMicLatency(ms);
    updateLatencyUI();
    $("calibResult").textContent =
      `offsets (ms): ${offsets.map((o) => Math.round(o * 1000)).join(", ")}  ->  median ${ms} ms, spread (MAD) ${Math.round(mad * 1000)} ms` +
      (mad > 0.03 ? "  (spread is large: try again, pluck right on the click)" : "");
    status(`Latency set to ${ms} ms (${activeLatencyKey()}).`, "ok");
  } finally {
    setBusy(false);
  }
}

function updateLatencyUI() {
  const key = activeLatencyKey();
  $("latency").value = S.latencyMs[key];
  $("latencyLabel").textContent = key === "mic" ? "(mic, saved in this browser)" : "(simulate mode, not saved)";
}

// ---------------------------------------------------------------------------
// Free-running metronome

function stopMetronomeUI() {
  if (S.metronome) S.metronome.stop();
  $("metroToggle").textContent = "Start metronome";
}

async function toggleMetronome() {
  await ensureAudio();
  if (S.metronome.running) return stopMetronomeUI();
  S.metronome.start(S.ctx.currentTime + 0.1, {
    bpm: clampBpm(),
    onBeat: (b) => ($("countIn").textContent = `beat ${(b % 4) + 1}`),
  });
  $("metroToggle").textContent = "Stop metronome";
}

function clampBpm() {
  const v = Math.min(200, Math.max(40, Number($("bpm").value) || 80));
  $("bpm").value = v;
  return v;
}

// ---------------------------------------------------------------------------
// Wire up controls

function bindRange(id, valId, fmt, apply) {
  const el = $(id);
  const update = () => {
    $(valId).textContent = fmt(Number(el.value));
    apply(Number(el.value));
    saveStore({ [id]: el.value });
  };
  if (stored[id] !== undefined) el.value = stored[id];
  el.addEventListener("input", update);
  update();
}

function init() {
  buildGrid();
  showSimExpected();
  if (stored.bpm) $("bpm").value = stored.bpm;
  $("bpm").addEventListener("change", () => saveStore({ bpm: clampBpm() }));

  bindRange("inputGain", "gainVal", (v) => `+${v} dB`, (v) => S.inputBus && (S.inputBus.gain.value = dbToLin(v)));
  bindRange("gate", "gateVal", (v) => `${v} dBFS`, (v) => {
    onsetParams.gateDb = v;
    pitchParams.minRms = dbToLin(v - 6);
  });
  bindRange("ratio", "ratioVal", (v) => `x${v.toFixed(1)} (+${(20 * Math.log10(v)).toFixed(1)} dB)`, (v) => (onsetParams.energyRatio = v));
  bindRange("clarity", "clarityVal", (v) => v.toFixed(2), (v) => (pitchParams.clarityThreshold = v));
  bindRange("tolerance", "tolVal", (v) => `±${v} ms`, () => {});
  bindRange("clickVol", "clickVolVal", (v) => v.toFixed(2), (v) => S.metronome && (S.metronome.volume = v));

  $("tripletClick").addEventListener("change", () => S.metronome && (S.metronome.tripletClick = $("tripletClick").checked));
  $("legato").addEventListener("change", () => (onsetParams.legato = $("legato").checked));
  $("simMonitor").addEventListener("input", () => S.simMonitor && (S.simMonitor.gain.value = Number($("simMonitor").value)));
  $("simPattern").addEventListener("input", showSimExpected);

  $("enableMic").addEventListener("click", () => enableMic($("deviceSelect").value || undefined).catch(() => {}));
  $("deviceSelect").addEventListener("change", () => S.stream && enableMic($("deviceSelect").value).catch(() => {}));
  navigator.mediaDevices?.addEventListener?.("devicechange", () => S.stream && refreshDevices());

  $("simulate").addEventListener("change", async () => {
    await ensureAudio();
    applySimRouting();
    status(isSim() ? "Simulate mode: synthetic plucks feed the detector (mic disconnected)." : "Simulate off.", "ok");
  });
  $("latency").addEventListener("change", () => {
    const v = Math.round(Number($("latency").value) || 0);
    S.latencyMs[activeLatencyKey()] = v;
    if (activeLatencyKey() === "mic") saveMicLatency(v);
  });

  $("calibrate").addEventListener("click", () => calibrate().catch((e) => status(e.message, "err")));
  $("record").addEventListener("click", () => recordAnswer().catch(() => {}));
  $("metroToggle").addEventListener("click", () => toggleMetronome());
  $("simPlayNow").addEventListener("click", async () => {
    await ensureAudio();
    if (!isSim()) {
      $("simulate").checked = true;
      applySimRouting();
    }
    try {
      scheduleSim(simNotesForPhrase(S.ctx.currentTime + 0.2, clampBpm()));
    } catch (e) {
      status(e.message, "err");
    }
  });
  $("copyJson").addEventListener("click", () => navigator.clipboard?.writeText($("jsonOut").textContent));
  $("clearLog").addEventListener("click", () => {
    $("log").innerHTML = "";
    logLines.length = 0;
  });
  updateLatencyUI();

  if (!navigator.mediaDevices?.getUserMedia) {
    status("This page needs a secure context (http://localhost or https) for mic access.", "err");
  }
}

// Small API for whoever integrates this with the call/response app.
window.guitarInput = {
  recordAnswer, // -> Promise<{phrase, notes, rejected, bpm, phraseStart, latencyMs}>
  calibrate,
  enableMic,
  get lastResult() {
    return S.lastResult;
  },
};

init();
