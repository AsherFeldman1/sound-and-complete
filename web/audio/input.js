// input.js: guitar input for the main app. Same detection pipeline as the lab
// page (lab.html / app.js): mic -> capture worklet -> OnsetDetector -> onsets.
// Settings (latency) are shared with the lab page through localStorage.

import { loadPitchDetector, makePitchEstimator, dbToLin } from "./pitch.js";
import { OnsetDetector, DEFAULT_ONSET_PARAMS, pitchWindowSize } from "./onsets.js";

const STORE_KEY = "sound-and-complete.guitar-input.v1";

export function loadSettings() {
  try {
    return JSON.parse(localStorage.getItem(STORE_KEY) || "{}") || {};
  } catch {
    return {};
  }
}

export class GuitarInput {
  constructor(ctx) {
    this.ctx = ctx;
    this.listeners = new Set(); // called with every onset event
    this.stream = null;
    this.source = null;
    this.level = -Infinity; // dBFS, for a meter
  }

  async init() {
    const ctx = this.ctx;
    await ctx.audioWorklet.addModule("audio/capture-worklet.js");
    this.bus = ctx.createGain();
    const worklet = new AudioWorkletNode(ctx, "capture-processor", {
      numberOfInputs: 1, numberOfOutputs: 1, channelCount: 1,
      channelCountMode: "explicit", channelInterpretation: "speakers",
    });
    const silent = ctx.createGain();
    silent.gain.value = 0; // keep the worklet running; never play the mic out loud
    this.bus.connect(worklet).connect(silent).connect(ctx.destination);

    // The song is in A minor blues (A C D Eb E G): ambiguous pitches lean toward it.
    const onsetParams = { ...DEFAULT_ONSET_PARAMS, scalePcs: [9, 0, 2, 3, 4, 7] };
    const pitchParams = { clarityThreshold: 0.8, minRms: dbToLin(onsetParams.gateDb - 6) };
    const W = pitchWindowSize(ctx.sampleRate);
    const { detector: pd, source } = await loadPitchDetector(W);
    this.pitchSource = source;
    this.estimatePitch = makePitchEstimator(pd, ctx.sampleRate, pitchParams);
    this.detector = new OnsetDetector({
      sampleRate: ctx.sampleRate,
      estimatePitch: this.estimatePitch,
      windowSize: W,
      params: onsetParams,
    });
    worklet.port.onmessage = ({ data }) => {
      if (this.rec) this.rec.push({ frame: data.frame, samples: data.samples.slice() });
      for (const ev of this.detector.push(data.samples, data.frame)) {
        for (const l of this.listeners) l(ev);
      }
      this.level = this.detector.state.rmsDb;
    };
  }

  async listDevices() {
    const devices = await navigator.mediaDevices.enumerateDevices();
    return devices.filter((d) => d.kind === "audioinput");
  }

  async enableMic(deviceId) {
    if (this.stream) this.stream.getTracks().forEach((t) => t.stop());
    if (this.source) this.source.disconnect();
    this.stream = await navigator.mediaDevices.getUserMedia({
      audio: {
        deviceId: deviceId ? { exact: deviceId } : undefined,
        echoCancellation: false, noiseSuppression: false, autoGainControl: false,
      },
    });
    this.source = this.ctx.createMediaStreamSource(this.stream);
    this.source.connect(this.bus);
    this.detector.reset();
    return this.stream.getAudioTracks()[0]?.label || "default input";
  }

  /** True once latency was measured on the lab page. */
  get calibrated() {
    return Number.isFinite(Number(loadSettings().latencyMicMs)) && loadSettings().latencyMicMs !== undefined;
  }

  /** Latency (seconds): the lab's measurement, or else the browser's own
   * estimate of output delay (it includes Bluetooth headphones on most systems). */
  get latency() {
    if (this.calibrated) return (Number(loadSettings().latencyMicMs) || 0) / 1000;
    return (this.ctx.outputLatency || 0) + (this.ctx.baseLatency || 0) + 0.02;
  }

  /** Record raw mic samples (for the debug upload). */
  startRecording() {
    this.rec = [];
  }

  /**
   * Read the notes played between t0 and t1 (AudioContext seconds) from the
   * recorded audio, after the fact (see offline.js), in a background worker.
   * Needs startRecording(). Resolves to onset events, or null if that audio
   * was not recorded.
   */
  async analyze(t0, t1) {
    const chunks = this.rec;
    if (!chunks?.length) return null;
    const sr = this.ctx.sampleRate;
    const f0 = Math.round(t0 * sr), f1 = Math.round(t1 * sr);
    const first = chunks[0].frame, last = chunks[chunks.length - 1];
    const a = Math.max(f0, first), b = Math.min(f1, last.frame + last.samples.length);
    if (b - a < sr * 0.5) return null;
    const samples = new Float32Array(b - a);
    for (const c of chunks) {
      const lo = Math.max(c.frame, a), hi = Math.min(c.frame + c.samples.length, b);
      if (hi > lo) samples.set(c.samples.subarray(lo - c.frame, hi - c.frame), lo - a);
    }
    if (!this.worker) {
      this.worker = new Worker(new URL("./analyze-worker.js", import.meta.url), { type: "module" });
      this.jobs = new Map();
      this.worker.onmessage = ({ data }) => {
        const job = this.jobs.get(data.id);
        this.jobs.delete(data.id);
        if (data.error) job?.reject(new Error(data.error));
        else job?.resolve(data.events);
      };
    }
    const id = (this.jobId = (this.jobId ?? 0) + 1);
    const params = JSON.parse(JSON.stringify(this.detector.params));
    return new Promise((resolve, reject) => {
      this.jobs.set(id, { resolve, reject });
      this.worker.postMessage({ id, samples, sampleRate: sr, startFrame: a, params, tuning: this.detector.tuning ?? 0 }, [samples.buffer]);
    });
  }

  /** Stop recording: {sampleRate, startFrame, samples: Float32Array}. */
  stopRecording() {
    const chunks = this.rec ?? [];
    this.rec = null;
    if (!chunks.length) return null;
    const startFrame = chunks[0].frame;
    const total = chunks[chunks.length - 1].frame + chunks[chunks.length - 1].samples.length - startFrame;
    const samples = new Float32Array(total);
    for (const c of chunks) samples.set(c.samples, c.frame - startFrame);
    return { sampleRate: this.ctx.sampleRate, startFrame, samples };
  }

  /** Collect onsets between t0 and t1 (AudioContext seconds). Returns {events, stop}. */
  collect(t0, t1) {
    const events = [];
    const l = (ev) => {
      if (ev.time >= t0 && ev.time <= t1) events.push(ev);
    };
    this.listeners.add(l);
    return { events, stop: () => this.listeners.delete(l) };
  }
}
