// sampler.js: play recorded instrument samples (web/samples/, listed in
// sounds.js and downloaded by samples/fetch.mjs).
// A pitched instrument has some recorded notes; other notes use the nearest
// recording, sped up or slowed down a little. Where there are several loudness
// layers, the one closest to the note's velocity plays; where there are several
// takes of the same note and layer, one is picked at random.

import { SOUND_OPTIONS, PARTS, findOption } from "./sounds.js";

/** Where the sound really starts (skips MP3 padding and silence), in seconds. */
function findOnset(buffer, peak) {
  const d = buffer.getChannelData(0);
  const thr = 0.05 * peak;
  for (let i = 0; i < d.length; i++) {
    if (Math.abs(d[i]) >= thr) return Math.max(0, i / buffer.sampleRate - 0.002);
  }
  return 0;
}

function peakOf(buffer) {
  let p = 0;
  for (let c = 0; c < buffer.numberOfChannels; c++) {
    const d = buffer.getChannelData(c);
    for (let i = 0; i < d.length; i++) p = Math.max(p, Math.abs(d[i]));
  }
  return p || 1;
}

export class Sampler {
  /**
   * @param {AudioContext} ctx
   * @param {{id:string, files:Array}} option  one entry of SOUND_OPTIONS
   * @param {string} base  URL prefix of the samples folder
   */
  constructor(ctx, option, base = "samples/") {
    this.ctx = ctx;
    this.option = option;
    this.base = base;
    this.zones = []; // {midi?, name?, dyn, buffer, offset}
    this.trim = 1; // level matching between options
  }

  async load() {
    const zones = await Promise.all(this.option.files.map(async (f) => {
      const res = await fetch(this.base + f.path);
      if (!res.ok) throw new Error(`${f.path}: HTTP ${res.status}`);
      const buffer = await this.ctx.decodeAudioData(await res.arrayBuffer());
      const peak = peakOf(buffer);
      return { midi: f.midi, name: f.name, dyn: f.dyn ?? 0.5, buffer, peak, offset: findOnset(buffer, peak) };
    }));
    this.zones = zones;
    // Level matching: scale so the middle loudness layer peaks at about -6 dB.
    const mids = zones.filter((z) => Math.abs(z.dyn - 0.5) <= 0.26);
    const ref = (mids.length ? mids : zones).reduce((s, z) => s + z.peak, 0) / Math.max(1, (mids.length ? mids : zones).length);
    this.trim = (ref > 0 ? 0.5 / ref : 1) * Math.pow(10, (this.option.db ?? 0) / 20);
    return this;
  }

  /** The recordings that can play `note` at velocity `vel`. */
  _pick(note, vel) {
    let cands;
    if (typeof note === "number") {
      let best = Infinity;
      for (const z of this.zones) if (z.midi !== undefined) best = Math.min(best, Math.abs(z.midi - note));
      // Nearest recorded note; on a tie prefer the one below (shifting up sounds more natural).
      const near = this.zones.filter((z) => z.midi !== undefined && Math.abs(z.midi - note) === best);
      const below = near.filter((z) => z.midi <= note);
      cands = below.length ? below.filter((z) => z.midi === below[0].midi) : near.filter((z) => z.midi === near[0].midi);
    } else {
      cands = this.zones.filter((z) => z.name === note);
    }
    if (!cands.length) return null;
    let bestD = Infinity;
    for (const z of cands) bestD = Math.min(bestD, Math.abs(z.dyn - vel));
    const layer = cands.filter((z) => Math.abs(z.dyn - vel) === bestD);
    return layer[Math.floor(Math.random() * layer.length)];
  }

  /** True if this instrument has a sound for `note` (drum names). */
  has(note) {
    return this.zones.some((z) => (typeof note === "number" ? z.midi !== undefined : z.name === note));
  }

  /**
   * Start a note. Returns {src, env, end} so the caller can track/stop it.
   * @param {number|string} note  MIDI number (pitched) or drum name
   * @param {number} time         AudioContext start time
   * @param {AudioNode} dest
   * @param {object} o  dur (s, undefined = let it ring), vel 0..1, release (s), gain
   */
  play(note, time, dest, { dur, vel = 0.7, release = 0.08, gain = 1, vibrato } = {}) {
    const zone = this._pick(note, vel);
    if (!zone) return null;
    const ctx = this.ctx;
    const rate = typeof note === "number" ? Math.pow(2, (note - zone.midi) / 12) : 1;
    const src = ctx.createBufferSource();
    src.buffer = zone.buffer;
    src.playbackRate.value = rate;
    const env = ctx.createGain();
    // Loudness layers already sound louder or softer; velocity only adds a gentle level change.
    const level = this.trim * gain * (0.35 + 0.65 * Math.max(0, Math.min(1, vel)));
    env.gain.setValueAtTime(0, time);
    env.gain.linearRampToValueAtTime(level, time + 0.002);
    const natural = (zone.buffer.duration - zone.offset) / rate;
    let end = time + natural;
    if (dur !== undefined && dur < natural) {
      env.gain.setValueAtTime(level, time + dur);
      env.gain.setTargetAtTime(0, time + dur, release / 3);
      end = time + dur + release * 2;
    }
    src.connect(env).connect(dest);
    src.start(time, zone.offset);
    src.stop(end + 0.05);
    const sources = [src];
    // Vibrato for held notes: a slow pitch wobble that fades in after the attack.
    if (vibrato) {
      const lfo = ctx.createOscillator();
      lfo.frequency.value = vibrato.rate ?? 5.5;
      const depth = ctx.createGain();
      const t0 = time + (vibrato.delay ?? 0.2);
      depth.gain.setValueAtTime(0, time);
      depth.gain.setValueAtTime(0, t0);
      depth.gain.linearRampToValueAtTime(vibrato.cents ?? 18, t0 + 0.35);
      lfo.connect(depth).connect(src.detune);
      lfo.start(time);
      lfo.stop(end + 0.05);
      sources.push(lfo);
    }
    return { src, env, end, sources };
  }
}

const cache = new WeakMap(); // ctx -> Map(optionId -> Promise<Sampler>)

/** Load (once per AudioContext) the sampler for one option id. */
export function loadOption(ctx, part, id, base = "samples/") {
  if (!cache.has(ctx)) cache.set(ctx, new Map());
  const m = cache.get(ctx);
  const opt = findOption(part, id);
  if (!m.has(opt.id)) {
    const p = new Sampler(ctx, opt, base).load();
    p.catch(() => m.delete(opt.id)); // allow a retry later
    m.set(opt.id, p);
  }
  return m.get(opt.id);
}

/** Load the chosen option of every part: {guitar, bass, keys, drums} (keys may be empty). */
export async function loadBandSamples(ctx, choice, base = "samples/") {
  const out = {};
  await Promise.all(PARTS.map(async (p) => { out[p] = await loadOption(ctx, p, choice?.[p], base); }));
  return out;
}

export { SOUND_OPTIONS };
