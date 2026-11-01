// metronome.js: Web Audio metronome using the "lookahead scheduler" pattern.
//
// A coarse JS timer (setInterval, 25 ms) only WAKES UP the scheduler; every
// click is scheduled on the AudioContext clock (source.start(exactTime)) a
// little ahead of time, so clicks are sample-accurate even if the main
// thread is busy. (setInterval alone would jitter by 10+ ms.)
//
// The scheduler steps through triplet slots (3 per beat, matching the
// phrase grid). Beat 1 of each bar is accented, other beats are quieter,
// and optionally the 3rd triplet of each beat (the swung "and"/"let") gets a
// soft click so you can feel the shuffle.
//
// Clicks are short band-passed NOISE bursts, not sine beeps, on purpose: if
// the click bleeds from speakers into the guitar mic, the pitch detector
// sees no clear pitch, so the bleed can never become a fake note.

const LOOKAHEAD_S = 0.12; // schedule this far ahead
const TIMER_MS = 25; // how often the scheduler wakes up

export class Metronome {
  constructor(ctx, destination = ctx.destination) {
    this.ctx = ctx;
    this.out = ctx.createGain();
    this.out.gain.value = 0.8;
    this.out.connect(destination);
    // 60 ms of white noise, reused for every click.
    const len = Math.round(0.06 * ctx.sampleRate);
    this.noise = ctx.createBuffer(1, len, ctx.sampleRate);
    const d = this.noise.getChannelData(0);
    for (let i = 0; i < len; i++) d[i] = Math.random() * 2 - 1;
    this.timer = null;
    this.tripletClick = false;
  }

  set volume(v) {
    this.out.gain.value = v;
  }

  get running() {
    return this.timer !== null;
  }

  /**
   * Start clicking at AudioContext time `t0` (beat 1).
   * @param {number} t0
   * @param {object} o
   * @param {number} o.bpm
   * @param {number} [o.beats=Infinity]  stop after this many beats
   * @param {(beatIndex:number, time:number) => void} [o.onBeat]  UI callback, fired near the click time
   */
  start(t0, { bpm, beats = Infinity, onBeat } = {}) {
    this.stop();
    const slotDur = 60 / bpm / 3;
    let slot = 0;
    const lastSlot = beats * 3; // exclusive
    const tick = () => {
      const horizon = this.ctx.currentTime + LOOKAHEAD_S;
      while (slot < lastSlot) {
        const t = t0 + slot * slotDur;
        if (t > horizon) break;
        const sub = slot % 3;
        const beat = Math.floor(slot / 3);
        if (sub === 0) {
          const accent = beat % 4 === 0;
          this._click(t, accent ? 1.0 : 0.45, accent ? 2600 : 1700);
          if (onBeat) {
            const delay = Math.max(0, (t - this.ctx.currentTime) * 1000);
            setTimeout(() => onBeat(beat, t), delay);
          }
        } else if (sub === 2 && this.tripletClick) {
          this._click(t, 0.12, 1200);
        }
        slot++;
      }
      if (slot >= lastSlot) this.stop();
    };
    tick();
    this.timer = setInterval(tick, TIMER_MS);
    return t0;
  }

  stop() {
    if (this.timer !== null) clearInterval(this.timer);
    this.timer = null;
  }

  _click(time, gain, freq) {
    const src = this.ctx.createBufferSource();
    src.buffer = this.noise;
    const bp = this.ctx.createBiquadFilter();
    bp.type = "bandpass";
    bp.frequency.value = freq;
    bp.Q.value = 0.9; // wide band -> no clear pitch
    const g = this.ctx.createGain();
    g.gain.setValueAtTime(0, time);
    g.gain.linearRampToValueAtTime(gain, time + 0.001);
    g.gain.exponentialRampToValueAtTime(0.001, time + 0.035);
    src.connect(bp).connect(g).connect(this.out);
    src.start(time);
    src.stop(time + 0.05);
  }
}
