// amp.js: a guitar rig for the browser, built on a real amp capture.
//
// guitar -> low cut -> compressor -> mid push (like a Tube Screamer in front of
// the amp, more as Drive goes up) -> input level (Drive) -> Fender Deluxe
// Reverb (a Neural Amp Modeler capture, run by TONE3000's NAM WebAssembly
// engine) -> tone -> speaker cabinet (a recorded Celestion impulse response)
// -> dry + ambience (Reverb knob): recorded spring reverb, a slapback echo
// panned off to one side, and a stereo room -> volume -> limiter -> out.
//
// Used twice: for your guitar (from the audio interface) and for the AI's
// guitar playing the calls, so you trade licks through the same amp.
//
// Until the capture has loaded, or if it can't load, a simple simulated amp
// (soft clipping and filters) plays instead, so there is always sound.
//
// Assets (web/tone/, from github.com/tone-3000/neural-amp-modeler-wasm, MIT):
// deluxe-a2.nam (Fender Deluxe Reverb, NAM A2), celestion.wav, spring.wav.

const ENGINE_URL = new URL("../node_modules/neural-amp-modeler-wasm/dist/engine/index.js", import.meta.url).href;
const TONE_DIR = new URL("../tone/", import.meta.url);

/** Load the capture and impulse responses once per AudioContext. */
const shared = new WeakMap();
function loadShared(ctx) {
  if (!shared.has(ctx)) {
    shared.set(ctx, (async () => {
      const [{ NamEngine }, model, cab, spring] = await Promise.all([
        import(ENGINE_URL),
        fetch(new URL("deluxe-a2.nam", TONE_DIR)).then((r) => { if (!r.ok) throw new Error("amp model missing"); return r.text(); }),
        fetch(new URL("celestion.wav", TONE_DIR)).then((r) => r.arrayBuffer()).then((b) => ctx.decodeAudioData(b)),
        fetch(new URL("spring.wav", TONE_DIR)).then((r) => r.arrayBuffer()).then((b) => ctx.decodeAudioData(b)),
      ]);
      const engine = await NamEngine.attach(ctx);
      return { engine, model, cab, spring };
    })());
  }
  return shared.get(ctx);
}

/** Soft-clipping curve for the fallback amp. */
function softClip(k) {
  const n = 2048, c = new Float32Array(n);
  for (let i = 0; i < n; i++) {
    const x = (i / (n - 1)) * 2 - 1;
    c[i] = Math.tanh(k * x) / Math.tanh(k);
  }
  return c;
}

/** A small stereo room: a soft, dark 1.3 s decay, different in each ear so it
 * sounds wide. Fixed seed, so it is the same room every time. */
function roomImpulse(ctx, seconds = 1.3) {
  const len = Math.floor(ctx.sampleRate * seconds);
  const buf = ctx.createBuffer(2, len, ctx.sampleRate);
  let seed = 12345;
  const rnd = () => ((seed = (seed * 1103515245 + 12345) >>> 0) / 4294967296) * 2 - 1;
  const pre = Math.floor(0.014 * ctx.sampleRate); // early reflections arrive a little late
  for (let ch = 0; ch < 2; ch++) {
    const d = buf.getChannelData(ch);
    let lp = 0;
    for (let i = pre; i < len; i++) {
      const t = (i - pre) / ctx.sampleRate;
      const damp = 0.35 + 0.5 * Math.min(1, t / seconds); // darker as it decays, like a real room
      lp += (rnd() - lp) * (1 - damp);
      d[i] = lp * Math.exp(-t * 4.2);
    }
  }
  return buf;
}

export class GuitarAmp {
  /**
   * @param {BaseAudioContext} ctx
   * @param {{output?: AudioNode, inputTrim?: number, echo?: boolean}} o
   *   output: where the amp plays (default: the speakers); inputTrim: level
   *   matching for the source; echo: include the slapback echo.
   */
  constructor(ctx, { output = ctx.destination, inputTrim = 1, echo = true } = {}) {
    this.ctx = ctx;
    const f = (type, freq, gain = 0, Q = 0.707) => {
      const b = ctx.createBiquadFilter();
      b.type = type; b.frequency.value = freq; b.gain.value = gain; b.Q.value = Q;
      return b;
    };
    const gain = (v = 1) => {
      const g = ctx.createGain();
      g.gain.value = v;
      return g;
    };

    // --- in front of the amp
    this.input = gain(inputTrim);
    this.lowCut = f("highpass", 60);
    this.comp = ctx.createDynamicsCompressor(); // sustain, evens out the picking
    this.comp.threshold.value = -30;
    this.comp.knee.value = 10;
    this.comp.ratio.value = 3;
    this.comp.attack.value = 0.012; // lets the pick attack through
    this.comp.release.value = 0.18;
    this.compMakeup = gain(1.7);
    this.pushLow = f("lowshelf", 300); // the boost tightens the lows...
    this.pushMid = f("peaking", 760, 0, 0.75); // ...and pushes the singing mids
    this.drive = gain(); // how hard the guitar hits the amp
    this.ampIn = gain(); // -> the capture (or the fallback)
    this.ampOut = gain(); // <- the capture (or the fallback)
    this.level = gain(0.5); // levels the capture's output
    this.bass = f("lowshelf", 220);
    this.treble = f("highshelf", 2600);
    this.cab = ctx.createConvolver(); // filled when the IR loads
    this.cabFallback = [f("highpass", 90, 0, 0.8), f("peaking", 120, 2.5, 1.2), f("lowpass", 4800, 0, 0.9), f("lowpass", 5600, 0, 0.6)];
    this.post = gain(); // after the cabinet: the dry guitar
    this.input.connect(this.lowCut).connect(this.comp).connect(this.compMakeup).connect(this.pushLow)
      .connect(this.pushMid).connect(this.drive).connect(this.ampIn);
    this.ampOut.connect(this.level).connect(this.bass).connect(this.treble);
    // Fallback amp and cabinet until the capture is ready.
    this.fbShaper = ctx.createWaveShaper();
    this.fbShaper.curve = softClip(2.5);
    this.fbShaper.oversample = "4x";
    this.ampIn.connect(this.fbShaper).connect(this.ampOut);
    this.cabFallback.reduce((a, b) => a.connect(b));
    this.treble.connect(this.cabFallback[0]);
    this.cabFallback[3].connect(this.post);

    // --- ambience (Reverb knob)
    this.out = gain(0);
    this.post.connect(this.out);
    this.spring = ctx.createConvolver(); // filled when the IR loads
    this.springSend = gain(0);
    this.post.connect(this.springSend); // connected on to the spring once loaded
    this.room = ctx.createConvolver();
    this.room.normalize = true;
    this.room.buffer = roomImpulse(ctx);
    this.roomSend = gain(0);
    this.post.connect(this.roomSend).connect(this.room).connect(this.out);
    this.echoSend = gain(0);
    if (echo) {
      // Slapback: one or two soft, darker repeats, a little to the right.
      const delay = ctx.createDelay(1);
      delay.delayTime.value = 0.125;
      const fb = gain(0.2), dark = f("lowpass", 2600), pan = ctx.createStereoPanner();
      pan.pan.value = 0.45;
      this.post.connect(this.echoSend).connect(delay).connect(dark).connect(pan).connect(this.out);
      dark.connect(fb).connect(delay);
    }

    // Safety limiter: a hard pick on a clean setting can't clip the output.
    this.limiter = ctx.createDynamicsCompressor();
    this.limiter.threshold.value = -4;
    this.limiter.knee.value = 2;
    this.limiter.ratio.value = 20;
    this.limiter.attack.value = 0.002;
    this.limiter.release.value = 0.12;
    this.out.connect(this.limiter).connect(output);

    this.source = null;
    this.real = false; // true once the Deluxe capture is playing
    this.settings = { volume: 0.6, drive: 0.55, tone: 0.45, reverb: 0.4, on: true };
    this.apply();
    this.ready = this._loadReal().catch((e) => {
      console.warn(`Amp capture not available, using the simulated amp: ${e.message}`);
      return false;
    });
  }

  async _loadReal() {
    const { engine, model, cab, spring } = await loadShared(this.ctx);
    const node = await engine.createNode();
    await node.loadModel(model, { slimSize: 1.0 });
    // Swap the fallback for the capture.
    this.ampIn.disconnect(this.fbShaper);
    this.fbShaper.disconnect();
    this.ampIn.connect(node).connect(this.ampOut);
    this.node = node;
    // Level the capture's output. Measured: it is clean with a gain of ~13x
    // below an input of ~0.008, breaks up around 0.01-0.016, and saturates at
    // an output of ~0.19. This brings a played note to about 0.5-0.9.
    this.level.gain.value = 8;
    // Real speaker cabinet and spring.
    this.cab.normalize = true;
    this.cab.buffer = cab;
    this.spring.normalize = true;
    this.spring.buffer = spring;
    this.springSend.connect(this.spring).connect(this.out);
    this.treble.disconnect();
    this.treble.connect(this.cab).connect(this.post);
    this.real = true;
    this.apply();
    return true;
  }

  /** Plug a guitar source into the amp. */
  attach(source) {
    if (this.source) { try { this.source.disconnect(this.input); } catch { /* already gone */ } }
    this.source = source;
    if (source) source.connect(this.input);
  }

  /** volume, drive, tone, reverb: 0..1. on: whether the amp is sounding. */
  set(patch) {
    Object.assign(this.settings, patch);
    this.apply();
  }

  apply() {
    const { volume, drive, tone, reverb, on } = this.settings;
    const t = this.ctx.currentTime;
    const to = (param, v) => param.setTargetAtTime(v, t, 0.02);
    // Drive: how hard the guitar hits the amp. This Deluxe capture was taken
    // cranked, so a normal guitar level (peaks ~0.3-0.5) must come down ~30-48
    // dB to stay warm: drive 0 is clean, ~0.45 is the edge of breakup, 1 is
    // fully cranked. (The fallback amp is less sensitive: 30 dB more.)
    const driveDb = -48 + drive * 30 + (this.real ? 0 : 30);
    to(this.drive.gain, Math.pow(10, driveDb / 20));
    // The mid push comes in with the drive, like stepping on an overdrive.
    to(this.pushMid.gain, 2 + drive * 6);
    to(this.pushLow.gain, -1 - drive * 4);
    // Even out loudness across the knob: clean settings are quieter going in.
    to(this.ampOut.gain, Math.pow(10, -(drive - 0.5) * 15 / 20));
    // Tone: one knob. Left is warm and round, right is bright.
    to(this.treble.gain, -8 + tone * 14);
    to(this.bass.gain, 3 - tone * 5);
    // Reverb: spring, slapback echo and room, together.
    to(this.springSend.gain, 0.04 + reverb * 0.4);
    to(this.echoSend.gain, reverb * 0.45);
    to(this.roomSend.gain, reverb * 0.6);
    // The compressor and mid push add sustain and level; 0.55 brings the whole
    // rig back to about the loudness of the plain amp (measured).
    this.out.gain.setTargetAtTime(on ? volume * volume * 1.6 * 0.3 : 0, t, 0.03);
  }
}
