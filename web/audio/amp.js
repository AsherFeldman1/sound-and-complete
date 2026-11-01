// amp.js: play the guitar input out loud, through a simulated tube amp.
//
// guitar -> input trim -> pre-EQ -> drive (tube-style soft clipping) ->
// tone stack (bass / mid scoop / treble, like a Fender) -> speaker cabinet
// (a 12" speaker's band: no deep lows, no fizz above ~5 kHz) -> spring-style
// reverb -> volume -> speakers.
//
// Only the sound you hear goes through this chain. The note detector reads the
// clean input separately, so the amp settings never change how notes are heard.

const sigmoid = (k) => {
  // Asymmetric soft clipping: like a tube, the two halves of the wave clip a
  // little differently, which adds the warm even harmonics.
  const n = 4096, curve = new Float32Array(n);
  for (let i = 0; i < n; i++) {
    const x = (i / (n - 1)) * 2 - 1;
    const y = x >= 0 ? Math.tanh(k * x) : Math.tanh(k * 0.8 * x) * 1.05;
    curve[i] = y;
  }
  const peak = Math.max(...curve.map(Math.abs));
  return curve.map((v) => v / peak);
};

/** A short, bright, slightly boingy decay: a rough spring reverb tank. */
function springImpulse(ctx, seconds = 1.6) {
  const len = Math.floor(ctx.sampleRate * seconds);
  const buf = ctx.createBuffer(2, len, ctx.sampleRate);
  for (let ch = 0; ch < 2; ch++) {
    const d = buf.getChannelData(ch);
    for (let i = 0; i < len; i++) {
      const t = i / ctx.sampleRate;
      const flutter = 1 + 0.35 * Math.sin(2 * Math.PI * 7.5 * t); // the spring's wobble
      d[i] = (Math.random() * 2 - 1) * Math.exp(-t * 3.2) * flutter * (t < 0.012 ? t / 0.012 : 1);
    }
  }
  return buf;
}

export class GuitarAmp {
  constructor(ctx) {
    this.ctx = ctx;
    const f = (type, freq, gain = 0, Q = 0.707) => {
      const b = ctx.createBiquadFilter();
      b.type = type; b.frequency.value = freq; b.gain.value = gain; b.Q.value = Q;
      return b;
    };

    this.input = ctx.createGain();
    this.lowCut = f("highpass", 70);
    this.preDrive = ctx.createGain();
    this.preEmph = f("peaking", 900, 4, 0.8); // pushes the mids into the drive, like a tube preamp
    this.shaper = ctx.createWaveShaper();
    this.shaper.oversample = "4x";
    this.postDrive = ctx.createGain();
    this.bass = f("lowshelf", 160);
    this.mid = f("peaking", 650, -4, 0.9); // the Fender mid scoop
    this.treble = f("highshelf", 2800);
    // 12" speaker in a cabinet
    this.cabLow = f("highpass", 95, 0, 0.9);
    this.cabThump = f("peaking", 130, 3, 1.2);
    this.cabPresence = f("peaking", 2400, 3.5, 1.1);
    this.cabHigh1 = f("lowpass", 5200, 0, 0.75);
    this.cabHigh2 = f("lowpass", 6500, 0, 0.6);
    // reverb send
    this.verb = ctx.createConvolver();
    this.verb.buffer = springImpulse(ctx);
    this.verbTone = f("highpass", 400);
    this.verbMix = ctx.createGain();
    this.verbMix.gain.value = 0.16;
    this.dry = ctx.createGain();
    this.out = ctx.createGain();
    this.out.gain.value = 0;

    this.input.connect(this.lowCut).connect(this.preEmph).connect(this.preDrive).connect(this.shaper)
      .connect(this.postDrive).connect(this.bass).connect(this.mid).connect(this.treble)
      .connect(this.cabLow).connect(this.cabThump).connect(this.cabPresence).connect(this.cabHigh1).connect(this.cabHigh2);
    this.cabHigh2.connect(this.dry).connect(this.out);
    this.cabHigh2.connect(this.verbTone).connect(this.verb).connect(this.verbMix).connect(this.out);
    this.out.connect(ctx.destination);

    this.source = null;
    this.settings = { volume: 0.6, drive: 0.4, tone: 0.55, on: true };
    this.apply();
  }

  /** Plug a guitar input (a MediaStreamAudioSourceNode) into the amp. */
  attach(source) {
    if (this.source) { try { this.source.disconnect(this.input); } catch { /* already gone */ } }
    this.source = source;
    if (source) source.connect(this.input);
  }

  /** volume, drive, tone: 0..1. on: whether the amp is sounding. */
  set(patch) {
    Object.assign(this.settings, patch);
    this.apply();
  }

  apply() {
    const { volume, drive, tone, on } = this.settings;
    const t = this.ctx.currentTime;
    // Drive 0 is clean; 1 is a cranked tweed. More drive, more clipping; the
    // output is evened out so turning up drive doesn't also make it much louder.
    const k = 1 + drive * drive * 24;
    this.shaper.curve = sigmoid(k);
    this.preDrive.gain.setTargetAtTime(1 + drive * 10, t, 0.02);
    this.postDrive.gain.setTargetAtTime(1.2 / (1 + drive * 5), t, 0.02);
    // Tone: one knob, like a tweed amp. Low = warm and dark, high = bright and cutting.
    this.treble.gain.setTargetAtTime(-9 + tone * 18, t, 0.02);
    this.bass.gain.setTargetAtTime(4 - tone * 6, t, 0.02);
    this.out.gain.setTargetAtTime(on ? volume * volume * 1.4 : 0, t, 0.03);
  }
}
