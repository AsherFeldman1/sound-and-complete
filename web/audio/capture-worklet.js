// capture-worklet.js: AudioWorkletProcessor that forwards mono input audio
// to the main thread in 512-sample chunks, each tagged with the absolute
// AudioContext frame index of its first sample (`currentFrame`).
//
// That frame index is what makes onset times sample-accurate on the same
// clock as the metronome (time = frame / sampleRate = AudioContext time).
// The main thread does the actual analysis (onsets.js); batching 4 render
// quanta per message keeps message overhead low (~94 messages/s at 48 kHz).
//
// If the input is disconnected the node sees zero channels; we then send
// silence so the timeline stays continuous.

const CHUNK = 512;

class CaptureProcessor extends AudioWorkletProcessor {
  constructor() {
    super();
    this.buf = new Float32Array(CHUNK);
    this.fill = 0;
    this.startFrame = 0;
  }

  process(inputs) {
    const input = inputs[0];
    const ch = input && input.length > 0 ? input[0] : null;
    const n = ch ? ch.length : 128;
    for (let i = 0; i < n; i++) {
      if (this.fill === 0) this.startFrame = currentFrame + i;
      this.buf[this.fill++] = ch ? ch[i] : 0;
      if (this.fill === CHUNK) {
        this.port.postMessage({ frame: this.startFrame, samples: this.buf }, [this.buf.buffer]);
        this.buf = new Float32Array(CHUNK);
        this.fill = 0;
      }
    }
    return true; // keep alive
  }
}

registerProcessor("capture-processor", CaptureProcessor);
