// analyze-worker.js: runs the after-the-answer analysis (offline.js) off the
// main thread, so the band keeps playing smoothly while it works.
import { analyzeRecording } from "./offline.js";
import { loadPitchDetector, makePitchEstimator, dbToLin } from "./pitch.js";
import { pitchWindowSize } from "./onsets.js";

let ready = null; // {estimatePitch, voteEstimatePitch} per sample rate

async function setup(sampleRate, params) {
  if (ready?.sampleRate === sampleRate) return ready;
  const W = pitchWindowSize(sampleRate);
  const { detector: a } = await loadPitchDetector(W);
  const { detector: b } = await loadPitchDetector(W);
  const minRms = dbToLin(params.gateDb - 6);
  ready = {
    sampleRate,
    estimatePitch: makePitchEstimator(a, sampleRate, { clarityThreshold: 0.8, minRms }),
    voteEstimatePitch: makePitchEstimator(b, sampleRate, { clarityThreshold: 0.75, minRms }),
  };
  return ready;
}

self.onmessage = async ({ data }) => {
  const { id, samples, sampleRate, startFrame, params, tuning } = data;
  try {
    const { estimatePitch, voteEstimatePitch } = await setup(sampleRate, params);
    const events = analyzeRecording({ samples, sampleRate, startFrame, estimatePitch, voteEstimatePitch, params, tuning });
    self.postMessage({ id, events });
  } catch (e) {
    self.postMessage({ id, error: String(e?.stack || e) });
  }
};
