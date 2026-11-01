# Guitar input prototype (web/)

Browser prototype that listens to an acoustic guitar (DJI Mic 3 lav near the
soundhole, or any input), detects single-note onsets and pitches, and turns a
2-bar answer into the 24-slot phrase that the Lean grader consumes.

No build step, no dependencies to install. The only external code is
[`pitchy@4.1.0`](https://www.npmjs.com/package/pitchy) (McLeod pitch method),
loaded from jsDelivr at runtime. If the CDN can't be reached, a built-in
fallback McLeod detector is used automatically (the page shows `pitch: pitchy`
or `pitch: fallback`).

## Run

```sh
node web/server.js          # serves web/ on http://localhost:8765 (PORT=... to change)
```

Open <http://localhost:8765> in Chrome (Safari and Firefox should work too).
`localhost` counts as a secure context, so the mic works without https.

Tests (pure parts: quantizer, plus an offline synth -> onset detector -> quantizer pipeline):

```sh
node --test web/audio/*.test.mjs    # or: cd web && npm test
```

(On Node 22, `node --test web/audio/` with a bare directory does not work; it
tries to load the directory as a module. Use the glob above.)

## Using the page

1. **Input**: click *Enable mic*, allow access, pick the DJI receiver in
   *Device* (it is preselected if its name contains "DJI"). The page asks for
   `echoCancellation: false, noiseSuppression: false, autoGainControl: false`;
   the line under the picker shows what the browser actually granted. Pluck
   a note: the big note name (e.g. `A3`) and the level meter should react.
2. **Settings**: tempo, input gain, noise gate, onset sensitivity, pitch
   clarity, on-grid tolerance, click volume, triplet "let" click.
3. **Latency calibration** (do this once per setup; see below).
4. **Record answer**: one bar of count-in clicks, then 2 bars are recorded.
   The page shows the 2x12 grid (note name and timing offset per slot), the
   JSON phrase, a per-note table and the onsets it ignored (and why).
5. **Simulate**: tick *Simulate* to feed synthetic plucks into the detector
   instead of the mic. Everything else (calibration, record, grid) works the
   same, so you can demo/debug the whole pipeline without a guitar.
6. **Onset log**: every detected onset as it happens (time, attack/legato,
   note, Hz, clarity). Grey = no clear pitch (knock, click bleed, noise).

For integration, the page exposes `window.guitarInput.recordAnswer()` (returns
a Promise of the result below) and fires a `guitar-phrase` event on `window`.

## JSON contract (to the Lean side)

Grid: shuffle/triplet grid, 3 slots per beat, 4 beats per bar, 12 slots per
bar, 2 bars = **24 slots**. Slot 0 is beat 1. Only note **onsets** matter.
At 80 BPM one slot is 60/80/3 = 0.25 s.

`phrase`: a JSON array of exactly 24 entries, each `null` (no note starts in
that slot) or an integer MIDI pitch 40..88 (E2..E6):

```json
[64,null,67,69,null,67,64,null,null,62,null,null,60,null,57,57,null,null,60,62,null,64,null,69]
```

Per-note feedback (`notes`, in time order):

```json
{ "time": 18.1234, "midi": 62, "slot": 19, "offsetMs": -6.2, "onGrid": true }
```

- `time`: raw onset time in seconds (AudioContext clock, before latency correction)
- `slot`: assigned slot 0..23
- `offsetMs`: (time - latency - slot time) in ms; **negative = early**
- `onGrid`: `|offsetMs| <= tolerance`

Quantization rules (`audio/quantize.js`, a pure function, intended to be
ported to Lean): subtract latency, snap to the nearest slot (exact half rounds
up), drop onsets outside slots 0..23, drop onsets without a valid pitch, and
if two onsets land in the same slot keep the first. With *Strict* on, notes
outside the tolerance are dropped instead of placed.

## Latency calibration

The detector timestamps audio on the same clock as the metronome, so the only
unknown is real-world latency: click leaving the speakers/headphones,
plus the wireless mic + USB input path, plus your own habit of playing
slightly ahead/behind. Calibration measures all of it at once:

1. Mute the strings with your fretting hand.
2. Click *Calibrate*. After a 1-bar count-in, pluck a dead "chk" exactly on
   each of the next 8 clicks.
3. The latency is the **median** of (onset time - click time). The individual
   offsets and their spread are shown; a spread above ~30 ms means "redo it".
4. The value is saved in localStorage (per browser) and subtracted during
   recording. You can also type a value by hand.

Recalibrate whenever you change the output device (Bluetooth headphones add
150-250 ms!) or the input device. Simulate mode keeps its own latency value
(not saved), so you can test calibration with *Simulated latency* without
overwriting the real one.

## Tuning tips: omni lav (DJI Mic 3) near the soundhole

- **Placement**: clip it 5-15 cm from the soundhole, pointing at the neck/body
  joint rather than straight into the hole (less boom, clearer pitch).
- **Gain**: set the transmitter gain so hard plucks peak around -12 to -6
  dBFS on the meter. Use the DJI's own gain first; *Input gain* here is a
  digital boost (it also boosts noise). Turn off the DJI's noise cancelling
  / voice tone presets if you can; they treat guitar as noise.
- **Noise gate**: watch the meter while *not* playing (backing track on).
  Set the gate ~6-10 dB above that idle level and below your softest notes.
- **Backing track bleed**: an omni mic hears the room. Best: play the backing
  track and clicks through **headphones**. With speakers, keep them quiet and
  away from the guitar; the metronome uses unpitched noise clicks so bleed
  can't become fake notes, but a loud pitched backing track can.
- **False onsets** (extra notes): raise *Onset sensitivity* (bigger jump
  needed) or the gate; untick *Detect hammer-ons* if vibrato/bends trigger
  new notes. **Missed repeated notes**: lower *Onset sensitivity*.
- **Wrong octave / no pitch**: raise the gain a little; lower *Pitch clarity
  min* to ~0.85; avoid letting other strings ring.

## Files

| file | what |
| --- | --- |
| `server.js` | dependency-free static server (http + fs) |
| `index.html`, `style.css`, `app.js` | UI, audio graph, calibration, recording |
| `audio/quantize.js` | **pure** onsets -> 24-slot phrase |
| `audio/onsets.js` | **pure** streaming onset detector (energy jump + pitch-change onsets) |
| `audio/pitch.js` | pitchy loader, fallback McLeod detector, MIDI helpers |
| `audio/capture-worklet.js` | AudioWorklet that forwards samples tagged with their frame index |
| `audio/metronome.js` | lookahead-scheduled Web Audio metronome |
| `audio/synth.js` | **pure** synthetic pluck renderer (simulate mode + tests) |
| `audio/*.test.mjs` | Node tests |

## How detection works (short)

- An AudioWorklet sends 512-sample chunks tagged with `currentFrame`, so
  onset times are sample-accurate on the AudioContext clock (better than
  AnalyserNode + requestAnimationFrame polling, which jitters by a frame).
- Every 256 samples (~5 ms): an **attack** is a hop whose RMS is above the
  gate and >= *sensitivity* x the level 16-43 ms earlier, at least 90 ms
  after the previous onset. The time is refined to the first sample of the
  attack.
- The pitch of an attack is the median MIDI note of 5 analysis windows
  (~43 ms each) that start >= 25 ms after the attack (skipping pick noise).
  Notes come out ~0.1 s after they are played.
- A **legato** onset (hammer-on, pull-off, slide arrival) is a stable change
  of >= 1 semitone (held >= 35 ms) while a note rings. Exact octave jumps are
  ignored (usually detector errors). Legato timing is less precise (~20 ms).

## Known limitations

- Monophonic only. Chords, double stops and other strings ringing confuse it.
- Real acoustic-guitar behaviour is untested here (no guitar available while
  building); thresholds were tuned on synthetic plucks. Expect to adjust the
  gate and sensitivity on the day.
- Bends and wide vibrato can create extra legato onsets; slides are reported
  as one onset at the arrival note.
- Very soft notes after a loud one (ghost notes) may be missed: the energy
  jump is relative.
- A pitched backing track played loudly through speakers can produce wrong
  notes if it clears the gate. Use headphones.
- Notes are reported ~0.1 s after they happen, so a recording waits ~0.5 s
  after the last slot before showing the result.
- Latency drifts if devices change (or Bluetooth output is used); recalibrate.
- Stereo inputs are averaged to mono; a silent second channel costs 6 dB.
- Tempo is fixed per recording; the grid assumes a perfectly steady click.
