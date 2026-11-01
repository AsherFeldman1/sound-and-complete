// pedals.js: how each rule's pedal looks. Purely visual.
//
// Like a real pedalboard, every pedal is a different product: its own case,
// paint, lettering, artwork and knobs. Cases:
//   box     - compact die-cast box, knobs on top, metal stomp switch
//   mini    - narrow mini pedal, one knob or none
//   treadle - wider pedal whose lower half is a big ribbed rubber plate you step on
//   wide    - a wide box with room for two knobs side by side
// Finishes: gloss, sparkle (metal flake), hammer (hammertone), brushed (bare aluminium), matte.
// Knobs: black (ridged), chrome (black skirt, chrome cap), cream, white.
// font/weight/style: the lettering of the pedal's name. art: a printed graphic
// that says what the rule does (see ART). frame: a printed border line.
// model: the little model code printed on the pedal.

export const PEDAL_DESIGNS = {
  startNear:        { type: "box",     c: "#c3261d", print: "#fff1dc", font: "'Abril Fatface'", size: 28, finish: "gloss", knob: "chrome", model: "SN-2", art: "target", frame: true },
  echoSomeRhythm:   { type: "treadle", c: "#8a3fb0", print: "#ffffff", font: "'Unbounded'", weight: 700, size: 15, finish: "gloss", knob: "black", model: "ER-2" },
  echoRhythm:       { type: "mini",    c: "#f0c43c", print: "#2a1d00", font: "'Fraunces'", weight: 800, style: "italic", size: 22, finish: "gloss", knob: "black", model: "Echo", art: "echo" },
  sequence:         { type: "box",     c: "#178a84", print: "#eafffb", font: "'Righteous'", size: 26, finish: "sparkle", knob: "white", model: "SQ-3", art: "stairs" },
  sayLess:          { type: "mini",    c: "#1d1d1f", print: "#efe6d2", font: "'Instrument Serif'", style: "italic", size: 30, finish: "matte", knob: "black", model: "Quiet", art: "bubble", frame: true },
  maxLeap:          { type: "treadle", c: "#6cc23a", print: "#0f1d06", font: "'Unbounded'", weight: 700, size: 15, finish: "gloss", knob: "black", model: "SS-5" },
  stayBetween:      { type: "wide",    c: "#b9bcc0", print: "#1a1a1a", font: "'Limelight'", size: 22, finish: "brushed", knob: "black", model: "Position", art: "range", frame: true },
  avoid:            { type: "box",     c: "#ec6a1f", print: "#1c0d02", font: "'Shrikhand'", size: 30, finish: "gloss", knob: "cream", model: "AV-10", art: "nonote" },
  chordToneOnBeat:  { type: "treadle", c: "#2a6fd6", print: "#ffffff", font: "'Unbounded'", weight: 700, size: 14, finish: "gloss", knob: "black", model: "CT-3" },
  maxNotesPerBar:   { type: "mini",    c: "#e34b8c", print: "#fff0f6", font: "'Bowlby One SC'", size: 18, finish: "gloss", knob: "white", model: "Room", art: "blocks" },
  leaveSpace:       { type: "wide",    c: "#5c1424", print: "#f7e3c9", font: "'Gloock'", size: 24, finish: "sparkle", knob: "chrome", model: "WB-3", art: "hourglass", frame: true },
};

/** Printed artwork, drawn as lines on a 64x64 grid (stroked in the print colour). */
export const ART = {
  target: '<circle cx="32" cy="32" r="24"/><circle cx="32" cy="32" r="14"/><circle cx="32" cy="32" r="4" fill="currentColor"/><path d="M4 32h8M52 32h8M32 4v8M32 52v8"/>',
  echo: '<path d="M14 20a16 16 0 0 1 0 24"/><path d="M24 14a24 24 0 0 1 0 36" opacity=".7"/><path d="M34 8a32 32 0 0 1 0 48" opacity=".45"/><circle cx="8" cy="32" r="4" fill="currentColor"/>',
  stairs: '<path d="M6 56h12V44h12V32h12V20h12V8"/><circle cx="12" cy="50" r="3" fill="currentColor"/><circle cx="24" cy="38" r="3" fill="currentColor"/><circle cx="36" cy="26" r="3" fill="currentColor"/><circle cx="48" cy="14" r="3" fill="currentColor"/>',
  bubble: '<path d="M10 14h44v26H30l-10 10v-10H10z"/><circle cx="32" cy="27" r="3" fill="currentColor"/>',
  range: '<path d="M14 8v48M50 8v48M14 8h6M14 56h6M50 8h-6M50 56h-6"/><path d="M22 40c4-10 8-10 10 0s6 10 10 0"/>',
  nonote: '<ellipse cx="26" cy="44" rx="9" ry="7" transform="rotate(-20 26 44)" fill="currentColor"/><path d="M34 42V12l12 6"/><circle cx="32" cy="32" r="27"/><path d="M13 13l38 38"/>',
  loop: '<path d="M50 24A20 20 0 1 0 52 38"/><path d="M50 12v12H38"/><circle cx="32" cy="32" r="4" fill="currentColor"/>',
  blocks: '<rect x="8" y="22" width="8" height="20" fill="currentColor"/><rect x="28" y="22" width="8" height="20" fill="currentColor"/><rect x="48" y="22" width="8" height="20" fill="currentColor"/><path d="M4 50h56"/>',
  offbeat: '<path d="M4 40h56"/><path d="M10 34v12M28 34v12M46 34v12" opacity=".5"/><circle cx="19" cy="28" r="5" fill="currentColor"/><circle cx="37" cy="20" r="5" fill="currentColor"/><circle cx="55" cy="28" r="5" fill="currentColor"/>',
  hourglass: '<path d="M18 8h28M18 56h28M20 8c0 16 24 16 24 24S20 40 20 56M44 8c0 16-24 16-24 24s24 8 24 24"/><path d="M26 50h12l-6-6z" fill="currentColor"/>',
};
