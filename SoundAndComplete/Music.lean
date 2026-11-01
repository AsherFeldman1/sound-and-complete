/-!
# Music basics

Notes, rhythm, chords, and the 12-bar A minor blues.

The main theorems talk about these definitions, so they are part of what the
theorems mean. Keep them small and plain.
-/

namespace Blues

/-! ## Notes -/

/-- A note, as a MIDI number. 60 is middle C. One step up is one fret up. -/
abbrev Pitch := Nat

/-- Lowest note on a guitar in standard tuning: the open low E string (E2). -/
def guitarLow : Pitch := 40

/-- Highest note we allow: fret 24 on the high E string (E6). -/
def guitarHigh : Pitch := 88

/-- The note can be played on a guitar in standard tuning. -/
def OnGuitar (p : Pitch) : Prop := guitarLow ≤ p ∧ p ≤ guitarHigh

/-- The note name without the octave: C = 0, C♯ = 1, D = 2, ..., A = 9, B♭ = 10, B = 11. -/
def pitchClass (p : Pitch) : Nat := p % 12

example : pitchClass 57 = 9 := rfl  -- A3 is an A

/-- How many frets (semitones) apart two notes are. -/
def distance (a b : Pitch) : Nat := if a ≤ b then b - a else a - b

example : distance 60 57 = 3 := rfl

/-! ## Rhythm

The song is a shuffle, so each beat is split into three equal parts (triplets).
A bar has 4 beats, so 12 slots. A phrase (a call or an answer) is 2 bars long,
so 24 slots.

Within a beat, slot 0 is *on* the beat. Slot 2 is the shuffle "and".

    beat:    1        2        3        4
    slot:    0  1  2  3  4  5  6  7  8  9  10 11   (bar 1)
            12 13 14 15 16 17 18 19 20 21 22 23   (bar 2)

We only track when notes *start* (onsets). How long a note rings is ignored.
-/

/-- What happens in one slot: nothing new starts, or a note starts. -/
inductive Slot
  | rest
  | note (p : Pitch)
  deriving Repr, DecidableEq

/-- A phrase: what happens in each slot, in order. A complete phrase has 24 slots. -/
abbrev Phrase := List Slot

/-- Slots in one bar. -/
def slotsPerBar : Nat := 12

/-- Slots in one phrase (2 bars). -/
def phraseSlots : Nat := 24

/-- Slot `s` falls exactly on a beat. -/
def OnBeat (s : Nat) : Prop := s % 3 = 0

/-- The slot where beat `b` of a phrase starts. Beats are counted 1 to 8 across
the two bars: beat 1 is slot 0, beat 5 (bar 2, beat 1) is slot 12. -/
def beatSlot (b : Nat) : Nat := (b - 1) * 3

example : beatSlot 5 = 12 := rfl

/-- The notes of a phrase starting from slot `i`, as (slot, note) pairs. -/
def notesFrom (i : Nat) : Phrase → List (Nat × Pitch)
  | [] => []
  | .rest :: rest => notesFrom (i + 1) rest
  | .note p :: rest => (i, p) :: notesFrom (i + 1) rest

/-- The notes of a phrase, in order, as (slot, note) pairs. -/
def notes (ph : Phrase) : List (Nat × Pitch) := notesFrom 0 ph

/-- Just the notes of a phrase, in order, without their timing. -/
def pitches (ph : Phrase) : List Pitch := (notes ph).map (·.2)

/-- Just the slots where notes start, in order. -/
def onsetSlots (ph : Phrase) : List Nat := (notes ph).map (·.1)

example : notes [.note 57, .rest, .rest, .note 60] = [(0, 57), (3, 60)] := rfl

/-- Build a 24-slot phrase from (slot, note) pairs. Slots not listed are rests.
Only for writing examples and tests by hand. -/
def Phrase.ofNotes (ns : List (Nat × Pitch)) : Phrase :=
  (List.range phraseSlots).map fun s =>
    match ns.find? (·.1 == s) with
    | some (_, p) => .note p
    | none => .rest

/-- Move every note of a phrase up by `d` frets. Rests and timing do not change.
Only for stating properties of the rules: the app does not use it. -/
def Phrase.moveUp (d : Nat) (ph : Phrase) : Phrase :=
  ph.map fun
    | .rest => .rest
    | .note p => .note (p + d)

/-! ## Chords -/

/-- The two kinds of chord in a minor blues. -/
inductive Quality
  /-- Minor 7, like Am7: root, minor third, fifth, flat seventh. -/
  | minor7
  /-- Dominant 7, like E7: root, major third, fifth, flat seventh. -/
  | dominant7
  deriving Repr, DecidableEq

/-- A chord: the note name of its root, and its quality. -/
structure Chord where
  root : Nat
  quality : Quality
  deriving Repr, DecidableEq

/-- The four notes of a seventh chord. -/
inductive ChordTone
  | root
  | third
  | fifth
  | seventh
  deriving Repr, DecidableEq

/-- How far above the root each chord tone is, in semitones. The third depends
on the quality: 3 for minor (Am7 has C), 4 for dominant (E7 has G♯). -/
def ChordTone.semitones : Quality → ChordTone → Nat
  | _, .root => 0
  | .minor7, .third => 3
  | .dominant7, .third => 4
  | _, .fifth => 7
  | _, .seventh => 10

/-- Note `p` is chord tone `t` of chord `c`, in any octave.
Example: C (any octave) is the third of Am7. -/
def IsTone (c : Chord) (t : ChordTone) (p : Pitch) : Prop :=
  pitchClass p = (c.root + t.semitones c.quality) % 12

/-- A minor 7. -/
def Am7 : Chord := ⟨9, .minor7⟩
/-- D minor 7. -/
def Dm7 : Chord := ⟨2, .minor7⟩
/-- E dominant 7. -/
def E7 : Chord := ⟨4, .dominant7⟩

/-! ## The song: 12-bar blues in A minor

    | Am7 | Am7 | Am7 | Am7 |
    | Dm7 | Dm7 | Am7 | Am7 |
    | E7  | Dm7 | Am7 | E7  |
-/

/-- The chord in each bar, numbered 1 to 12. -/
def chordOfBar (bar : Nat) : Chord :=
  match bar with
  | 5 | 6 | 10 => Dm7
  | 9 | 12 => E7
  | _ => Am7

/-- Where we are in the song.

One chorus has three exchanges. In each one the app plays a 2-bar call and you
answer in the next 2 bars:

* exchange 0: call in bars 1–2, answer in bars 3–4
* exchange 1: call in bars 5–6, answer in bars 7–8
* exchange 2: call in bars 9–10, answer in bars 11–12 (the turnaround)
-/
structure Context where
  exchange : Fin 3
  deriving Repr

/-- The song bar where your answer starts: bar 3, 7 or 11. -/
def Context.answerFirstBar (ctx : Context) : Nat := 4 * ctx.exchange.val + 3

/-- The song bar that slot `s` of your answer falls in. -/
def Context.barOfSlot (ctx : Context) (s : Nat) : Nat :=
  ctx.answerFirstBar + s / slotsPerBar

/-- The chord under slot `s` of your answer. -/
def Context.chordAt (ctx : Context) (s : Nat) : Chord := chordOfBar (ctx.barOfSlot s)

-- In the turnaround, bar 2 of the answer is song bar 12: E7.
example : (Context.chordAt ⟨2⟩ 12) = E7 := rfl

/-! ## Display -/

/-- Note name without octave, such as `A` or `C#`. -/
def letterName (p : Pitch) : String :=
  #["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "Bb", "B"][pitchClass p]!

/-- Name of a note, such as `A3` or `C#4`. -/
def noteName (p : Pitch) : String := letterName p ++ toString (p / 12 - 1)

end Blues
