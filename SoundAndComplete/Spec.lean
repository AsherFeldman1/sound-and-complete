import SoundAndComplete.Music

/-!
# The spec: what the rules mean

This is the file to review. It says, in plain terms, what each practice rule
means and when an answer obeys the rules. This file and `Music.lean` are all you
must agree with: the main theorems compare the running code against them.

Nothing here runs. The code that runs (the checkers and the search) is proven
to match this file.

A rule talks about your answer, and may also look at the call it answers and at
where you are in the song (`ctx`).
-/

namespace Blues

/-! ## Helpers -/

/-- No two notes in a row are more than `k` frets apart. Rests in between don't count. -/
def NoLeapBiggerThan (k : Nat) : List Pitch → Prop
  | a :: b :: rest => distance a b ≤ k ∧ NoLeapBiggerThan k (b :: rest)
  | _ => True

/-! ## The rules -/

/-- A practice rule that you set before you play. -/
inductive Rule
  -- Rules that answer the call
  /-- Your notes start in exactly the same slots as the call's notes.
  Same rhythm; the notes themselves can be anything. -/
  | echoRhythm
  /-- At least `k` of the call's note starts are also note starts in your answer.
  A looser echo of the call's rhythm. -/
  | echoSomeRhythm (k : Nat)
  /-- Your first `n` notes are the call's first `n` notes, all moved up or down
  by the same nonzero amount (the same melody shape, starting somewhere else).
  Copying the call exactly does not count. Rhythm is free. The app allows `n`
  from 1 to 4. -/
  | sequence (n : Nat)
  /-- You play fewer notes than the call. -/
  | sayLess
  /-- Your first note is at most this many frets from the call's last note. -/
  | startNear (frets : Nat)
  -- Rules about your answer alone
  /-- No jump between two notes in a row is bigger than this many frets. -/
  | maxLeap (frets : Nat)
  /-- A note starts exactly on beat `beat` (1 to 8, across your two bars), and it
  is chord tone `tone` of the chord under it. -/
  | chordToneOnBeat (tone : ChordTone) (beat : Nat)
  /-- You never play this note name (C = 0, ..., A = 9). -/
  | avoid (noteName : Nat)
  /-- Every note is between these two notes, inclusive (a hand position). -/
  | stayBetween (low high : Pitch)
  /-- No bar of your answer has more than this many notes. -/
  | maxNotesPerBar (n : Nat)
  /-- No note starts in the first `slots` slots. You wait before answering.
  (3 slots = 1 beat.) -/
  | leaveSpace (slots : Nat)
  deriving Repr, DecidableEq

/-- What it means for `answer` to obey `rule`, given the call it answers. -/
def RuleHolds (ctx : Context) (call answer : Phrase) : Rule → Prop
  | .echoRhythm =>
      onsetSlots answer = onsetSlots call
  | .echoSomeRhythm k =>
      k ≤ ((onsetSlots call).filter (· ∈ onsetSlots answer)).length
  | .sequence n =>
      n ≤ (pitches call).length ∧ n ≤ (pitches answer).length ∧
      ∃ shift : Int, shift ≠ 0 ∧
        ((pitches answer).take n).map (fun (p : Pitch) => (p : Int)) =
        ((pitches call).take n).map (fun (p : Pitch) => (p : Int) + shift)
  | .sayLess =>
      (notes answer).length < (notes call).length
  | .startNear k =>
      ∀ c a, (pitches call).getLast? = some c → (pitches answer).head? = some a →
        distance c a ≤ k
  | .maxLeap k =>
      NoLeapBiggerThan k (pitches answer)
  | .chordToneOnBeat t b =>
      1 ≤ b ∧ b ≤ 8 ∧
      ∃ p, (beatSlot b, p) ∈ notes answer ∧ IsTone (ctx.chordAt (beatSlot b)) t p
  | .avoid n =>
      ∀ p ∈ pitches answer, pitchClass p ≠ n
  | .stayBetween low high =>
      ∀ p ∈ pitches answer, low ≤ p ∧ p ≤ high
  | .maxNotesPerBar n =>
      ((notes answer).filter (·.1 < slotsPerBar)).length ≤ n ∧
      ((notes answer).filter (·.1 ≥ slotsPerBar)).length ≤ n
  | .leaveSpace k =>
      ∀ s p, (s, p) ∈ notes answer → k ≤ s

/-! ## Answers and calls -/

/-- A phrase a person can play: exactly 24 slots, at least one note, and every
note on the guitar. -/
def Playable (ph : Phrase) : Prop :=
  ph.length = phraseSlots ∧ notes ph ≠ [] ∧ ∀ p ∈ pitches ph, OnGuitar p

/-- `answer` is a correct answer to `call`: it is playable and obeys every rule. -/
def Satisfies (ctx : Context) (call : Phrase) (rules : List Rule) (answer : Phrase) : Prop :=
  Playable answer ∧ ∀ r ∈ rules, RuleHolds ctx call answer r

/-- There is at least one correct answer to `call`. -/
def Answerable (ctx : Context) (call : Phrase) (rules : List Rule) : Prop :=
  ∃ answer, Satisfies ctx call rules answer

/-- A call the app is allowed to play: it is playable and you can answer it. -/
def GoodCall (ctx : Context) (rules : List Rule) (call : Phrase) : Prop :=
  Playable call ∧ Answerable ctx call rules

/-- Your rules can be played: at least one call is a good call (playable, with
an answer that obeys every rule). If this is false, no call can ever work with
these rules, here in the song. -/
def CallExists (ctx : Context) (rules : List Rule) : Prop :=
  ∃ call, GoodCall ctx rules call

end Blues
