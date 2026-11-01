import SoundAndComplete.Spec

/-!
# The checker: the code that runs

This file has the code the app runs:

* `checkRule` and `grade` judge what you played.
* `findAnswer` searches for an answer that obeys every rule.
* `chooseCall` is the gate: it picks an LLM-proposed call only if you can answer it.
* `rulesWorkable` says whether any call at all can be answered under your rules.

The theorems in `Theorems.lean` prove this code agrees with `Spec.lean`.
-/

namespace Blues

/-! ## Judging one answer -/

/-- Runnable version of `OnGuitar`. -/
def onGuitarB (p : Pitch) : Bool := guitarLow ≤ p && p ≤ guitarHigh

/-- Runnable version of `IsTone`. -/
def isToneB (c : Chord) (t : ChordTone) (p : Pitch) : Bool :=
  pitchClass p == (c.root + t.semitones) % 12

/-- Runnable version of `NoLeapBiggerThan`. -/
def noLeapBiggerThanB (k : Nat) : Phrase → Bool
  | a :: b :: rest => distance a b ≤ k && noLeapBiggerThanB k (b :: rest)
  | _ => true

/-- Runnable version of `EndsOn`. -/
def endsOnB (phrase : Phrase) (good : Pitch → Bool) : Bool :=
  match phrase.getLast? with
  | some p => good p
  | none => true

/-- Does `answer` obey `rule`? Runnable version of `RuleHolds`. -/
def checkRule (ctx : Context) (call answer : Phrase) : Rule → Bool
  | .startNear k =>
      match call.getLast?, answer.head? with
      | some c, some a => distance c a ≤ k
      | _, _ => true
  | .maxLeap k => noLeapBiggerThanB k answer
  | .landOn t => endsOnB answer (isToneB ctx.endChord t)
  | .turnaroundEndsOn n => ctx.exchange != 2 || endsOnB answer (fun p => pitchClass p == n)
  | .stayBetween low high => answer.all fun p => low ≤ p && p ≤ high
  | .avoid n => answer.all fun p => pitchClass p != n

/-- The end-of-song report: each rule, and whether what you played obeyed it. -/
def grade (ctx : Context) (call : Phrase) (rules : List Rule) (played : Phrase) :
    List (Rule × Bool) :=
  rules.map fun r => (r, checkRule ctx call played r)

/-- Runnable version of `PlayableAnswer`. -/
def playableAnswerB (answer : Phrase) : Bool :=
  !answer.isEmpty && answer.length ≤ maxAnswerNotes && answer.all onGuitarB

/-- Runnable version of `PlayableCall`. -/
def playableCallB (call : Phrase) : Bool :=
  !call.isEmpty && call.length ≤ maxCallNotes && call.all onGuitarB

/-- Runnable version of `Satisfies`. -/
def checkAnswer (ctx : Context) (call : Phrase) (rules : List Rule) (answer : Phrase) : Bool :=
  playableAnswerB answer && rules.all (checkRule ctx call answer)

/-! ## Searching for an answer

Each rule looks at one part of the answer:

* every note (`stayBetween`, `avoid`)
* the first note (`startNear`)
* the last note (`landOn`, `turnaroundEndsOn`)
* each pair of neighboring notes (`maxLeap`)

So we can build answers one note at a time. Layer `n` keeps, for each note
the answer can end on, one valid start of length `n + 1` that ends there.
-/

/-- Which part of the answer a rule looks at. -/
inductive RulePart
  | everyNote
  | firstNote
  | lastNote
  | neighbors
  deriving DecidableEq

/-- Which part of the answer each rule looks at. -/
def Rule.part : Rule → RulePart
  | .startNear _ => .firstNote
  | .maxLeap _ => .neighbors
  | .landOn _ => .lastNote
  | .turnaroundEndsOn _ => .lastNote
  | .stayBetween _ _ => .everyNote
  | .avoid _ => .everyNote

/-- Every note on the guitar, low to high. -/
def guitarNotes : List Pitch :=
  (List.range (guitarHigh - guitarLow + 1)).map (· + guitarLow)

section Search
variable (ctx : Context) (call : Phrase) (rules : List Rule)

/-- `p` may appear anywhere in the answer. -/
def noteOk (p : Pitch) : Bool :=
  onGuitarB p && rules.all fun r => r.part != .everyNote || checkRule ctx call [p] r

/-- `p` may be the first note. -/
def firstOk (p : Pitch) : Bool :=
  rules.all fun r => r.part != .firstNote || checkRule ctx call [p] r

/-- `p` may be the last note. -/
def lastOk (p : Pitch) : Bool :=
  rules.all fun r => r.part != .lastNote || checkRule ctx call [p] r

/-- `q` may come right after `p`. -/
def stepOk (p q : Pitch) : Bool :=
  rules.all fun r => r.part != .neighbors || checkRule ctx call [p, q] r

/-- The newest note of a phrase stored newest-first passes `ok`. -/
def newestOk (ok : Pitch → Bool) : Phrase → Bool
  | p :: _ => ok p
  | [] => false

/-- One-note starts. Phrases in layers are stored newest note first. -/
def firstLayer : List Phrase :=
  (guitarNotes.filter fun p => noteOk ctx call rules p && firstOk ctx call rules p).map ([·])

/-- Add one note to the starts in `layer`, keeping one start per ending note. -/
def nextLayer (layer : List Phrase) : List Phrase :=
  guitarNotes.filterMap fun q =>
    if noteOk ctx call rules q then
      (layer.find? (newestOk (fun p => stepOk ctx call rules p q))).map (q :: ·)
    else none

/-- `layers n` holds valid starts of length `n + 1`, newest note first. -/
def layers : Nat → List Phrase
  | 0 => firstLayer ctx call rules
  | n + 1 => nextLayer ctx call rules (layers n)

/-- Find a correct answer to `call`, trying the shortest answers first.
Returns `none` if there is no correct answer. -/
def findAnswer : Option Phrase :=
  (List.range maxAnswerNotes).findSome? fun n =>
    ((layers ctx call rules n).find? (newestOk (lastOk ctx call rules))).map List.reverse

end Search

/-! ## The gate -/

/-- Runnable version of `GoodCall`: the call is playable and has an answer. -/
def callIsGood (ctx : Context) (rules : List Rule) (call : Phrase) : Bool :=
  playableCallB call && (findAnswer ctx call rules).isSome

/-- The gate. Given the calls the LLM proposed, in order, pick the first one
you can answer. `none` means the app must ask the LLM again or use a fallback. -/
def chooseCall (ctx : Context) (rules : List Rule) (proposals : List Phrase) : Option Phrase :=
  proposals.find? (callIsGood ctx rules)

/-- Is there any call at all, at this point in the song, that you can answer?
A call only matters through its last note, so it is enough to try every
one-note call. -/
def rulesWorkable (ctx : Context) (rules : List Rule) : Bool :=
  guitarNotes.any fun p => callIsGood ctx rules [p]

end Blues
