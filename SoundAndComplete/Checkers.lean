import SoundAndComplete.Spec
import SoundAndComplete.Search

/-!
# One checker per rule

Each rule in `Spec.lean` gets a checker that reads your answer slot by slot.
`Theorems.lean` states that each checker passes exactly the answers that obey
its rule.

All checkers share one memory type, `Mem`. Each rule uses only the fields it
needs and leaves the rest at their defaults. Once a rule has failed for good,
its memory becomes `Mem.fail` and stays that way. The search drops those
memories (`dead`), since they can never pass.
-/

namespace Blues

/-- The memory of one rule's checker. -/
structure Mem where
  /-- Still possible to pass. `false` means failed for good. -/
  ok : Bool := true
  /-- A counter (notes so far, matched notes, or a yes/no as 0/1). -/
  count : Nat := 0
  /-- A second counter (notes in bar 2). -/
  count2 : Nat := 0
  /-- A remembered note (the last note, or the first note). -/
  note : Option Pitch := none
  /-- A remembered shift, for `sequence`. -/
  shift : Option Int := none
  deriving DecidableEq, Repr, Hashable

/-- The memory of a checker that has failed for good. -/
def Mem.fail : Mem := { ok := false }

/-- The default memory: nothing seen yet. -/
def Mem.start : Mem := {}

/-- What the checkers need to know about the call, worked out once. -/
structure CallInfo where
  onsets : List Nat
  pitches : List Pitch
  deriving Repr

/-- Work out `CallInfo` from the call. -/
def CallInfo.of (call : Phrase) : CallInfo :=
  { onsets := Blues.onsetSlots call
    pitches := Blues.pitches call }

/-- Runnable version of `IsTone`. -/
def isToneB (c : Chord) (t : ChordTone) (p : Pitch) : Bool :=
  pitchClass p == (c.root + t.semitones c.quality) % 12

/-- A checker whose memory is just "still ok", failing for good the first time
`bad i p` is true for a note `p` in slot `i`. -/
def failIf (bad : Nat → Pitch → Bool) : Checker Mem where
  init := Mem.start
  step i m x :=
    match x with
    | .note p => if m.ok && bad i p then Mem.fail else m
    | .rest => m
  accept m := m.ok
  dead m := !m.ok

/-- A checker that passes once `good i p` is true for some note `p` in slot `i`. -/
def passIf (good : Nat → Pitch → Bool) : Checker Mem where
  init := Mem.start
  step i m x :=
    match x with
    | .note p => if good i p then { count := 1 } else m
    | .rest => m
  accept m := m.count == 1

/-- A checker that always passes. -/
def alwaysPass : Checker Mem := ⟨Mem.start, fun _ m _ => m, fun _ => true, fun _ => false⟩

/-- A checker that never passes. -/
def neverPass : Checker Mem := ⟨Mem.fail, fun _ m _ => m, fun _ => false, fun _ => true⟩

/-! ## The checkers -/

/-- `echoRhythm`: a note starts in slot `i` exactly when the call has one there,
and every call note is inside the 24 slots. -/
def echoRhythmChecker (ci : CallInfo) : Checker Mem where
  init := if ci.onsets.all (· < phraseSlots) then Mem.start else Mem.fail
  step i m x :=
    let isNote := match x with | .note _ => true | .rest => false
    if m.ok && isNote != ci.onsets.contains i then Mem.fail else m
  accept m := m.ok
  dead m := !m.ok

/-- `echoSomeRhythm k`: count slots where both you and the call start a note,
stopping at `k`. -/
def echoSomeRhythmChecker (ci : CallInfo) (k : Nat) : Checker Mem where
  init := Mem.start
  step i m x :=
    match x with
    | .note _ => if ci.onsets.contains i then { count := min (m.count + 1) k } else m
    | .rest => m
  accept m := k ≤ m.count

/-- `sequence n`: the first note fixes the shift; each of the next `n - 1` notes
must be the matching call note moved by that shift. -/
def sequenceChecker (ci : CallInfo) (n : Nat) : Checker Mem where
  init := Mem.start
  step _ m x :=
    match x with
    | .rest => m
    | .note p =>
      if !m.ok || n ≤ m.count then m
      else match ci.pitches[m.count]? with
        | none => Mem.fail
        | some c =>
          let sh : Int := match m.shift with
            | none => (p : Int) - c
            | some s => s
          if (p : Int) = c + sh then
            -- Once all `n` notes match, the shift no longer matters: forget it.
            { count := m.count + 1, shift := if n ≤ m.count + 1 then none else some sh }
          else Mem.fail
  accept m := m.ok && n ≤ m.count && n ≤ ci.pitches.length
  dead m := !m.ok

/-- `sayLess`: count your notes; fail for good once you reach the call's count. -/
def sayLessChecker (ci : CallInfo) : Checker Mem where
  init := Mem.start
  step _ m x :=
    match x with
    | .note _ =>
      if !m.ok then m
      else if m.count + 1 < ci.pitches.length then { count := m.count + 1 } else Mem.fail
    | .rest => m
  accept m := m.ok && m.count < ci.pitches.length
  dead m := !m.ok

/-- Your first note is within `k` frets of `c`; later notes don't matter. -/
def startNearFrom (c : Pitch) (k : Nat) : Checker Mem where
  init := Mem.start
  step _ m x :=
    match x with
    | .note p => if m.ok && m.count == 0 then
        (if distance c p ≤ k then { count := 1 } else Mem.fail) else m
    | .rest => m
  accept m := m.ok
  dead m := !m.ok

/-- `startNear k`: judge only your first note, against the call's last note. -/
def startNearChecker (ci : CallInfo) (k : Nat) : Checker Mem :=
  match ci.pitches.getLast? with
  | none => alwaysPass
  | some c => startNearFrom c k

/-- `maxLeap k`: remember your last note. -/
def maxLeapChecker (k : Nat) : Checker Mem where
  init := Mem.start
  step _ m x :=
    match x with
    | .rest => m
    | .note p =>
      if !m.ok then m
      else match m.note with
        | none => { note := some p }
        | some l => if distance l p ≤ k then { note := some p } else Mem.fail
  accept m := m.ok
  dead m := !m.ok

/-- `maxNotesPerBar n`: count notes in each bar. -/
def maxNotesPerBarChecker (n : Nat) : Checker Mem where
  init := Mem.start
  step i m x :=
    match x with
    | .rest => m
    | .note _ =>
      if !m.ok then m
      else if i < slotsPerBar then
        (if m.count + 1 ≤ n then { m with count := m.count + 1 } else Mem.fail)
      else
        (if m.count2 + 1 ≤ n then { m with count2 := m.count2 + 1 } else Mem.fail)
  accept m := m.ok
  dead m := !m.ok

/-- The checker for each rule, given where we are in the song and the call. -/
def ruleChecker (ctx : Context) (ci : CallInfo) : Rule → Checker Mem
  | .echoRhythm => echoRhythmChecker ci
  | .echoSomeRhythm k => echoSomeRhythmChecker ci k
  | .sequence n => sequenceChecker ci n
  | .sayLess => sayLessChecker ci
  | .startNear k => startNearChecker ci k
  | .maxLeap k => maxLeapChecker k
  | .chordToneOnBeat t b =>
      if 1 ≤ b && b ≤ 8 then
        passIf fun i p => i == beatSlot b && isToneB (ctx.chordAt i) t p
      else neverPass
  | .turnaroundTarget n b =>
      if ctx.exchange != 2 then alwaysPass
      else if 1 ≤ b && b ≤ 8 then passIf fun i p => i == beatSlot b && pitchClass p == n
      else neverPass
  | .avoid n => failIf fun _ p => pitchClass p == n
  | .stayBetween low high => failIf fun _ p => !(low ≤ p && p ≤ high)
  | .maxNotesPerBar n => maxNotesPerBarChecker n
  | .syncopate => passIf fun i _ => i % 3 != 0
  | .leaveSpace k => failIf fun i _ => i < k

/-- Checks the "playable" part of an answer that the search does not already
guarantee: at least one note, and every note on the guitar. -/
def playableChecker : Checker Mem where
  init := Mem.start
  step _ m x :=
    match x with
    | .rest => m
    | .note p => if !m.ok then m
        else if guitarLow ≤ p && p ≤ guitarHigh then { count := 1 } else Mem.fail
  accept m := m.ok && m.count == 1
  dead m := !m.ok

end Blues
