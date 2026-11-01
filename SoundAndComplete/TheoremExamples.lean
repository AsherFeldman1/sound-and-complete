import SoundAndComplete.Theorems
import SoundAndComplete.SpecExamples

/-!
# The main theorems on real inputs

A theorem can be true and still say nothing, if its hypotheses can never hold.
Here each main theorem from `Theorems.lean` is used on a real call and real
rules, with every hypothesis met. These are proofs, not tests.
-/

namespace Blues

/-! ## A call the gate accepts -/

/-- `answer1` has 24 slots, so the checker theorem applies to it. -/
example : checkRule ctx0 call1 answer1 .sayLess = true ↔
    RuleHolds ctx0 call1 answer1 .sayLess :=
  ruleChecker_correct ctx0 call1 answer1 .sayLess (by decide)

/-- `call1` has an answer under `rules1`, so the search finds one. -/
theorem call1_search_finds_answer : (findAnswer ctx0 call1 rules1).isSome :=
  findAnswer_complete ctx0 call1 rules1 ⟨answer1, answer1_satisfies⟩

/-- Whatever the search finds for `call1` keeps every rule. -/
example : ∃ a, findAnswer ctx0 call1 rules1 = some a ∧ Satisfies ctx0 call1 rules1 a := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp call1_search_finds_answer
  exact ⟨a, ha, findAnswer_sound ctx0 call1 rules1 a ha⟩

/-- The gate plays `call1` under `rules1`. -/
theorem call1_passes_gate : chooseCall ctx0 rules1 [call1] = some call1 := by
  have h : callIsGood ctx0 rules1 call1 = true :=
    (callIsGood_iff ctx0 rules1 call1).mpr call1_good
  simp [chooseCall, h]

/-- So the safety promise applies to `call1`. -/
example : call1 ∈ [call1] ∧ GoodCall ctx0 rules1 call1 :=
  chooseCall_safe ctx0 rules1 [call1] call1 call1_passes_gate

/-- `answer1` passes the check the app uses on its suggested answers. -/
example : isCorrectAnswer ctx0 call1 rules1 answer1 = true :=
  (isCorrectAnswer_iff ctx0 call1 rules1 answer1).mpr answer1_satisfies

/-- The report card gets a check mark for "say less" on `answer1`. -/
example : (Rule.sayLess, true) ∈ grade ctx0 call1 rules1 answer1 := by
  have hs : RuleHolds ctx0 call1 answer1 .sayLess := answer1_satisfies.2 _ (by decide)
  exact (grade_correct ctx0 call1 rules1 answer1 (by decide) .sayLess (by decide)).1.mpr hs

/-- When the gate plays `call1`, the search has a real answer to it. -/
example : ∃ a, findAnswer ctx0 call1 rules1 = some a ∧ Satisfies ctx0 call1 rules1 a :=
  chooseCall_has_answer ctx0 rules1 [call1] call1 call1_passes_gate

/-- With a useless proposal first, the gate skips it and takes `call1`. -/
theorem empty_then_call1_passes_gate : chooseCall ctx0 rules1 [[], call1] = some call1 := by
  have hbad : callIsGood ctx0 rules1 [] = false := by
    simp [callIsGood, isPlayable, phraseSlots]
  have hgood : callIsGood ctx0 rules1 call1 = true :=
    (callIsGood_iff ctx0 rules1 call1).mpr call1_good
  simp [chooseCall, hbad, hgood]

/-- The proposal it skipped was bad. -/
example : ¬ GoodCall ctx0 rules1 ([[], call1] : List Phrase)[0] :=
  chooseCall_skips_only_bad ctx0 rules1 [[], call1] call1 empty_then_call1_passes_gate 0
    (by simp) (by decide)

/-! ## A call the gate rejects -/

/-- Rules that can never hold together: echo exactly, but play fewer notes. -/
def conflictRules : List Rule := [.echoRhythm, .sayLess]

/-- So the gate rejects `call1` under them. -/
theorem call1_fails_gate : chooseCall ctx0 conflictRules [call1] = none := by
  have h : callIsGood ctx0 conflictRules call1 = false := by
    cases hc : callIsGood ctx0 conflictRules call1 with
    | false => rfl
    | true =>
      exact absurd ⟨call1, (callIsGood_iff ctx0 conflictRules call1).mp hc⟩
        (echoRhythm_sayLess_impossible ctx0)
  simp [chooseCall, h]

/-- And the "only rejects bad calls" promise applies. -/
example : ¬ GoodCall ctx0 conflictRules call1 :=
  chooseCall_rejects_only_bad ctx0 conflictRules [call1] call1_fails_gate call1 (by simp)

/-! ## Deciding before you play whether any call can work -/

/-- `call1` is a good call under `rules1`, so `findCall` finds a call. -/
theorem rules1_possible : (findCall ctx0 rules1).isSome :=
  findCall_complete ctx0 rules1 ⟨call1, call1_good⟩

/-- What it finds is a good call with a real answer. -/
example : ∃ call answer, findCall ctx0 rules1 = some (call, answer) ∧
    GoodCall ctx0 rules1 call ∧ Satisfies ctx0 call rules1 answer := by
  obtain ⟨⟨call, answer⟩, h⟩ := Option.isSome_iff_exists.mp rules1_possible
  exact ⟨call, answer, h, findCall_sound ctx0 rules1 call answer h⟩

/-- If no call can work, `findCall` finds nothing (by `findCall_sound`). -/
theorem findCall_none_of_impossible (ctx : Context) (rules : List Rule)
    (h : ¬ CallExists ctx rules) : findCall ctx rules = none := by
  cases hf : findCall ctx rules with
  | none => rfl
  | some ca => exact absurd ⟨ca.1, (findCall_sound ctx rules ca.1 ca.2 hf).1⟩ h

/-- "Root on beat 1" plus "never play A", in the first exchange: no call. -/
example : findCall ctx0 [.avoid 9, .chordToneOnBeat .root 1] = none :=
  findCall_none_of_impossible _ _ rootOnBeat1_avoidA_impossible

/-- "Echo exactly" plus "say less": no call. -/
example : findCall ctx0 conflictRules = none :=
  findCall_none_of_impossible _ _ (echoRhythm_sayLess_impossible ctx0)

/-! ## Properties of the rules

`answer1` keeps every rule in `rules1`, so each property below starts from a
real pass. `SpecExamples.lean` shows `answer1` failing the tighter settings of
these rules, so the setting does change the result. -/

example : RuleHolds ctx0 call1 answer1 (.maxLeap 6) :=
  maxLeap_looser ctx0 call1 answer1 (by decide) (answer1_satisfies.2 (.maxLeap 5) (by decide))

example : RuleHolds ctx0 call1 answer1 (.startNear 3) :=
  startNear_looser ctx0 call1 answer1 (by decide) (answer1_satisfies.2 (.startNear 2) (by decide))

example : RuleHolds ctx0 call1 answer1 (.maxNotesPerBar 3) :=
  maxNotesPerBar_looser ctx0 call1 answer1 (by decide)
    (answer1_satisfies.2 (.maxNotesPerBar 2) (by decide))

example : RuleHolds ctx0 call1 answer1 (.leaveSpace 2) :=
  leaveSpace_looser ctx0 call1 answer1 (by decide)
    (answer1_satisfies.2 (.leaveSpace 3) (by decide))

example : RuleHolds ctx0 call1 answer1 (.stayBetween 50 70) :=
  stayBetween_looser ctx0 call1 answer1 (by decide) (by decide)
    (answer1_satisfies.2 (.stayBetween 52 69) (by decide))

example : RuleHolds ctx0 call1 answer1 (.echoSomeRhythm 1) :=
  echoSomeRhythm_looser ctx0 call1 answer1 (by decide)
    (answer1_satisfies.2 (.echoSomeRhythm 2) (by decide))

example : RuleHolds ctx0 call1 answer1 (.sequence 1) :=
  sequence_looser ctx0 call1 answer1 (by decide) (answer1_satisfies.2 (.sequence 2) (by decide))

/-- Playing the call itself is an exact echo, so it shares all 4 note starts. -/
example : RuleHolds ctx0 call1 call1 (.echoSomeRhythm 4) :=
  echoRhythm_gives_echoSomeRhythm ctx0 call1 call1 (by decide) rfl

/-- Moving up an octave really changes the notes, and leaves the timing alone. -/
example : notes (answer1.moveUp 12) = [(3, 74), (8, 72), (12, 72)] := by decide

example : RuleHolds ctx0 call1 (answer1.moveUp 12) (.maxLeap 5) :=
  (maxLeap_moveUp ctx0 call1 answer1 5 12).mpr (answer1_satisfies.2 (.maxLeap 5) (by decide))

example : RuleHolds ctx0 (call1.moveUp 12) (answer1.moveUp 12) (.startNear 2) :=
  (startNear_moveUp ctx0 call1 answer1 2 12).mpr (answer1_satisfies.2 (.startNear 2) (by decide))

example : RuleHolds ctx0 (call1.moveUp 12) (answer1.moveUp 12) (.sequence 2) :=
  (sequence_moveUp ctx0 call1 answer1 2 12).mpr (answer1_satisfies.2 (.sequence 2) (by decide))

end Blues
