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

/-- The gate's pick fits the exact description: `call1` is good. -/
example : GoodCall ctx0 rules1 call1 := by
  obtain ⟨-, -, -, hgood, -⟩ := (chooseCall_eq_some_iff ctx0 rules1 [call1] call1).mp call1_passes_gate
  exact hgood

/-- A proposal with no slots is not a good call. -/
theorem emptyPhrase_bad : ¬ GoodCall ctx0 rules1 [] := fun h => by
  have hlen := h.1.1
  simp [phraseSlots] at hlen

/-- With a bad proposal first, the gate still picks `call1`: `call1` is good, and
the only proposal before it is bad. -/
theorem first_good_wins : chooseCall ctx0 rules1 [[], call1] = some call1 :=
  (chooseCall_eq_some_iff ctx0 rules1 [[], call1] call1).mpr
    ⟨[[]], [], rfl, call1_good, by simpa using emptyPhrase_bad⟩

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

end Blues
