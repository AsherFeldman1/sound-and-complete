import SoundAndComplete.CallSearch

/-!
# Challenge: the statements Comparator checks

This file repeats the statement of each main theorem in `Theorems.lean`, with
no proof. `lake comparator` (config: `comparator.json`) checks that each
theorem in `Theorems.lean` proves exactly this statement, about the same
definitions, using only the standard axioms.

Copy statements here word for word from `Theorems.lean`. If a statement in
`Theorems.lean` changes, change it here too, on purpose.
-/

namespace Blues

theorem ruleChecker_correct (ctx : Context) (call answer : Phrase) (r : Rule)
    (hlen : answer.length = phraseSlots) :
    checkRule ctx call answer r = true ↔ RuleHolds ctx call answer r := by
  sorry

theorem grade_correct (ctx : Context) (call : Phrase) (rules : List Rule) (played : Phrase)
    (hlen : played.length = phraseSlots) (r : Rule) (hr : r ∈ rules) :
    ((r, true) ∈ grade ctx call rules played ↔ RuleHolds ctx call played r) ∧
    ((r, false) ∈ grade ctx call rules played ↔ ¬ RuleHolds ctx call played r) := by
  sorry

theorem grade_keeps_rule_order (ctx : Context) (call : Phrase) (rules : List Rule)
    (played : Phrase) : (grade ctx call rules played).map (·.1) = rules := by
  sorry

theorem isCorrectAnswer_iff (ctx : Context) (call : Phrase) (rules : List Rule)
    (answer : Phrase) :
    isCorrectAnswer ctx call rules answer = true ↔ Satisfies ctx call rules answer := by
  sorry

theorem findAnswer_sound (ctx : Context) (call : Phrase) (rules : List Rule)
    (answer : Phrase) :
    findAnswer ctx call rules = some answer → Satisfies ctx call rules answer := by
  sorry

theorem findAnswer_complete (ctx : Context) (call : Phrase) (rules : List Rule) :
    Answerable ctx call rules → (findAnswer ctx call rules).isSome := by
  sorry

theorem chooseCall_safe (ctx : Context) (rules : List Rule) (proposals : List Phrase)
    (call : Phrase) :
    chooseCall ctx rules proposals = some call →
      call ∈ proposals ∧ GoodCall ctx rules call := by
  sorry

theorem chooseCall_rejects_only_bad (ctx : Context) (rules : List Rule)
    (proposals : List Phrase) :
    chooseCall ctx rules proposals = none →
      ∀ call ∈ proposals, ¬ GoodCall ctx rules call := by
  sorry

theorem findCall_sound (ctx : Context) (rules : List Rule) (call answer : Phrase) :
    findCall ctx rules = some (call, answer) →
      GoodCall ctx rules call ∧ Satisfies ctx call rules answer := by
  sorry

theorem findCall_complete (ctx : Context) (rules : List Rule) :
    CallExists ctx rules → (findCall ctx rules).isSome := by
  sorry

end Blues
