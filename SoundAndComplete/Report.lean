import SoundAndComplete.Theorems
import SoundAndComplete.SpecExamples
import SoundAndComplete.Audit

/-!
# Audit report

Prints what each main theorem's statement depends on (split into the spec you
must agree with, and the code being checked), and which axioms its proof uses.
`sorryAx` means a proof is not finished. Run with `make audit`.
-/

open Blues

#spec_surface findAnswer_complete
#spec_surface chooseCall_safe

#audit_axioms ruleChecker_correct
#audit_axioms grade_correct
#audit_axioms findAnswer_sound
#audit_axioms findAnswer_complete
#audit_axioms chooseCall_safe
#audit_axioms chooseCall_rejects_only_bad
#audit_axioms knownConflict_sound
#audit_axioms answer1_satisfies
#audit_axioms echoRhythm_sayLess_conflict
