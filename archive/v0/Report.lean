import SoundAndComplete.Theorems
import SoundAndComplete.Audit

/-!
# Audit report

Building this file prints, for each main theorem:

* what its statement depends on (review these definitions), and
* which axioms its proof uses (`sorryAx` = not finished).

Run with `make audit`.
-/

open Blues

#spec_surface checkRule_correct
#spec_surface grade_correct
#spec_surface findAnswer_sound
#spec_surface findAnswer_complete
#spec_surface chooseCall_safe
#spec_surface chooseCall_rejects_only_bad
#spec_surface rulesWorkable_correct

#audit_axioms checkRule_correct
#audit_axioms grade_correct
#audit_axioms findAnswer_sound
#audit_axioms findAnswer_complete
#audit_axioms chooseCall_safe
#audit_axioms chooseCall_rejects_only_bad
#audit_axioms rulesWorkable_correct
