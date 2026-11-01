import SoundAndComplete.Checker

/-!
# The main theorems

These are the promises the app makes to the player. Each one has:

* **In plain words**: what it says.
* **Why you care**: what goes wrong in the app if it is false.
* **What it does not say**: the limits, so nobody over-reads it.

Every statement uses only definitions from `Music.lean` and `Spec.lean` (plus
the code being checked). If you agree with those two files and with the
statements below, you can trust the app's verdicts without reading any proof.

The LLM is not trusted anywhere. It only proposes calls; `chooseCall` decides.

STATUS: statements only. Every proof is `sorry`.
-/

namespace Blues

/-! ## 1. The report card is honest -/

/-- **In plain words:** the app's rule checker says "you obeyed this rule"
exactly when you did obey it, as the rule is defined in `Spec.lean`.

**Why you care:** this is the end-of-song report. If it is false, the app
could praise you for breaking a rule or blame you for one you followed. Every
other theorem also depends on this checker.

**What it does not say:** that the notes the app *heard* are the notes you
*played*. Pitch detection from the guitar is outside the proof. -/
theorem checkRule_correct (ctx : Context) (call answer : Phrase) (r : Rule) :
    checkRule ctx call answer r = true ↔ RuleHolds ctx call answer r := by
  sorry

/-- **In plain words:** for each rule you set, the report shows a check mark
exactly when you obeyed it, and an X exactly when you broke it.

**Why you care:** this is the screen the player sees at the end. It is
`checkRule_correct` applied to the whole list of rules. -/
theorem grade_correct (ctx : Context) (call : Phrase) (rules : List Rule)
    (played : Phrase) (r : Rule) (hr : r ∈ rules) :
    ((r, true) ∈ grade ctx call rules played ↔ RuleHolds ctx call played r) ∧
    ((r, false) ∈ grade ctx call rules played ↔ ¬ RuleHolds ctx call played r) := by
  sorry

/-! ## 2. The answer search finds a real answer, and never misses one -/

/-- **In plain words (sound):** if the app says "here is an answer you could
play", that answer really obeys every one of your rules, and you can play it
on a guitar.

**Why you care:** the app shows this as a hint ("you could have played
this"). It is also the evidence that the call was fair. A wrong hint would
teach you something that breaks your own rules. -/
theorem findAnswer_sound (ctx : Context) (call : Phrase) (rules : List Rule)
    (answer : Phrase) :
    findAnswer ctx call rules = some answer → Satisfies ctx call rules answer := by
  sorry

/-- **In plain words (complete):** if any correct answer exists, the app
finds one. When it says "no answer exists", that is true.

**Why you care:** without this, the gate could reject good LLM calls for no
reason, and `rulesWorkable` could warn you your rules are impossible when they
are not. Sound plus complete means the search is exactly right: it is the
"sound and complete" in the project name.

**What it does not say:** answers longer than `maxAnswerNotes` notes are not
searched. "Correct answer" in `Spec.lean` already includes that limit. -/
theorem findAnswer_complete (ctx : Context) (call : Phrase) (rules : List Rule) :
    Answerable ctx call rules → (findAnswer ctx call rules).isSome := by
  sorry

/-! ## 3. The gate: the LLM can never hand you an impossible call -/

/-- **In plain words:** whatever the LLM proposes, a call the app actually
plays (1) is one of the LLM's proposals, (2) is playable on a guitar, and
(3) has at least one answer that obeys all your rules.

**Why you care:** this is the headline promise. The LLM can produce anything,
including calls that make your rules impossible to follow. This theorem says
none of those ever reaches your ears. It holds for *every* list of proposals,
so it does not depend on the LLM behaving well.

**What it does not say:** that the answer is easy, or that it sounds good. -/
theorem chooseCall_safe (ctx : Context) (rules : List Rule) (proposals : List Phrase)
    (call : Phrase) :
    chooseCall ctx rules proposals = some call →
      call ∈ proposals ∧ GoodCall ctx rules call := by
  sorry

/-- **In plain words:** the gate only throws away bad calls. If it rejects
all the LLM's proposals, then none of them could be answered (or none was
playable).

**Why you care:** a gate that rejects everything is "safe" but useless.
This rules that out. -/
theorem chooseCall_rejects_only_bad (ctx : Context) (rules : List Rule)
    (proposals : List Phrase) :
    chooseCall ctx rules proposals = none →
      ∀ call ∈ proposals, ¬ GoodCall ctx rules call := by
  sorry

/-! ## 4. Warning you about impossible rules -/

/-- **In plain words:** before you play, the app checks each part of the song.
It says "your rules work here" exactly when there is some call the app could
play there that you could answer.

**Why you care:** with rules like "land on the root" and "never play A" in A,
no call can ever be answered. The app catches that up front instead of
leaving the LLM stuck. The check tries only one-note calls, so this theorem
is what shows that trying those is enough. -/
theorem rulesWorkable_correct (ctx : Context) (rules : List Rule) :
    rulesWorkable ctx rules = true ↔ ∃ call, GoodCall ctx rules call := by
  sorry

end Blues
