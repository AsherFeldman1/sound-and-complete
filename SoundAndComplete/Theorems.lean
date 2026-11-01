import SoundAndComplete.CallSearchProofs
import SoundAndComplete.SpecProperties

/-!
# The main theorems

These are the promises the app makes to the player. Each one has:

* **In plain words**: what it says.
* **Why you care**: what goes wrong in the app if it is false.
* **What it does not say**: the limits, so nobody over-reads it.

The statements use the spec (`Music.lean`, `Spec.lean`) and the code being
checked (`Search.lean`, `Checkers.lean`, `App.lean`, `CallSearch.lean`). If you
agree with the spec and with these statements, you can trust the app without
reading any proof.

The LLM is not trusted anywhere. It only proposes calls; `chooseCall` decides.

The promises cover all 11 rules, for every value of their settings. Each one is
also tried on a real example in `TheoremExamples.lean`.
-/

namespace Blues

/-! ## 1. Each checker means exactly its rule -/

/-- **In plain words:** for a 24-slot answer, the app's checker for a rule
says "obeyed" exactly when the answer obeys the rule as `Spec.lean` defines it.

**Why you care:** everything else is built on this. The report card runs these
checkers on what you played, and the answer search runs them on every answer it
considers. A wrong checker would grade you wrongly and let the gate pass calls
you cannot answer.

**What it does not say:** that the notes the app *heard* are the notes you
*played*. Pitch and timing detection is outside the proof. -/
theorem ruleChecker_correct (ctx : Context) (call answer : Phrase) (r : Rule)
    (hlen : answer.length = phraseSlots) :
    checkRule ctx call answer r = true ↔ RuleHolds ctx call answer r := by
  unfold checkRule
  cases r with
  | echoRhythm => exact echoRhythm_correct ctx call answer hlen
  | echoSomeRhythm k => exact echoSomeRhythm_correct ctx call answer k
  | sequence n => exact sequence_correct ctx call answer n
  | sayLess => exact sayLess_correct ctx call answer
  | startNear k => exact startNear_correct ctx call answer k
  | maxLeap k => exact maxLeap_correct ctx call answer k
  | chordToneOnBeat t b => exact chordToneOnBeat_correct ctx call answer t b
  | avoid n => exact avoid_correct ctx call answer n
  | stayBetween low high => exact stayBetween_correct ctx call answer low high
  | maxNotesPerBar n => exact maxNotesPerBar_correct ctx call answer n
  | leaveSpace k => exact leaveSpace_correct ctx call answer k

/-! ## 2. The report card is honest -/

/-- **In plain words:** for each rule you set, the end-of-song report shows a
check mark exactly when you obeyed it, and an X exactly when you broke it.

**Why you care:** this is the screen the player sees at the end.

**What it does not say:**
* Anything about timing you played between grid slots. The app snaps what you
  played to the 24-slot grid first; that step is outside this theorem.
* That you played at all. A rule that only forbids something is obeyed by
  silence (`silence_obeys_avoid` in `SpecExamples.lean`), so a silent answer can
  get check marks. Only `isCorrectAnswer` also asks for at least one note. -/
theorem grade_correct (ctx : Context) (call : Phrase) (rules : List Rule) (played : Phrase)
    (hlen : played.length = phraseSlots) (r : Rule) (hr : r ∈ rules) :
    ((r, true) ∈ grade ctx call rules played ↔ RuleHolds ctx call played r) ∧
    ((r, false) ∈ grade ctx call rules played ↔ ¬ RuleHolds ctx call played r) := by
  have hc := ruleChecker_correct ctx call played r hlen
  have key : ∀ b, (r, b) ∈ grade ctx call rules played ↔ checkRule ctx call played r = b := by
    intro b
    simp only [grade, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨r', -, rfl, h⟩; exact h
    · intro h; exact ⟨r, hr, rfl, h⟩
  rw [key, key, ← hc]
  cases checkRule ctx call played r <;> simp

/-- **In plain words:** the report has one line per rule, in the order you set
the rules.

**Why you care:** the app reads the results by position: the first result goes
next to the first rule. If the order changed, a check mark could land on the
wrong rule. -/
theorem grade_keeps_rule_order (ctx : Context) (call : Phrase) (rules : List Rule)
    (played : Phrase) : (grade ctx call rules played).map (·.1) = rules := by
  simp [grade, Function.comp_def]

/-- **In plain words:** `isCorrectAnswer` says yes exactly when the answer is
playable and keeps every rule.

**Why you care:** the app picks the musical answer it shows after a song with
this check, so "an answer that keeps every rule" is true even though that
answer comes from unproven code. -/
theorem isCorrectAnswer_iff (ctx : Context) (call : Phrase) (rules : List Rule)
    (answer : Phrase) :
    isCorrectAnswer ctx call rules answer = true ↔ Satisfies ctx call rules answer := by
  simp only [isCorrectAnswer, Bool.and_eq_true, Satisfies, List.all_eq_true]
  constructor
  · rintro ⟨hp, hall⟩
    have hplay : Playable answer := (isPlayable_iff answer).mp hp
    refine ⟨hplay, fun r hr => ?_⟩
    have := hall (r, checkRule ctx call answer r) (List.mem_map_of_mem hr)
    exact (ruleChecker_correct ctx call answer r hplay.1).mp this
  · rintro ⟨hplay, hrules⟩
    refine ⟨(isPlayable_iff answer).mpr hplay, ?_⟩
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact (ruleChecker_correct ctx call answer r hplay.1).mpr (hrules r hr)

/-! ## 3. The answer search is exact -/

/-- **In plain words (sound):** if the app says "here is an answer you could
play", that answer really is 24 slots long, playable on a guitar, and obeys
every one of your rules.

**Why you care:** the app shows this answer as a hint after you play. It is
also the evidence that the call was fair. -/
theorem findAnswer_sound (ctx : Context) (call : Phrase) (rules : List Rule)
    (answer : Phrase) :
    findAnswer ctx call rules = some answer → Satisfies ctx call rules answer := by
  intro h
  obtain ⟨hlen, hacc⟩ := search_sound _ _ _ h
  rw [answerChecker, allOf_accepts] at hacc
  have hplay := hacc playableChecker (by simp)
  refine ⟨(isPlayable_iff answer).mp (by simp [hlen, phraseSlots, hplay]), ?_⟩
  intro r hr
  have := hacc (ruleChecker ctx (CallInfo.of call) r) (List.mem_cons_of_mem _ (List.mem_map_of_mem hr))
  exact (ruleChecker_correct ctx call answer r hlen).mp this

/-- **In plain words (complete):** if any correct answer exists, the app finds
one. So when the app says "no answer exists", that is true.

**Why you care:** without this, the gate could throw away good LLM calls for no
reason. Sound plus complete means the search is exactly right. This is the
"sound and complete" in the project name. -/
theorem findAnswer_complete (ctx : Context) (call : Phrase) (rules : List Rule) :
    Answerable ctx call rules → (findAnswer ctx call rules).isSome := by
  rintro ⟨answer, hplay, hrules⟩
  apply search_complete
  · apply allOf_deadIsFinal
    intro c hc
    simp only [List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨r, -, rfl⟩
    · exact playableChecker_deadIsFinal
    · exact ruleChecker_deadIsFinal ctx _ r
  · refine ⟨answer, hplay.1, playable_in_alphabet answer hplay, ?_⟩
    rw [answerChecker, allOf_accepts]
    intro c hc
    simp only [List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨r, hr, rfl⟩
    · have := (isPlayable_iff answer).mpr hplay
      simp only [Bool.and_eq_true] at this
      exact this.2
    · exact (ruleChecker_correct ctx call answer r hplay.1).mpr (hrules r hr)

/-- `callIsGood` is exactly `GoodCall`. Used by the gate theorems. -/
theorem callIsGood_iff (ctx : Context) (rules : List Rule) (call : Phrase) :
    callIsGood ctx rules call = true ↔ GoodCall ctx rules call := by
  simp only [callIsGood, Bool.and_eq_true, GoodCall]
  constructor
  · rintro ⟨hp, hs⟩
    refine ⟨(isPlayable_iff call).mp hp, ?_⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨a, findAnswer_sound ctx call rules a ha⟩
  · rintro ⟨hp, hans⟩
    exact ⟨(isPlayable_iff call).mpr hp, findAnswer_complete ctx call rules hans⟩

/-! ## 4. The gate: the LLM can never hand you an impossible call -/

/-- **In plain words:** whatever the LLM proposes, a call the app actually
plays (1) is one of the LLM's proposals, (2) is playable on a guitar, and
(3) has at least one answer that obeys all your rules.

**Why you care:** this is the headline promise. The LLM can produce anything,
including calls that make your rules impossible. None of those ever reaches
your ears. It holds for *every* list of proposals, so it does not depend on
the LLM behaving well.

**What it does not say:** that the answer is easy, or that the call sounds good. -/
theorem chooseCall_safe (ctx : Context) (rules : List Rule) (proposals : List Phrase)
    (call : Phrase) :
    chooseCall ctx rules proposals = some call →
      call ∈ proposals ∧ GoodCall ctx rules call := by
  intro h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  exact (callIsGood_iff ctx rules call).mp (List.find?_some h)

/-- **In plain words:** the gate only throws away bad calls. If it rejects every
proposal, then none of them was both playable and answerable.

**Why you care:** a gate that rejects everything is "safe" but useless. This
rules that out. -/
theorem chooseCall_rejects_only_bad (ctx : Context) (rules : List Rule)
    (proposals : List Phrase) :
    chooseCall ctx rules proposals = none →
      ∀ call ∈ proposals, ¬ GoodCall ctx rules call := by
  intro h call hc hgood
  have := List.find?_eq_none.mp h call hc
  rw [(callIsGood_iff ctx rules call).mpr hgood] at this
  exact this rfl

/-- **In plain words:** if the gate picks a call, the search has a real answer to
it, and that answer keeps every rule.

**Why you care:** this joins the gate to the hint. The app plays the call and
shows this answer, so the answer is never missing for a call that was played. -/
theorem chooseCall_has_answer (ctx : Context) (rules : List Rule) (proposals : List Phrase)
    (call : Phrase) :
    chooseCall ctx rules proposals = some call →
      ∃ answer, findAnswer ctx call rules = some answer ∧ Satisfies ctx call rules answer := by
  intro h
  have hans := (chooseCall_safe ctx rules proposals call h).2.2
  obtain ⟨answer, ha⟩ := Option.isSome_iff_exists.mp (findAnswer_complete ctx call rules hans)
  exact ⟨answer, ha, findAnswer_sound ctx call rules answer ha⟩

/-- **In plain words:** every proposal before the chosen call is bad. The gate
does not skip a good call.

**Why you care:** the app counts the proposals before the chosen one and tells
you Lean turned them down. This says that count is honest. The position
`proposals.idxOf call` is the number the app receives. -/
theorem chooseCall_skips_only_bad (ctx : Context) (rules : List Rule) (proposals : List Phrase)
    (call : Phrase) :
    chooseCall ctx rules proposals = some call →
      ∀ (i : Nat) (hi : i < proposals.length), i < proposals.idxOf call →
        ¬ GoodCall ctx rules proposals[i] := by
  intro h i hi hbefore hgood
  have hfound : proposals.find? (callIsGood ctx rules) = some call := h
  obtain ⟨hcall, before, after, rfl, hbad⟩ := List.find?_eq_some_iff_append.mp hfound
  have hnot : ∀ c ∈ before, callIsGood ctx rules c = false := fun c hc => by simpa using hbad c hc
  have hcall_out : call ∉ before := fun hc => by simp [hnot call hc] at hcall
  have hlt : i < before.length := by simpa [List.idxOf_append, hcall_out] using hbefore
  rw [List.getElem_append_left hlt] at hgood
  have := hnot _ (List.getElem_mem hlt)
  rw [(callIsGood_iff ctx rules _).mpr hgood] at this
  cases this

/-! ## 5. Impossible rules: decided before you play -/

/-- **In plain words:** if `findCall` returns a call and an answer, the call is
one the app may play (playable, with an answer), and that answer obeys every
rule against it.

**Why you care:** when the app says "your rules can be played", it holds the
proof in hand: a real call and a real answer. -/
theorem findCall_sound (ctx : Context) (rules : List Rule) (call answer : Phrase) :
    findCall ctx rules = some (call, answer) →
      GoodCall ctx rules call ∧ Satisfies ctx call rules answer := by
  intro h
  unfold findCall at h
  split at h
  · cases h
  obtain ⟨s, -, hs⟩ := List.exists_of_findSome?_eq_some h
  simp only at hs
  cases hsr : search (bestCallChecker ctx rules s) phraseSlots with
  | none => rw [hsr] at hs; cases hs
  | some a =>
    rw [hsr] at hs
    simp only at hs
    split at hs
    · rename_i hok
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [Bool.and_eq_true] at hok
      have hsat := (isCorrectAnswer_iff ctx _ rules a).mp hok.2
      exact ⟨⟨(isPlayable_iff _).mp hok.1, a, hsat⟩, hsat⟩
    · cases hs

/-- **In plain words:** if any call at all could work with your rules,
`findCall` finds one. So when it finds none, the rules are impossible: no call
the LLM could ever write would let you answer.

**Why you care:** the app warns "these rules can't all hold" exactly when this
is true. There is no list of known bad combinations; the warning is decided by
proof, for every rule set.

**What it does not say:** that the call it finds sounds good. It is only
evidence. The calls you hear still come from the LLM, through the gate. -/
theorem findCall_complete (ctx : Context) (rules : List Rule) :
    CallExists ctx rules → (findCall ctx rules).isSome := by
  rintro ⟨c, hc, a, ha⟩
  -- The quick test passes `a`, so it finds some answer.
  have hq := search_complete (quickChecker ctx rules) phraseSlots
    (quickChecker_deadIsFinal ctx rules)
    ⟨a, ha.1.1, playable_in_alphabet a ha.1, quickChecker_complete ctx rules c a hc ha⟩
  have hnone : (search (quickChecker ctx rules) phraseSlots).isNone = false := by
    cases h : search (quickChecker ctx rules) phraseSlots with
    | none => rw [h] at hq; cases hq
    | some _ => rfl
  -- One of the shifts works.
  obtain ⟨s, hs, hacc⟩ := bestCallChecker_complete ctx rules c a hc ha
  have hsome := search_complete (bestCallChecker ctx rules s) phraseSlots
    (bestCallChecker_deadIsFinal ctx rules s)
    ⟨a, ha.1.1, playable_in_alphabet a ha.1, hacc⟩
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hlen', hacc'⟩ := search_sound _ _ _ ha'
  obtain ⟨hpa, hpc, hrules⟩ :=
    bestCallChecker_sound ctx rules s a' hlen' (callShifts_ne_zero rules s hs) hacc'
  have h1 : isPlayable (bestCall rules s a') = true := (isPlayable_iff _).mpr hpc
  have h2 : isCorrectAnswer ctx (bestCall rules s a') rules a' = true :=
    (isCorrectAnswer_iff ctx _ rules a').mpr ⟨hpa, hrules⟩
  unfold findCall
  simp only [hnone, Bool.false_eq_true, ↓reduceIte]
  rw [List.findSome?_isSome_iff]
  refine ⟨s, hs, ?_⟩
  simp only [ha', h1, h2, Bool.and_self, ↓reduceIte, Option.isSome_some]

end Blues
