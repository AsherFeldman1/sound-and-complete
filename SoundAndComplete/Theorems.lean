import SoundAndComplete.App
import SoundAndComplete.CheckerProofs

/-!
# The main theorems

These are the promises the app makes to the player. Each one has:

* **In plain words**: what it says.
* **Why you care**: what goes wrong in the app if it is false.
* **What it does not say**: the limits, so nobody over-reads it.

The statements use the spec (`Music.lean`, `Spec.lean`) and the code being
checked (`Search.lean`, `Checkers.lean`, `App.lean`). If you agree with the
spec and with these statements, you can trust the app without reading any proof.

The LLM is not trusted anywhere. It only proposes calls; `chooseCall` decides.

The promises cover all 13 rules, for every value of their settings. Each one is
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
  | turnaroundTarget n b => exact turnaroundTarget_correct ctx call answer n b
  | avoid n => exact avoid_correct ctx call answer n
  | stayBetween low high => exact stayBetween_correct ctx call answer low high
  | maxNotesPerBar n => exact maxNotesPerBar_correct ctx call answer n
  | syncopate => exact syncopate_correct ctx call answer
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

/-! ## 5. Warning about impossible rules -/

/-- **In plain words:** when the app warns "these rules can never all hold",
that is true: no call at all could be answered.

**Why you care:** it catches mistakes like "echo the rhythm exactly" plus "say
less" before you start playing.

**What it does not say:** that every impossible rule set gets a warning. Some
impossible combinations depend on the call. Those are caught by the gate during
play instead. -/
theorem knownConflict_sound (ctx : Context) (rules : List Rule) :
    knownConflict ctx rules = true → ∀ call, ¬ Answerable ctx call rules := by
  intro h call ⟨answer, hplay, hrules⟩
  -- Every playable answer has a note.
  obtain ⟨⟨s, p⟩, hsp⟩ := List.exists_mem_of_ne_nil _ hplay.2.1
  have hslot := (notesFrom_slot_range 0 answer s p hsp).2
  rw [hplay.1] at hslot
  have hguitar : OnGuitar p := hplay.2.2 p (by simp only [pitches, List.mem_map]; exact ⟨_, hsp, rfl⟩)
  simp only [OnGuitar, guitarLow, guitarHigh] at hguitar
  simp only [knownConflict, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    List.contains_iff_mem] at h
  rcases h with ⟨r, hr, himp⟩ | ⟨hecho, hless⟩
  · have hholds := hrules r hr
    cases r <;> simp only [Rule.impossibleAlone, Bool.false_eq_true] at himp
    case chordToneOnBeat t b =>
      obtain ⟨h1, h2, -⟩ := hholds
      simp_all
    case turnaroundTarget n b =>
      simp only [Bool.and_eq_true, beq_iff_eq] at himp
      obtain ⟨h1, h2, -⟩ := hholds himp.1
      simp_all
    case stayBetween low high =>
      have := hholds p (by simp only [pitches, List.mem_map]; exact ⟨_, hsp, rfl⟩)
      simp only [Bool.or_eq_true, decide_eq_true_eq, guitarLow, guitarHigh] at himp
      have key : ∀ a b c : Nat, (b < a ∨ b < 40 ∨ 88 < a) → 40 ≤ c → c ≤ 88 → a ≤ c → c ≤ b →
          False := by omega
      have himp' : high < low ∨ high < 40 ∨ 88 < low := by
        rcases himp with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (of_decide_eq_true h))
        · exact Or.inr (Or.inr (of_decide_eq_true h))
      exact key low high p himp' hguitar.1 hguitar.2 this.1 this.2
    case maxNotesPerBar n =>
      simp only [beq_iff_eq] at himp
      subst himp
      obtain ⟨h1, h2⟩ := hholds
      simp only [Nat.le_zero, List.length_eq_zero_iff, List.filter_eq_nil_iff,
        decide_eq_true_eq] at h1 h2
      have a1 := h1 _ hsp
      have a2 := h2 _ hsp
      simp only [slotsPerBar] at a1 a2
      omega
    case leaveSpace k =>
      simp only [decide_eq_true_eq] at himp
      have := hholds s p hsp
      simp only [phraseSlots] at himp hslot
      omega
  · have h1 := hrules _ hecho
    have h2 := hrules _ hless
    simp only [RuleHolds, onsetSlots] at h1 h2
    have := congrArg List.length h1
    simp at this
    omega

end Blues
