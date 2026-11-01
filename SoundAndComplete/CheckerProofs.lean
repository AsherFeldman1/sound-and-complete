import SoundAndComplete.Checkers

/-!
# Proofs that each checker means its rule

For each rule: the checker passes a 24-slot answer exactly when `RuleHolds`.
Also: "dead" memories stay dead and never pass (needed for the search).

The general pattern: describe what the memory means after reading any part of
the answer, show that holds at the start and is kept by each step, then read
off the final answer.
-/

namespace Blues

/-! ## Notes of a phrase -/

@[simp] theorem notesFrom_nil (i : Nat) : notesFrom i [] = [] := rfl
@[simp] theorem notesFrom_rest (i : Nat) (w : Phrase) :
    notesFrom i (.rest :: w) = notesFrom (i + 1) w := rfl
@[simp] theorem notesFrom_note (i : Nat) (p : Pitch) (w : Phrase) :
    notesFrom i (.note p :: w) = (i, p) :: notesFrom (i + 1) w := rfl

/-- Every note found from slot `i` sits at slot `i` or later, inside the phrase. -/
theorem notesFrom_slot_range (i : Nat) (w : Phrase) (j : Nat) (p : Pitch) :
    (j, p) ∈ notesFrom i w → i ≤ j ∧ j < i + w.length := by
  induction w generalizing i with
  | nil => simp
  | cons x w ih =>
    cases x with
    | rest =>
      intro h
      have := ih (i + 1) (by simpa using h)
      simp only [List.length_cons]; omega
    | note q =>
      intro h
      simp only [notesFrom_note, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · simp
      · have := ih (i + 1) h
        simp only [List.length_cons]; omega

/-- A note appears in the phrase exactly when it appears among its notes. -/
theorem note_mem_iff (i : Nat) (w : Phrase) (p : Pitch) :
    Slot.note p ∈ w ↔ ∃ j, (j, p) ∈ notesFrom i w := by
  induction w generalizing i with
  | nil => simp
  | cons x w ih =>
    cases x with
    | rest => simp [ih (i + 1)]
    | note q =>
      simp only [List.mem_cons, Slot.note.injEq, notesFrom_note, Prod.mk.injEq, ih (i + 1)]
      constructor
      · rintro (rfl | ⟨j, hj⟩)
        · exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨j, Or.inr hj⟩
      · rintro ⟨j, ⟨-, rfl⟩ | hj⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨j, hj⟩

/-! ## General facts about checkers -/

/-- A state that no step changes stays put. -/
theorem runFrom_fixed {σ : Type} (c : Checker σ) (s : σ) (h : ∀ i x, c.step i s x = s)
    (i : Nat) (w : Phrase) : c.runFrom i s w = s := by
  induction w generalizing i with
  | nil => rfl
  | cons x w ih => simp only [Checker.runFrom, h, ih]

/-- A checker whose steps never touch a failed memory, and whose dead memories
are exactly the failed ones, and which never passes a failed memory. -/
theorem deadIsFinal_of_fail (c : Checker Mem)
    (hdead : ∀ m, c.dead m = !m.ok)
    (hstep : ∀ i m x, m.ok = false → (c.step i m x).ok = false)
    (hacc : ∀ m, m.ok = false → c.accept m = false) : c.DeadIsFinal := by
  constructor
  · intro i m x h
    rw [hdead] at h ⊢
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
    exact hstep i m x h
  · intro m h
    rw [hdead] at h
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact hacc m h

/-! ## "Fail if" and "pass if" checkers -/

@[simp] theorem failIf_step_rest (bad : Nat → Pitch → Bool) (i : Nat) (m : Mem) :
    (failIf bad).step i m .rest = m := rfl
@[simp] theorem failIf_step_note (bad : Nat → Pitch → Bool) (i : Nat) (m : Mem) (p : Pitch) :
    (failIf bad).step i m (.note p) = if m.ok && bad i p then Mem.fail else m := rfl
@[simp] theorem passIf_step_rest (good : Nat → Pitch → Bool) (i : Nat) (m : Mem) :
    (passIf good).step i m .rest = m := rfl
@[simp] theorem passIf_step_note (good : Nat → Pitch → Bool) (i : Nat) (m : Mem) (p : Pitch) :
    (passIf good).step i m (.note p) = if good i p then { count := 1 } else m := rfl

theorem failIf_runFrom_ok (bad : Nat → Pitch → Bool) (i : Nat) (m : Mem) (w : Phrase) :
    ((failIf bad).runFrom i m w).ok =
      (m.ok && (notesFrom i w).all (fun jp => !bad jp.1 jp.2)) := by
  induction w generalizing i m with
  | nil => simp [Checker.runFrom]
  | cons x w ih =>
    cases x with
    | rest => simp only [Checker.runFrom, failIf_step_rest, ih, notesFrom_rest]
    | note p =>
      simp only [Checker.runFrom, failIf_step_note, notesFrom_note, List.all_cons]
      cases hm : m.ok <;> cases hb : bad i p <;> simp [ih, hm, Mem.fail]

/-- A "fail if" checker passes exactly when no note is bad. -/
theorem failIf_accepts (bad : Nat → Pitch → Bool) (w : Phrase) :
    (failIf bad).accepts w = true ↔ ∀ j p, (j, p) ∈ notes w → bad j p = false := by
  simp only [Checker.accepts, Checker.run]
  show ((failIf bad).runFrom 0 Mem.start w).ok = true ↔ _
  rw [failIf_runFrom_ok]
  simp [Mem.start, notes]

theorem passIf_runFrom_count (good : Nat → Pitch → Bool) (i : Nat) (m : Mem) (w : Phrase) :
    ((passIf good).runFrom i m w).count = 1 ↔
      (m.count = 1 ∨ ∃ j p, (j, p) ∈ notesFrom i w ∧ good j p = true) := by
  induction w generalizing i m with
  | nil => simp [Checker.runFrom]
  | cons x w ih =>
    cases x with
    | rest => simp only [Checker.runFrom, passIf_step_rest, ih, notesFrom_rest]
    | note p =>
      simp only [Checker.runFrom, passIf_step_note, notesFrom_note, List.mem_cons, Prod.mk.injEq]
      cases hg : good i p
      · simp only [Bool.false_eq_true, ↓reduceIte, ih]
        constructor
        · rintro (h | ⟨j, q, hm, hq⟩)
          · exact Or.inl h
          · exact Or.inr ⟨j, q, Or.inr hm, hq⟩
        · rintro (h | ⟨j, q, ⟨rfl, rfl⟩ | hm, hq⟩)
          · exact Or.inl h
          · rw [hg] at hq; cases hq
          · exact Or.inr ⟨j, q, hm, hq⟩
      · simp only [↓reduceIte, ih]
        constructor
        · intro _; exact Or.inr ⟨i, p, Or.inl ⟨rfl, rfl⟩, hg⟩
        · intro _; exact Or.inl trivial

/-- A "pass if" checker passes exactly when some note is good. -/
theorem passIf_accepts (good : Nat → Pitch → Bool) (w : Phrase) :
    (passIf good).accepts w = true ↔ ∃ j p, (j, p) ∈ notes w ∧ good j p = true := by
  simp only [Checker.accepts, Checker.run]
  show ((passIf good).runFrom 0 Mem.start w).count == 1 ↔ _
  rw [beq_iff_eq, passIf_runFrom_count]
  simp [Mem.start, notes]

theorem alwaysPass_accepts (w : Phrase) : alwaysPass.accepts w = true := by
  simp [Checker.accepts, Checker.run, alwaysPass, runFrom_fixed]

theorem neverPass_accepts (w : Phrase) : neverPass.accepts w = false := by
  simp [Checker.accepts, Checker.run, neverPass]

/-! ## Dead memories stay dead -/

theorem deadIsFinal_of_never_dead {σ : Type} (c : Checker σ) (h : ∀ s, c.dead s = false) :
    c.DeadIsFinal :=
  ⟨fun _ s _ hd => (by rw [h s] at hd; cases hd), fun s hd => (by rw [h s] at hd; cases hd)⟩

theorem failIf_deadIsFinal (bad : Nat → Pitch → Bool) : (failIf bad).DeadIsFinal :=
  deadIsFinal_of_fail _ (fun _ => rfl)
    (fun i m x hm => by cases x <;> simp [hm])
    (fun m hm => hm)

theorem passIf_deadIsFinal (good : Nat → Pitch → Bool) : (passIf good).DeadIsFinal :=
  deadIsFinal_of_never_dead _ (fun _ => rfl)

theorem alwaysPass_deadIsFinal : alwaysPass.DeadIsFinal :=
  deadIsFinal_of_never_dead _ (fun _ => rfl)

theorem neverPass_deadIsFinal : neverPass.DeadIsFinal :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem playableChecker_deadIsFinal : playableChecker.DeadIsFinal :=
  deadIsFinal_of_fail _ (fun _ => rfl)
    (fun i m x hm => by cases x <;> simp [playableChecker, hm])
    (fun m hm => by simp [playableChecker, hm])

/-- Dropping dead memories is safe for every rule's checker. -/
theorem ruleChecker_deadIsFinal (ctx : Context) (ci : CallInfo) (r : Rule) :
    (ruleChecker ctx ci r).DeadIsFinal := by
  cases r with
  | echoRhythm =>
    exact deadIsFinal_of_fail _ (fun _ => rfl)
      (fun i m x hm => by cases x <;> simp [ruleChecker, echoRhythmChecker, hm])
      (fun m hm => by simp [ruleChecker, echoRhythmChecker, hm])
  | echoSomeRhythm k => exact deadIsFinal_of_never_dead _ (fun _ => rfl)
  | sequence n =>
    refine deadIsFinal_of_fail _ (fun _ => rfl) (fun i m x hm => ?_)
      (fun m hm => by simp [ruleChecker, sequenceChecker, hm])
    cases x <;> simp [ruleChecker, sequenceChecker, hm]
  | sayLess =>
    exact deadIsFinal_of_fail _ (fun _ => rfl)
      (fun i m x hm => by cases x <;> simp [ruleChecker, sayLessChecker, hm])
      (fun m hm => by simp [ruleChecker, sayLessChecker, hm])
  | startNear k =>
    simp only [ruleChecker, startNearChecker]
    split
    · exact alwaysPass_deadIsFinal
    · exact deadIsFinal_of_fail _ (fun _ => rfl)
        (fun i m x hm => by cases x <;> simp [startNearFrom, hm])
        (fun m hm => by simp [startNearFrom, hm])
  | maxLeap k =>
    refine deadIsFinal_of_fail _ (fun _ => rfl) (fun i m x hm => ?_)
      (fun m hm => by simp [ruleChecker, maxLeapChecker, hm])
    cases x <;> simp [ruleChecker, maxLeapChecker, hm]
  | chordToneOnBeat t b =>
    simp only [ruleChecker]
    split
    · exact passIf_deadIsFinal _
    · exact neverPass_deadIsFinal
  | avoid n => exact failIf_deadIsFinal _
  | stayBetween low high => exact failIf_deadIsFinal _
  | maxNotesPerBar n =>
    refine deadIsFinal_of_fail _ (fun _ => rfl) (fun i m x hm => ?_)
      (fun m hm => by simp [ruleChecker, maxNotesPerBarChecker, hm])
    cases x <;> simp [ruleChecker, maxNotesPerBarChecker, hm]
  | leaveSpace k => exact failIf_deadIsFinal _

/-! ## Simple rules: each checker means its rule -/

section Simple
variable (ctx : Context) (call answer : Phrase)

private theorem mem_pitches (w : Phrase) (p : Pitch) :
    p ∈ pitches w ↔ ∃ j, (j, p) ∈ notes w := by
  simp [pitches]

theorem avoid_correct (n : Nat) :
    (ruleChecker ctx (CallInfo.of call) (.avoid n)).accepts answer = true ↔
      RuleHolds ctx call answer (.avoid n) := by
  simp only [ruleChecker, failIf_accepts, RuleHolds, mem_pitches, beq_eq_false_iff_ne]
  constructor
  · rintro h p ⟨j, hj⟩; exact h j p hj
  · intro h j p hj; exact h p ⟨j, hj⟩

theorem stayBetween_correct (low high : Pitch) :
    (ruleChecker ctx (CallInfo.of call) (.stayBetween low high)).accepts answer = true ↔
      RuleHolds ctx call answer (.stayBetween low high) := by
  simp only [ruleChecker, failIf_accepts, RuleHolds, mem_pitches]
  constructor
  · rintro h p ⟨j, hj⟩; have := h j p hj; simp at this; omega
  · intro h j p hj; have := h p ⟨j, hj⟩; simp; omega

theorem leaveSpace_correct (k : Nat) :
    (ruleChecker ctx (CallInfo.of call) (.leaveSpace k)).accepts answer = true ↔
      RuleHolds ctx call answer (.leaveSpace k) := by
  simp only [ruleChecker, failIf_accepts, RuleHolds, decide_eq_false_iff_not, Nat.not_lt]

theorem isToneB_iff (c : Chord) (t : ChordTone) (p : Pitch) :
    isToneB c t p = true ↔ IsTone c t p := by
  simp [isToneB, IsTone]

theorem chordToneOnBeat_correct (t : ChordTone) (b : Nat) :
    (ruleChecker ctx (CallInfo.of call) (.chordToneOnBeat t b)).accepts answer = true ↔
      RuleHolds ctx call answer (.chordToneOnBeat t b) := by
  simp only [ruleChecker, RuleHolds]
  split
  · rename_i hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rw [passIf_accepts]
    constructor
    · rintro ⟨j, p, hj, hg⟩
      simp only [Bool.and_eq_true, beq_iff_eq, isToneB_iff] at hg
      obtain ⟨rfl, ht⟩ := hg
      exact ⟨hb.1, hb.2, p, hj, ht⟩
    · rintro ⟨-, -, p, hj, ht⟩
      exact ⟨beatSlot b, p, hj, by simp [isToneB_iff, ht]⟩
  · rename_i hb
    simp only [neverPass_accepts, Bool.false_eq_true, false_iff]
    rintro ⟨h1, h2, -⟩
    exact hb (by simp [h1, h2])

end Simple

/-! ## Playable -/

@[simp] theorem playable_step_rest (i : Nat) (m : Mem) :
    playableChecker.step i m .rest = m := rfl
@[simp] theorem playable_step_note (i : Nat) (m : Mem) (p : Pitch) :
    playableChecker.step i m (.note p) =
      if !m.ok then m else if guitarLow ≤ p && p ≤ guitarHigh then { count := 1 } else Mem.fail :=
  rfl

theorem playable_runFrom (i : Nat) (m : Mem) (w : Phrase) (hm : m.ok = true)
    (hc : m.count = 0 ∨ m.count = 1) :
    playableChecker.accept (playableChecker.runFrom i m w) = true ↔
      (m.count = 1 ∨ notesFrom i w ≠ []) ∧ ∀ j p, (j, p) ∈ notesFrom i w → OnGuitar p := by
  induction w generalizing i m with
  | nil =>
    simp only [Checker.runFrom, playableChecker, hm, Bool.true_and, beq_iff_eq, notesFrom_nil,
      ne_eq, not_true_eq_false, or_false, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  | cons x w ih =>
    cases x with
    | rest => simp only [Checker.runFrom, playable_step_rest, notesFrom_rest]; exact ih _ _ hm hc
    | note p =>
      simp only [Checker.runFrom, playable_step_note, hm, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, notesFrom_note, ne_eq, reduceCtorEq, not_false_eq_true, or_true,
        List.mem_cons, Prod.mk.injEq, true_and]
      split
      · rename_i hg
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        rw [ih _ _ rfl (Or.inr rfl)]
        constructor
        · rintro ⟨-, h⟩ j q (⟨rfl, rfl⟩ | hq)
          · exact hg
          · exact h j q hq
        · intro h
          exact ⟨Or.inl rfl, fun j q hq => h j q (Or.inr hq)⟩
      · rename_i hg
        rw [runFrom_fixed _ _ (fun i x => by cases x <;> simp [Mem.fail])]
        simp only [playableChecker, Mem.fail, Bool.false_and, Bool.false_eq_true, false_iff]
        intro h
        exact hg (by simpa [OnGuitar] using h i p (Or.inl ⟨rfl, rfl⟩))

/-- The playable checker, on a 24-slot phrase, means `Playable`. -/
theorem isPlayable_iff (w : Phrase) :
    (w.length == phraseSlots && playableChecker.accepts w) = true ↔ Playable w := by
  simp only [Bool.and_eq_true, beq_iff_eq, Playable, Checker.accepts, Checker.run]
  rw [show playableChecker.init = Mem.start from rfl,
    playable_runFrom 0 Mem.start w rfl (Or.inl rfl)]
  simp only [Mem.start, Nat.zero_ne_one, false_or, notes, pitches, List.mem_map]
  constructor
  · rintro ⟨hl, hne, h⟩
    exact ⟨hl, hne, fun p ⟨⟨j, q⟩, hj, hq⟩ => by simp at hq; subst hq; exact h j _ hj⟩
  · rintro ⟨hl, hne, h⟩
    exact ⟨hl, hne, fun j p hj => h p ⟨(j, p), hj, rfl⟩⟩

/-- Every slot of a playable phrase is something the search tries. -/
theorem playable_in_alphabet (w : Phrase) (h : Playable w) : ∀ x ∈ w, x ∈ alphabet := by
  intro x hx
  cases x with
  | rest => simp [alphabet]
  | note p =>
    obtain ⟨j, hj⟩ := (note_mem_iff 0 w p).mp hx
    have hg : OnGuitar p := h.2.2 p (by simp only [pitches, List.mem_map]; exact ⟨(j, p), hj, rfl⟩)
    have hg' : 40 ≤ (p : Nat) ∧ (p : Nat) ≤ 88 := hg
    simp only [alphabet, List.mem_cons, reduceCtorEq, List.mem_map, Slot.note.injEq, false_or]
    refine ⟨p, ?_, rfl⟩
    have hall : (p : Nat) ∈ (List.range (guitarHigh - guitarLow + 1)).map (· + guitarLow) := by
      simp only [List.mem_map, List.mem_range, guitarHigh, guitarLow]
      have key : ∀ q : Nat, 40 ≤ q → q ≤ 88 → q - 40 < 88 - 40 + 1 ∧ q - 40 + 40 = q := by
        intro q h1 h2; omega
      exact ⟨p - 40, (key p hg'.1 hg'.2).1, (key p hg'.1 hg'.2).2⟩
    simp only [guitarNotes, List.mem_append, List.mem_filter]
    cases (inBluesScale p && 55 ≤ p && p ≤ 72) <;> cases inBluesScale p <;> simp_all

/-! ## Counting and memory rules -/

/-- `Mem.fail` stays failed under any checker that leaves failed memories alone. -/
theorem runFrom_fail (c : Checker Mem) (h : ∀ i x, c.step i Mem.fail x = Mem.fail)
    (i : Nat) (w : Phrase) : (c.runFrom i Mem.fail w) = Mem.fail :=
  runFrom_fixed c _ h i w

section Counting
variable (ctx : Context) (call answer : Phrase)

theorem maxNotes_runFrom (n i : Nat) (m : Mem) (w : Phrase) (hm : m.ok = true)
    (hc : m.count ≤ n) (hc2 : m.count2 ≤ n) :
    ((maxNotesPerBarChecker n).runFrom i m w).ok = true ↔
      m.count + ((notesFrom i w).filter (·.1 < slotsPerBar)).length ≤ n ∧
      m.count2 + ((notesFrom i w).filter (·.1 ≥ slotsPerBar)).length ≤ n := by
  induction w generalizing i m with
  | nil => simp [Checker.runFrom, hm, hc, hc2]
  | cons x w ih =>
    cases x with
    | rest =>
      simp only [Checker.runFrom, notesFrom_rest]
      exact ih (i + 1) m hm hc hc2
    | note p =>
      have hfail : ∀ j, ((maxNotesPerBarChecker n).runFrom j Mem.fail w).ok = false := by
        intro j
        rw [runFrom_fail _ (fun i x => by cases x <;> simp [maxNotesPerBarChecker, Mem.fail])]
        rfl
      simp only [Checker.runFrom, notesFrom_note, List.filter_cons]
      show ((maxNotesPerBarChecker n).runFrom (i + 1)
        (if !m.ok then m else if i < slotsPerBar then
          (if m.count + 1 ≤ n then { m with count := m.count + 1 } else Mem.fail)
        else (if m.count2 + 1 ≤ n then { m with count2 := m.count2 + 1 } else Mem.fail)) w).ok
          = true ↔ _
      simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hi : i < slotsPerBar
      · have hi' : ¬ i ≥ slotsPerBar := by omega
        simp only [hi, hi', decide_true, decide_false, ↓reduceIte, List.length_cons,
          Bool.false_eq_true]
        by_cases hn : m.count + 1 ≤ n
        · simp only [hn, ↓reduceIte]
          rw [ih (i + 1) { count := m.count + 1, count2 := m.count2, note := m.note, shift := m.shift } rfl hn hc2]
          constructor <;> rintro ⟨h1, h2⟩ <;> simp only at h1 h2 ⊢ <;> constructor <;> omega
        · simp only [hn, ↓reduceIte, hfail, Bool.false_eq_true, false_iff]
          omega
      · have hi' : i ≥ slotsPerBar := by omega
        simp only [hi, hi', decide_true, decide_false, ↓reduceIte, List.length_cons,
          Bool.false_eq_true]
        by_cases hn : m.count2 + 1 ≤ n
        · simp only [hn, ↓reduceIte]
          rw [ih (i + 1) { count := m.count, count2 := m.count2 + 1, note := m.note, shift := m.shift } rfl hc hn]
          constructor <;> rintro ⟨h1, h2⟩ <;> simp only at h1 h2 ⊢ <;> constructor <;> omega
        · simp only [hn, ↓reduceIte, hfail, Bool.false_eq_true, false_iff]
          omega

theorem maxNotesPerBar_correct (n : Nat) :
    (ruleChecker ctx (CallInfo.of call) (.maxNotesPerBar n)).accepts answer = true ↔
      RuleHolds ctx call answer (.maxNotesPerBar n) := by
  simp only [ruleChecker, RuleHolds, Checker.accepts, Checker.run]
  show ((maxNotesPerBarChecker n).runFrom 0 Mem.start answer).ok = true ↔ _
  rw [maxNotes_runFrom n 0 Mem.start answer rfl (Nat.zero_le _) (Nat.zero_le _)]
  simp [Mem.start, notes]

@[simp] theorem sayLess_step_rest (ci : CallInfo) (i : Nat) (m : Mem) :
    (sayLessChecker ci).step i m .rest = m := rfl
@[simp] theorem sayLess_step_note (ci : CallInfo) (i : Nat) (m : Mem) (p : Pitch) :
    (sayLessChecker ci).step i m (.note p) =
      if !m.ok then m
      else if m.count + 1 < ci.pitches.length then { count := m.count + 1 } else Mem.fail := rfl

theorem sayLess_runFrom (ci : CallInfo) (i : Nat) (m : Mem) (w : Phrase) (hm : m.ok = true) :
    (sayLessChecker ci).accept ((sayLessChecker ci).runFrom i m w) = true ↔
      m.count + (notesFrom i w).length < ci.pitches.length := by
  induction w generalizing i m with
  | nil => simp [Checker.runFrom, sayLessChecker, hm]
  | cons x w ih =>
    cases x with
    | rest =>
      simp only [Checker.runFrom, notesFrom_rest, sayLess_step_rest]
      exact ih (i + 1) m hm
    | note p =>
      simp only [Checker.runFrom, notesFrom_note, List.length_cons, sayLess_step_note, hm,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hn : m.count + 1 < ci.pitches.length
      · simp only [hn, ↓reduceIte]
        rw [ih (i + 1) { count := m.count + 1 } rfl]
        constructor <;> intro h <;> simp only at h ⊢ <;> omega
      · simp only [hn, ↓reduceIte]
        rw [runFrom_fail _ (fun i x => by cases x <;> simp [Mem.fail])]
        simp only [sayLessChecker, Mem.fail, Bool.false_and, Bool.false_eq_true, false_iff]
        omega

theorem sayLess_correct :
    (ruleChecker ctx (CallInfo.of call) .sayLess).accepts answer = true ↔
      RuleHolds ctx call answer .sayLess := by
  simp only [ruleChecker, RuleHolds, Checker.accepts, Checker.run]
  show (sayLessChecker (CallInfo.of call)).accept
    ((sayLessChecker (CallInfo.of call)).runFrom 0 Mem.start answer) = true ↔ _
  rw [sayLess_runFrom _ 0 Mem.start answer rfl]
  simp [Mem.start, notes, CallInfo.of, pitches]

end Counting

/-! ## First-note and last-note rules -/

section Memory
variable (ctx : Context) (call answer : Phrase)

@[simp] theorem startNearFrom_step_rest (c : Pitch) (k i : Nat) (m : Mem) :
    (startNearFrom c k).step i m .rest = m := rfl
@[simp] theorem startNearFrom_step_note (c : Pitch) (k i : Nat) (m : Mem) (p : Pitch) :
    (startNearFrom c k).step i m (.note p) =
      if m.ok && m.count == 0 then (if distance c p ≤ k then { count := 1 } else Mem.fail)
      else m := rfl

theorem startNearFrom_runFrom (c : Pitch) (k i : Nat) (w : Phrase) :
    ((startNearFrom c k).runFrom i Mem.start w).ok = true ↔
      ∀ a, ((notesFrom i w).map (·.2)).head? = some a → distance c a ≤ k := by
  induction w generalizing i with
  | nil => simp [Checker.runFrom, Mem.start]
  | cons x w ih =>
    cases x with
    | rest => simp only [Checker.runFrom, startNearFrom_step_rest, notesFrom_rest]; exact ih _
    | note p =>
      simp only [Checker.runFrom, startNearFrom_step_note, notesFrom_note, List.map_cons,
        List.head?_cons, Option.some.injEq]
      have hs : (Mem.start.ok && Mem.start.count == 0) = true := rfl
      simp only [hs, ↓reduceIte]
      by_cases hd : distance c p ≤ k
      · simp only [hd, ↓reduceIte]
        rw [runFrom_fixed _ _ (fun i x => by cases x <;> simp)]
        simp only [true_iff]
        rintro a rfl; exact hd
      · simp only [hd, ↓reduceIte]
        rw [runFrom_fail _ (fun i x => by cases x <;> simp [Mem.fail])]
        simp only [Mem.fail, Bool.false_eq_true, false_iff]
        intro h; exact hd (h p rfl)

theorem startNear_correct (k : Nat) :
    (ruleChecker ctx (CallInfo.of call) (.startNear k)).accepts answer = true ↔
      RuleHolds ctx call answer (.startNear k) := by
  simp only [ruleChecker, RuleHolds, startNearChecker, CallInfo.of]
  split
  · rename_i hlast
    simp only [alwaysPass_accepts, true_iff]
    intro c a hc; rw [hlast] at hc; cases hc
  · rename_i c hlast
    simp only [Checker.accepts, Checker.run]
    show ((startNearFrom c k).runFrom 0 Mem.start answer).ok = true ↔ _
    rw [startNearFrom_runFrom]
    simp only [pitches, notes] at hlast ⊢
    constructor
    · intro h c' a hc' ha; rw [hlast] at hc'; cases hc'; exact h a ha
    · intro h a ha; exact h c a hlast ha

@[simp] theorem maxLeap_step_rest (k i : Nat) (m : Mem) :
    (maxLeapChecker k).step i m .rest = m := rfl
@[simp] theorem maxLeap_step_note (k i : Nat) (m : Mem) (p : Pitch) :
    (maxLeapChecker k).step i m (.note p) =
      if !m.ok then m
      else match m.note with
        | none => { note := some p }
        | some l => if distance l p ≤ k then { note := some p } else Mem.fail := rfl

theorem maxLeap_runFrom_last (k : Nat) (l : Pitch) (i : Nat) (w : Phrase) :
    ((maxLeapChecker k).runFrom i { note := some l } w).ok = true ↔
      NoLeapBiggerThan k (l :: (notesFrom i w).map (·.2)) := by
  induction w generalizing i l with
  | nil => simp [Checker.runFrom, NoLeapBiggerThan]
  | cons x w ih =>
    cases x with
    | rest => simp only [Checker.runFrom, maxLeap_step_rest, notesFrom_rest]; exact ih _ _
    | note p =>
      simp only [Checker.runFrom, maxLeap_step_note, notesFrom_note, List.map_cons,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hd : distance l p ≤ k
      · simp only [hd, ↓reduceIte]
        rw [ih]
        simp [NoLeapBiggerThan, hd]
      · simp only [hd, ↓reduceIte]
        rw [runFrom_fail _ (fun i x => by cases x <;> simp [Mem.fail])]
        simp [Mem.fail, NoLeapBiggerThan, hd]

theorem maxLeap_runFrom_start (k i : Nat) (w : Phrase) :
    ((maxLeapChecker k).runFrom i Mem.start w).ok = true ↔
      NoLeapBiggerThan k ((notesFrom i w).map (·.2)) := by
  induction w generalizing i with
  | nil => simp [Checker.runFrom, Mem.start, NoLeapBiggerThan]
  | cons x w ih =>
    cases x with
    | rest => simp only [Checker.runFrom, maxLeap_step_rest, notesFrom_rest]; exact ih _
    | note p =>
      simp only [Checker.runFrom, maxLeap_step_note, notesFrom_note, List.map_cons]
      exact maxLeap_runFrom_last k p (i + 1) w

theorem maxLeap_correct (k : Nat) :
    (ruleChecker ctx (CallInfo.of call) (.maxLeap k)).accepts answer = true ↔
      RuleHolds ctx call answer (.maxLeap k) := by
  simp only [ruleChecker, RuleHolds, Checker.accepts, Checker.run]
  show ((maxLeapChecker k).runFrom 0 Mem.start answer).ok = true ↔ _
  rw [maxLeap_runFrom_start]
  rfl

end Memory

/-! ## Rules still being proven -/

/-- Note starts come in strictly increasing order. -/
theorem notesFrom_sorted (i : Nat) (w : Phrase) :
    ((notesFrom i w).map (·.1)).Pairwise (· < ·) := by
  induction w generalizing i with
  | nil => simp
  | cons x w ih =>
    cases x with
    | rest => simpa using ih (i + 1)
    | note p =>
      simp only [notesFrom_note, List.map_cons, List.pairwise_cons, List.mem_map]
      refine ⟨?_, ih (i + 1)⟩
      rintro _ ⟨⟨j, q⟩, hj, rfl⟩
      have := (notesFrom_slot_range (i + 1) w j q hj).1
      simp only; omega

/-- No slot appears twice among a phrase's note starts. -/
theorem onsetSlots_nodup (w : Phrase) : (onsetSlots w).Nodup :=
  (notesFrom_sorted 0 w).imp (fun h => Nat.ne_of_lt h)

@[simp] theorem echoSome_step_rest (ci : CallInfo) (k i : Nat) (m : Mem) :
    (echoSomeRhythmChecker ci k).step i m .rest = m := rfl
@[simp] theorem echoSome_step_note (ci : CallInfo) (k i : Nat) (m : Mem) (p : Pitch) :
    (echoSomeRhythmChecker ci k).step i m (.note p) =
      if ci.onsets.contains i then { count := min (m.count + 1) k } else m := rfl

theorem echoSome_runFrom (ci : CallInfo) (k i : Nat) (m : Mem) (w : Phrase) (hm : m.count ≤ k) :
    ((echoSomeRhythmChecker ci k).runFrom i m w).count =
      min (m.count + ((notesFrom i w).filter (fun jp => ci.onsets.contains jp.1)).length) k := by
  induction w generalizing i m with
  | nil => simp [Checker.runFrom]; omega
  | cons x w ih =>
    cases x with
    | rest => simp only [Checker.runFrom, echoSome_step_rest, notesFrom_rest]; exact ih _ _ hm
    | note p =>
      simp only [Checker.runFrom, echoSome_step_note, notesFrom_note, List.filter_cons]
      by_cases hc : ci.onsets.contains i
      · simp only [hc, ↓reduceIte, List.length_cons]
        rw [ih _ _ (by simp only; omega)]
        simp only; omega
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ih _ _ hm

theorem echoSomeRhythm_correct (ctx : Context) (call answer : Phrase) (k : Nat) :
    (ruleChecker ctx (CallInfo.of call) (.echoSomeRhythm k)).accepts answer = true ↔
      RuleHolds ctx call answer (.echoSomeRhythm k) := by
  simp only [ruleChecker, RuleHolds, Checker.accepts, Checker.run]
  show decide (k ≤ ((echoSomeRhythmChecker (CallInfo.of call) k).runFrom 0 Mem.start answer).count)
    = true ↔ _
  rw [echoSome_runFrom _ k 0 Mem.start answer (Nat.zero_le _)]
  simp only [decide_eq_true_eq, Mem.start, Nat.zero_add]
  -- Count matches from the answer's side, then switch to the call's side.
  have hA : ((notesFrom 0 answer).filter (fun jp => (CallInfo.of call).onsets.contains jp.1)).length
      = ((onsetSlots answer).filter (fun s => (onsetSlots call).contains s)).length := by
    simp [onsetSlots, notes, CallInfo.of, List.filter_map]
    rfl
  have hperm : ((onsetSlots answer).filter (fun s => (onsetSlots call).contains s)).Perm
      ((onsetSlots call).filter (· ∈ onsetSlots answer)) := by
    rw [List.perm_ext_iff_of_nodup ((onsetSlots_nodup answer).filter _)
      ((onsetSlots_nodup call).filter _)]
    intro a
    simp only [List.mem_filter, List.contains_iff_mem, decide_eq_true_eq]
    exact And.comm
  rw [hA, hperm.length_eq]
  constructor
  · intro h; omega
  · intro h; omega

/-- Two strictly increasing lists with the same members are the same list. -/
theorem eq_of_sorted_of_same_members : ∀ (l1 l2 : List Nat),
    l1.Pairwise (· < ·) → l2.Pairwise (· < ·) → (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp (by simp)) (by simp)
  | a :: t1, b :: t2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      have ha := (h a).mp (by simp)
      have hb := (h b).mpr (by simp)
      simp only [List.mem_cons] at ha hb
      rcases ha with ha | ha
      · exact ha
      · rcases hb with hb | hb
        · exact hb.symm
        · have := h2.1 a ha; have := h1.1 b hb; omega
    subst hab
    congr 1
    apply eq_of_sorted_of_same_members t1 t2 h1.2 h2.2
    intro x
    constructor
    · intro hx
      have := (h x).mp (by simp [hx])
      have hne : x ≠ a := Nat.ne_of_gt (h1.1 x hx)
      simpa [hne] using this
    · intro hx
      have := (h x).mpr (by simp [hx])
      have hne : x ≠ a := Nat.ne_of_gt (h2.1 x hx)
      simpa [hne] using this

theorem echoRhythm_step (ci : CallInfo) (i : Nat) (m : Mem) (x : Slot) :
    (echoRhythmChecker ci).step i m x =
      if m.ok && ((match x with | .note _ => true | .rest => false) != ci.onsets.contains i)
      then Mem.fail else m := rfl

theorem echoRhythm_runFrom (ci : CallInfo) (i : Nat) (m : Mem) (w : Phrase) :
    ((echoRhythmChecker ci).runFrom i m w).ok = true ↔
      m.ok = true ∧ ∀ s, i ≤ s → s < i + w.length →
        (s ∈ (notesFrom i w).map (·.1) ↔ s ∈ ci.onsets) := by
  induction w generalizing i m with
  | nil =>
    simp only [Checker.runFrom, List.length_nil, Nat.add_zero]
    constructor
    · intro h; exact ⟨h, fun s h1 h2 => absurd h2 (by omega)⟩
    · intro h; exact h.1
  | cons x w ih =>
    have hlater : i ∉ (notesFrom (i + 1) w).map (·.1) := by
      simp only [List.mem_map, not_exists, not_and]
      intro ⟨j, q⟩ hj hji
      have := (notesFrom_slot_range (i + 1) w j q hj).1
      simp only at hji; omega
    have hfail : ∀ j, ((echoRhythmChecker ci).runFrom j Mem.fail w).ok = false := by
      intro j
      rw [runFrom_fail _ (fun i x => by rw [echoRhythm_step]; simp [Mem.fail])]
      rfl
    cases hmb : m.ok with
    | false =>
      have : ((echoRhythmChecker ci).runFrom i m (x :: w)).ok = false := by
        rw [runFrom_fixed _ _ (fun i x => by rw [echoRhythm_step]; simp [hmb])]
        exact hmb
      simp [this]
    | true =>
    have hm : m.ok = true := hmb
    cases x with
    | rest =>
      have hstep : (echoRhythmChecker ci).step i m .rest =
          if i ∈ ci.onsets then Mem.fail else m := by
        rw [echoRhythm_step]
        by_cases hc : i ∈ ci.onsets <;> simp [hm, hc]
      simp only [Checker.runFrom, hstep, notesFrom_rest, List.length_cons]
      by_cases hc : i ∈ ci.onsets
      · simp only [hc, ↓reduceIte, hfail, Bool.false_eq_true, false_iff, not_and]
        intro _ h
        exact hlater ((h i (Nat.le_refl _) (by omega)).mpr hc)
      · simp only [hc, ↓reduceIte, ih, hm, true_and]
        constructor
        · intro h s hs1 hs2
          by_cases hsi : s = i
          · subst hsi; simp [hlater, hc]
          · exact h s (by omega) (by omega)
        · intro h s hs1 hs2; exact h s (by omega) (by omega)
    | note p =>
      have hstep : (echoRhythmChecker ci).step i m (.note p) =
          if i ∈ ci.onsets then m else Mem.fail := by
        rw [echoRhythm_step]
        by_cases hc : i ∈ ci.onsets <;> simp [hm, hc]
      simp only [Checker.runFrom, hstep, notesFrom_note, List.map_cons, List.length_cons,
        List.mem_cons]
      by_cases hc : i ∈ ci.onsets
      · simp only [hc, ↓reduceIte, ih, hm, true_and]
        constructor
        · intro h s hs1 hs2
          by_cases hsi : s = i
          · subst hsi; simp [hc]
          · have := h s (by omega) (by omega)
            simp [hsi, this]
        · intro h s hs1 hs2
          have := h s (by omega) (by omega)
          have hsi : s ≠ i := by omega
          simpa [hsi] using this
      · simp only [hc, ↓reduceIte, hfail, Bool.false_eq_true, false_iff, not_and]
        intro _ h
        exact hc ((h i (Nat.le_refl _) (by omega)).mp (Or.inl rfl))

theorem echoRhythm_correct (ctx : Context) (call answer : Phrase)
    (hlen : answer.length = phraseSlots) :
    (ruleChecker ctx (CallInfo.of call) .echoRhythm).accepts answer = true ↔
      RuleHolds ctx call answer .echoRhythm := by
  simp only [ruleChecker, RuleHolds, Checker.accepts, Checker.run]
  show ((echoRhythmChecker (CallInfo.of call)).runFrom 0
    (if (CallInfo.of call).onsets.all (· < phraseSlots) then Mem.start else Mem.fail)
      answer).ok = true ↔ _
  rw [echoRhythm_runFrom]
  simp only [hlen, Nat.zero_add, Nat.zero_le, true_imp_iff, CallInfo.of]
  have hA : ∀ s, s ∈ onsetSlots answer → s < phraseSlots := by
    intro s hs
    simp only [onsetSlots, notes, List.mem_map] at hs
    obtain ⟨⟨j, q⟩, hj, rfl⟩ := hs
    have := (notesFrom_slot_range 0 answer j q hj).2
    simp only; omega
  constructor
  · rintro ⟨hinit, hsame⟩
    have hC : ∀ c ∈ onsetSlots call, c < phraseSlots := by
      by_cases hall : ((onsetSlots call).all fun x => decide (x < phraseSlots)) = true
      · simpa using hall
      · simp [hall, Mem.fail] at hinit
    apply eq_of_sorted_of_same_members _ _ (notesFrom_sorted 0 answer) (notesFrom_sorted 0 call)
    intro x
    by_cases hx : x < phraseSlots
    · exact hsame x hx
    · constructor
      · intro h; exact absurd (hA x h) hx
      · intro h; exact absurd (hC x h) hx
  · intro heq
    refine ⟨?_, fun s _ => by rw [show (notesFrom 0 answer).map (·.1) = onsetSlots answer from rfl, heq]⟩
    have hall : (onsetSlots call).all (· < phraseSlots) = true := by
      simp only [List.all_eq_true, decide_eq_true_eq]
      intro c hc; rw [← heq] at hc; exact hA c hc
    simp [hall, Mem.start]

/-! ### Sequence -/

section Sequence
variable (ci : CallInfo) (n : Nat)

/-- The sequence checker's step on a note (it ignores the slot number). -/
def seqStep (m : Mem) (p : Pitch) : Mem := (sequenceChecker ci n).step 0 m (.note p)

/-- Sequence ignores rests and slot numbers: running it is a loop over the notes. -/
theorem sequence_runFrom (i : Nat) (m : Mem) (w : Phrase) :
    (sequenceChecker ci n).runFrom i m w = ((notesFrom i w).map (·.2)).foldl (seqStep ci n) m := by
  induction w generalizing i m with
  | nil => rfl
  | cons x w ih =>
    cases x with
    | rest => exact ih (i + 1) m
    | note p => exact ih (i + 1) _

theorem seqStep_fixed (m : Mem) (h : m.ok = false ∨ n ≤ m.count) (p : Pitch) :
    seqStep ci n m p = m := by
  rcases h with h | h <;> simp [seqStep, sequenceChecker, h]

theorem foldl_seqStep_fixed (m : Mem) (h : m.ok = false ∨ n ≤ m.count) (ps : List Pitch) :
    ps.foldl (seqStep ci n) m = m := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.foldl_cons, seqStep_fixed ci n m h, ih]

/-- The sequence checker passes a memory: not failed, all `n` notes matched,
and the call has at least `n` notes. -/
def seqAccept (m : Mem) : Prop := m.ok = true ∧ n ≤ m.count ∧ n ≤ ci.pitches.length

theorem seqAccept_iff (m : Mem) : (sequenceChecker ci n).accept m = true ↔ seqAccept ci n m := by
  simp [sequenceChecker, seqAccept, and_assoc]

/-- After matching `j` notes with shift `sh`, the rest passes exactly when the
next `n - j` notes are the matching call notes moved by `sh`, and `sh` is not 0. -/
theorem seq_after (j : Nat) (sh : Int) (hj : j < n) (ps : List Pitch) :
    seqAccept ci n (ps.foldl (seqStep ci n) { count := j, shift := some sh }) ↔
      n ≤ ci.pitches.length ∧ n - j ≤ ps.length ∧ sh ≠ 0 ∧
      (ps.take (n - j)).map (fun (p : Pitch) => (p : Int)) =
        ((ci.pitches.drop j).take (n - j)).map (fun (p : Pitch) => (p : Int) + sh) := by
  induction ps generalizing j with
  | nil =>
    simp only [List.foldl_nil, seqAccept, List.length_nil]
    constructor
    · rintro ⟨-, h, -⟩; omega
    · rintro ⟨-, h, -⟩; omega
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have hfail : ¬ seqAccept ci n (ps.foldl (seqStep ci n) Mem.fail) := by
      rw [foldl_seqStep_fixed ci n _ (Or.inl rfl)]
      simp [seqAccept, Mem.fail]
    by_cases hjc : j < ci.pitches.length
    · have hdrop := List.drop_eq_getElem_cons hjc
      set_option linter.unusedSimpArgs false in
      have hget : ci.pitches[j]? = some ci.pitches[j] := List.getElem?_eq_getElem hjc
      have hn : n - j = (n - (j + 1)) + 1 := by omega
      rw [hdrop, hn]
      simp only [List.take_succ_cons, List.map_cons, List.cons.injEq, List.length_cons]
      by_cases hp : (p : Int) = ci.pitches[j] + sh
      · by_cases hjn : n ≤ j + 1
        · have hnj : n - (j + 1) = 0 := by omega
          simp only [hnj, List.take_zero, List.map_nil, and_true, hp]
          by_cases hsh : sh = 0
          · have hstep : seqStep ci n { count := j, shift := some sh } p = Mem.fail := by
              simp [seqStep, sequenceChecker, hget, hp, Nat.not_le.mpr hj, hjn, hsh]
            rw [hstep]
            simp only [hfail, hsh, ne_eq, not_true_eq_false, false_and, and_false]
          · have hstep : seqStep ci n { count := j, shift := some sh } p = { count := j + 1 } := by
              simp [seqStep, sequenceChecker, hget, hp, Nat.not_le.mpr hj, hjn, hsh]
            rw [hstep, foldl_seqStep_fixed ci n _ (Or.inr (by simp only; omega))]
            simp only [seqAccept, true_and, hsh, ne_eq, not_false_eq_true, and_true]
            constructor
            · intro h; exact ⟨h.2, by omega⟩
            · intro h; exact ⟨by omega, h.1⟩
        · have hstep : seqStep ci n { count := j, shift := some sh } p =
              { count := j + 1, shift := some sh } := by
            simp [seqStep, sequenceChecker, hget, hp, Nat.not_le.mpr hj, hjn]
          rw [hstep]
          simp only [hp, true_and]
          rw [ih (j + 1) (by omega)]
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h3⟩
          · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h3⟩
      · have hstep : seqStep ci n { count := j, shift := some sh } p = Mem.fail := by
          simp [seqStep, sequenceChecker, hget, hp, Nat.not_le.mpr hj]
        rw [hstep]
        simp only [hp, false_and, and_false, iff_false]
        exact hfail
    · have hget : ci.pitches[j]? = none := List.getElem?_eq_none (by omega)
      have hstep : seqStep ci n { count := j, shift := some sh } p = Mem.fail := by
        simp [seqStep, sequenceChecker, hget, Nat.not_le.mpr hj]
      rw [hstep]
      simp only [hfail, false_iff, not_and]
      intro h; omega

/-- From the start: the answer passes exactly when its first `n` notes are the
call's first `n` notes moved by one shift that is not 0. -/
theorem seq_start (ps : List Pitch) :
    seqAccept ci n (ps.foldl (seqStep ci n) Mem.start) ↔
      n ≤ ci.pitches.length ∧ n ≤ ps.length ∧
      ∃ sh : Int, sh ≠ 0 ∧ (ps.take n).map (fun (p : Pitch) => (p : Int)) =
        (ci.pitches.take n).map (fun (p : Pitch) => (p : Int) + sh) := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [foldl_seqStep_fixed ci 0 _ (Or.inr (Nat.zero_le _))]
    simp only [seqAccept, Mem.start, Nat.zero_le, List.take_zero, List.map_nil, and_true,
      true_and, ne_eq]
    exact ⟨fun _ => ⟨1, by decide⟩, fun _ => trivial⟩
  cases ps with
  | nil =>
    simp only [List.foldl_nil, seqAccept, Mem.start, List.length_nil]
    constructor
    · rintro ⟨-, h, -⟩; omega
    · rintro ⟨-, h, -⟩; omega
  | cons p ps =>
    simp only [List.foldl_cons, List.length_cons]
    have hfail : ¬ seqAccept ci n (ps.foldl (seqStep ci n) Mem.fail) := by
      rw [foldl_seqStep_fixed ci n _ (Or.inl rfl)]
      simp [seqAccept, Mem.fail]
    by_cases hc : 0 < ci.pitches.length
    · have hget : ci.pitches[0]? = some ci.pitches[0] := List.getElem?_eq_getElem hc
      have hdrop := List.drop_eq_getElem_cons hc
      have htake : ci.pitches.take n = ci.pitches[0] :: (ci.pitches.drop 1).take (n - 1) := by
        conv => lhs; rw [← List.drop_zero (l := ci.pitches), hdrop]
        rw [show n = (n - 1) + 1 by omega, List.take_succ_cons]
        simp
      have htake' : (p :: ps).take n = p :: ps.take (n - 1) := by
        rw [show n = (n - 1) + 1 by omega, List.take_succ_cons]
        simp
      rw [htake, htake']
      simp only [List.map_cons, List.cons.injEq]
      by_cases hn1 : n ≤ 1
      · have hn1' : n = 1 := by omega
        subst hn1'
        simp only [Nat.sub_self, List.take_zero, List.map_nil, and_true]
        by_cases hsh : (p : Int) - ci.pitches[0] = 0
        · have hstep : seqStep ci 1 Mem.start p = Mem.fail := by
            simp [seqStep, sequenceChecker, Mem.start, hget, hsh]
          rw [hstep]
          simp only [hfail, false_iff, not_and, not_exists]
          intro _ _ sh hsh0 hp
          omega
        · have hstep : seqStep ci 1 Mem.start p = { count := 1 } := by
            simp [seqStep, sequenceChecker, Mem.start, hget, hsh]
            omega
          rw [hstep, foldl_seqStep_fixed ci 1 _ (Or.inr (Nat.le_refl _))]
          simp only [seqAccept, true_and, Nat.le_refl]
          constructor
          · intro h; exact ⟨h, by omega, (p : Int) - ci.pitches[0], hsh, by omega⟩
          · intro h; exact h.1
      · have hstep : seqStep ci n Mem.start p =
            { count := 1, shift := some ((p : Int) - ci.pitches[0]) } := by
          simp [seqStep, sequenceChecker, Mem.start, hget, hn0, hn1]
          omega
        rw [hstep, seq_after ci n 1 _ (by omega)]
        constructor
        · rintro ⟨h1, h2, hsh, h3⟩
          exact ⟨h1, by omega, (p : Int) - ci.pitches[0], hsh, by omega, h3⟩
        · rintro ⟨h1, h2, sh, hsh, hp, h3⟩
          have : sh = (p : Int) - ci.pitches[0] := by omega
          subst this
          exact ⟨h1, by omega, hsh, h3⟩
    · have hget : ci.pitches[0]? = none := List.getElem?_eq_none (by omega)
      have hstep : seqStep ci n Mem.start p = Mem.fail := by
        simp [seqStep, sequenceChecker, Mem.start, hget, hn0]
      rw [hstep]
      simp only [hfail, false_iff, not_and]
      intro h; omega

end Sequence

theorem sequence_correct (ctx : Context) (call answer : Phrase) (n : Nat) :
    (ruleChecker ctx (CallInfo.of call) (.sequence n)).accepts answer = true ↔
      RuleHolds ctx call answer (.sequence n) := by
  simp only [ruleChecker, RuleHolds, Checker.accepts, Checker.run]
  show (sequenceChecker (CallInfo.of call) n).accept
    ((sequenceChecker (CallInfo.of call) n).runFrom 0 Mem.start answer) = true ↔ _
  rw [seqAccept_iff, sequence_runFrom, seq_start]
  rfl

end Blues
