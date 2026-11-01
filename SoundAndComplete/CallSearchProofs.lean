import SoundAndComplete.CallSearch
import SoundAndComplete.CheckerProofs

/-!
# Proofs for `findCall`

Two facts, used by `findCall_sound` and `findCall_complete` in `Theorems.lean`:

* `bestCallChecker_sound`: if `bestCallChecker` passes an answer, the answer
  is playable, the best call is playable, and the answer obeys every rule
  against the best call.
* `bestCallChecker_complete`: if some playable call has an answer, then
  `bestCallChecker` passes that same answer for one of the shifts we try.
-/

namespace Blues

/-! ## Small facts about lists of notes -/

theorem notesFrom_length_le (i : Nat) (w : Phrase) : (notesFrom i w).length ≤ w.length := by
  induction w generalizing i with
  | nil => simp
  | cons x w ih =>
    have := ih (i + 1)
    cases x <;> simp only [notesFrom_rest, notesFrom_note, List.length_cons] <;> omega

theorem pitches_length (w : Phrase) : (pitches w).length = (notes w).length := by
  simp [pitches]

theorem onsetSlots_length (w : Phrase) : (onsetSlots w).length = (notes w).length := by
  simp [onsetSlots]

theorem notes_length_le (w : Phrase) : (notes w).length ≤ w.length := notesFrom_length_le 0 w

/-- The same case split as `ruleChecker_correct` in `Theorems.lean`. -/
theorem ruleChecker_accepts_iff (ctx : Context) (call answer : Phrase) (r : Rule)
    (hlen : answer.length = phraseSlots) :
    (ruleChecker ctx (CallInfo.of call) r).accepts answer = true ↔
      RuleHolds ctx call answer r := by
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

/-! ## `fillNotes` keeps the rhythm and uses the given notes -/

theorem fillNotes_length (ps : List Pitch) (w : Phrase) : (fillNotes ps w).length = w.length := by
  induction w generalizing ps with
  | nil => simp [fillNotes]
  | cons x w ih =>
    cases x with
    | rest => simp [fillNotes, ih]
    | note q => cases ps <;> simp [fillNotes, ih]

theorem fillNotes_notes (i : Nat) (ps : List Pitch) (w : Phrase)
    (h : (notesFrom i w).length ≤ ps.length) :
    (notesFrom i (fillNotes ps w)).map (·.1) = (notesFrom i w).map (·.1) ∧
    (notesFrom i (fillNotes ps w)).map (·.2) = ps.take (notesFrom i w).length := by
  induction w generalizing i ps with
  | nil => simp [fillNotes]
  | cons x w ih =>
    cases x with
    | rest =>
      simp only [fillNotes, notesFrom_rest] at h ⊢
      exact ih (i + 1) ps h
    | note q =>
      cases ps with
      | nil => simp at h
      | cons p ps =>
        simp only [fillNotes, notesFrom_note, List.length_cons, List.map_cons,
          List.take_succ_cons, List.cons.injEq, true_and] at h ⊢
        exact ih (i + 1) ps (by omega)

/-! ## The full call -/

theorem fullCall_length : fullCall.length = phraseSlots := by simp [fullCall]

theorem fullCall_onsets : onsetSlots fullCall = List.range phraseSlots := by decide

theorem fullCall_notes_length : (notes fullCall).length = phraseSlots := by decide

/-- Every note start of a 24-slot answer is one of the 24 slots. -/
theorem range_filter_onsets (a : Phrase) (hlen : a.length = phraseSlots) :
    ((List.range phraseSlots).filter (· ∈ onsetSlots a)).length = (onsetSlots a).length := by
  apply Nat.le_antisymm
  · apply List.Nodup.length_le_of_subset (List.nodup_range.filter _)
    intro x hx
    simpa using (List.mem_filter.mp hx).2
  · apply List.Nodup.length_le_of_subset (onsetSlots_nodup a)
    intro x hx
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    refine ⟨?_, hx⟩
    simp only [onsetSlots, notes, List.mem_map] at hx
    obtain ⟨⟨j, p⟩, hj, rfl⟩ := hx
    have := (notesFrom_slot_range 0 a j p hj).2
    simpa [hlen] using this

/-- Against the full call, `echoSomeRhythm k` means: at least `k` notes. -/
theorem fullCall_echoSome (ctx : Context) (a : Phrase) (k : Nat) (hlen : a.length = phraseSlots) :
    (ruleChecker ctx (CallInfo.of fullCall) (.echoSomeRhythm k)).accepts a = true ↔
      k ≤ (pitches a).length := by
  rw [echoSomeRhythm_correct]
  simp only [RuleHolds, fullCall_onsets]
  rw [range_filter_onsets a hlen, onsetSlots_length, pitches_length]

/-- Against the full call, `sayLess` means: fewer than 24 notes. -/
theorem fullCall_sayLess (ctx : Context) (a : Phrase) :
    (ruleChecker ctx (CallInfo.of fullCall) .sayLess).accepts a = true ↔
      (pitches a).length < phraseSlots := by
  rw [sayLess_correct]
  simp only [RuleHolds, fullCall_notes_length, pitches_length]

/-! ## `seqLength` and the shifts -/

theorem le_seqLength (rules : List Rule) (n : Nat) (h : Rule.sequence n ∈ rules) :
    n ≤ seqLength rules := by
  induction rules with
  | nil => simp at h
  | cons r rs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [seqLength]; omega
    · have := ih h
      cases r <;> simp only [seqLength] <;> omega

theorem seqLength_mem (rules : List Rule) :
    seqLength rules = 0 ∨ Rule.sequence (seqLength rules) ∈ rules := by
  induction rules with
  | nil => simp [seqLength]
  | cons r rs ih =>
    cases r with
    | sequence n =>
      simp only [seqLength]
      by_cases hn : seqLength rs ≤ n
      · rw [Nat.max_eq_left hn]; right; simp
      · rw [Nat.max_eq_right (by omega)]
        rcases ih with h | h
        · omega
        · right; exact List.mem_cons_of_mem _ h
    | _ =>
      simp only [seqLength]
      rcases ih with h | h
      · left; exact h
      · right; exact List.mem_cons_of_mem _ h

theorem callShifts_ne_zero (rules : List Rule) : ∀ s ∈ callShifts rules, s ≠ 0 := by
  intro s hs
  simp only [callShifts] at hs
  split at hs
  · simp at hs; omega
  · split at hs
    · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hs
      obtain ⟨i, -, h | h⟩ := hs <;> omega
    · simp at hs; omega

theorem mem_callShifts (rules : List Rule) (s : Int) (h0 : s ≠ 0)
    (h1 : -(guitarHigh - guitarLow : Nat) ≤ s) (h2 : s ≤ (guitarHigh - guitarLow : Nat))
    (hN : seqLength rules ≠ 0) (hall : needsAllShifts rules = true) : s ∈ callShifts rules := by
  simp only [callShifts, hN, hall, ↓reduceIte, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  simp only [guitarHigh, guitarLow] at h1 h2 ⊢
  by_cases hpos : 0 < s
  · exact ⟨s.toNat - 1, by omega, Or.inl (by omega)⟩
  · exact ⟨(-s).toNat - 1, by omega, Or.inr (by omega)⟩

theorem one_mem_callShifts (rules : List Rule) : (1 : Int) ∈ callShifts rules := by
  simp only [callShifts]
  split
  · simp
  · split
    · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨0, by simp [guitarHigh, guitarLow], Or.inl rfl⟩
    · simp

theorem neg_one_mem_callShifts (rules : List Rule) (hN : seqLength rules ≠ 0) :
    (-1 : Int) ∈ callShifts rules := by
  simp only [callShifts, hN, ↓reduceIte]
  split
  · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨0, by simp [guitarHigh, guitarLow], Or.inr rfl⟩
  · simp

/-! ## Checkers that ignore rests and slot numbers -/

/-- A checker that ignores rests and slot numbers is a loop over the notes. -/
theorem runFrom_eq_foldl (c : Checker Mem) (f : Mem → Pitch → Mem)
    (hr : ∀ i m, c.step i m .rest = m) (hn : ∀ i m p, c.step i m (.note p) = f m p)
    (i : Nat) (m : Mem) (w : Phrase) :
    c.runFrom i m w = ((notesFrom i w).map (·.2)).foldl f m := by
  induction w generalizing i m with
  | nil => rfl
  | cons x w ih =>
    cases x with
    | rest => simp only [Checker.runFrom, hr, notesFrom_rest]; exact ih _ _
    | note p => simp only [Checker.runFrom, hn, notesFrom_note, List.map_cons, List.foldl_cons]; exact ih _ _

/-! ## The "shifted notes on the guitar" checker -/

section Shifted
variable (n : Nat) (s : Int)

/-- Its memory after reading notes `ps`. -/
def gState (ps : List Pitch) : Mem :=
  if (ps.take n).all (shiftedOnGuitar s) then { count := min ps.length n } else Mem.fail

def gStep (m : Mem) (p : Pitch) : Mem := (shiftedOnGuitarChecker n s).step 0 m (.note p)

theorem gState_snoc (ps : List Pitch) (p : Pitch) :
    gStep n s (gState n s ps) p = gState n s (ps ++ [p]) := by
  unfold gStep gState
  by_cases hall : (ps.take n).all (shiftedOnGuitar s) = true
  · by_cases hn : n ≤ ps.length
    · have ht : (ps ++ [p]).take n = ps.take n := List.take_append_of_le_length hn
      have h1 : min ps.length n = n := by omega
      have h2 : min (ps.length + 1) n = n := by omega
      simp [shiftedOnGuitarChecker, hall, ht, h1, h2]
    · have ht : (ps ++ [p]).take n = ps ++ [p] := List.take_of_length_le (by simp; omega)
      have ht' : ps.take n = ps := List.take_of_length_le (by omega)
      rw [ht'] at hall
      have h1 : min ps.length n = ps.length := by omega
      have h2 : min (ps.length + 1) n = ps.length + 1 := by omega
      cases hp : shiftedOnGuitar s p <;>
        simp [shiftedOnGuitarChecker, hall, ht, ht', h1, h2, hp, Nat.not_le.mpr (by omega : ps.length < n)]
  · have hall' : ((ps ++ [p]).take n).all (shiftedOnGuitar s) = false := by
      rw [List.take_append, List.all_append]
      simp only [Bool.not_eq_true] at hall
      simp [hall]
    simp only [Bool.not_eq_true] at hall
    simp [shiftedOnGuitarChecker, hall, hall', Mem.fail]

theorem foldl_gStep (ps qs : List Pitch) :
    qs.foldl (gStep n s) (gState n s ps) = gState n s (ps ++ qs) := by
  induction qs generalizing ps with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons, gState_snoc, ih]
    simp

theorem shiftedOnGuitarChecker_accepts (w : Phrase) :
    (shiftedOnGuitarChecker n s).accepts w = true ↔
      ∀ p ∈ (pitches w).take n, shiftedOnGuitar s p = true := by
  have h0 : gState n s [] = Mem.start := by simp [gState, Mem.start]
  simp only [Checker.accepts, Checker.run]
  rw [runFrom_eq_foldl _ (gStep n s) (fun _ _ => rfl) (fun _ _ _ => rfl)]
  show (shiftedOnGuitarChecker n s).accept ((pitches w).foldl (gStep n s) Mem.start) = true ↔ _
  rw [← h0, foldl_gStep, List.nil_append]
  simp only [shiftedOnGuitarChecker, gState]
  split
  · rename_i h; simp only [List.all_eq_true] at h; simpa using h
  · rename_i h; simp only [List.all_eq_true] at h; simpa [Mem.fail] using h

theorem shiftedOnGuitarChecker_deadIsFinal : (shiftedOnGuitarChecker n s).DeadIsFinal :=
  deadIsFinal_of_fail _ (fun _ => rfl)
    (fun i m x hm => by cases x <;> simp [shiftedOnGuitarChecker, hm])
    (fun m hm => by simp [shiftedOnGuitarChecker, hm])

end Shifted

/-! ## The `startNear` checker for the best call -/

section StartNear
variable (n : Nat) (s : Int) (k : Nat) (restOk : Bool)

/-- What `startNearShifted` checks, on the answer's notes. -/
def SNCond (ps : List Pitch) : Prop :=
  n < ps.length ∨ (restOk = true ∧ ps.length < phraseSlots) ∨
  ∃ f l, ps.head? = some f ∧ ps.getLast? = some l ∧ distance (shiftDown s l) f ≤ k

/-- The latest note, moved down by `s`, is within `k` frets of the first note. -/
def lastNear (ps : List Pitch) : Bool :=
  match ps.head?, ps.getLast? with
  | some f, some l => decide (distance (shiftDown s l) f ≤ k)
  | _, _ => false

theorem lastNear_iff (ps : List Pitch) :
    lastNear s k ps = true ↔
      ∃ f l, ps.head? = some f ∧ ps.getLast? = some l ∧ distance (shiftDown s l) f ≤ k := by
  unfold lastNear
  cases ps.head? <;> cases ps.getLast? <;> simp

/-- Its memory after reading notes `ps`. -/
def snState (ps : List Pitch) : Mem :=
  if n < ps.length then { count := n + 1 }
  else { count := ps.length, note := ps.head?, count2 := if lastNear s k ps then 1 else 0 }

def snStep (m : Mem) (p : Pitch) : Mem := (startNearShifted n s k restOk).step 0 m (.note p)

theorem snState_snoc (ps : List Pitch) (p : Pitch) :
    snStep n s k restOk (snState n s k ps) p = snState n s k (ps ++ [p]) := by
  unfold snStep snState
  by_cases h1 : n < ps.length
  · have : n < ps.length + 1 := by omega
    simp [startNearShifted, h1, this]
  · by_cases h2 : ps.length = n
    · subst h2
      simp [startNearShifted]
    · have h3 : ¬ n < ps.length + 1 := by omega
      have h4 : ¬ n ≤ ps.length := by omega
      have hhead : (ps ++ [p]).head? = some (ps.head?.getD p) := by cases ps <;> simp
      have hlast : lastNear s k (ps ++ [p]) = decide (distance (shiftDown s p) (ps.head?.getD p) ≤ k) := by
        unfold lastNear; rw [hhead]; simp
      simp only [startNearShifted, h1, h3, h4, ↓reduceIte, List.length_append, List.length_cons,
        List.length_nil, hhead, hlast]
      by_cases hd : distance (shiftDown s p) (ps.head?.getD p) ≤ k <;> simp [hd]

theorem foldl_snStep (ps qs : List Pitch) :
    qs.foldl (snStep n s k restOk) (snState n s k ps) = snState n s k (ps ++ qs) := by
  induction qs generalizing ps with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons, snState_snoc, ih]
    simp

theorem startNearShifted_accepts (w : Phrase) :
    (startNearShifted n s k restOk).accepts w = true ↔ SNCond n s k restOk (pitches w) := by
  have h0 : snState n s k [] = Mem.start := by simp [snState, lastNear, Mem.start]
  simp only [Checker.accepts, Checker.run]
  rw [runFrom_eq_foldl _ (snStep n s k restOk) (fun _ _ => rfl) (fun _ _ _ => rfl)]
  show (startNearShifted n s k restOk).accept
    ((pitches w).foldl (snStep n s k restOk) Mem.start) = true ↔ _
  rw [← h0, foldl_snStep, List.nil_append]
  unfold SNCond
  simp only [startNearShifted, snState]
  split
  · rename_i h; simp [h]
  · rename_i h
    rw [← lastNear_iff]
    cases lastNear s k (pitches w) <;> simp [h]

theorem startNearShifted_deadIsFinal : (startNearShifted n s k restOk).DeadIsFinal :=
  deadIsFinal_of_never_dead _ (fun _ => rfl)

end StartNear

/-! ## The best call -/

section BestCall
variable (rules : List Rule) (s : Int) (a : Phrase)

/-- The rhythm of the best call. -/
abbrev bestRhythm : Phrase := if rules.contains .echoRhythm then a else fullCall

theorem bestRhythm_length (hlen : a.length = phraseSlots) :
    (bestRhythm rules a).length = phraseSlots := by
  unfold bestRhythm; split
  · exact hlen
  · exact fullCall_length

theorem bestCallNotes_length (n : Nat) (ps : List Pitch) :
    phraseSlots ≤ (bestCallNotes n s ps).length := by
  simp [bestCallNotes]

theorem bestCall_eq : bestCall rules s a =
    fillNotes (bestCallNotes (seqLength rules) s (pitches a)) (bestRhythm rules a) := rfl

theorem bestCall_notes (hlen : a.length = phraseSlots) :
    onsetSlots (bestCall rules s a) = onsetSlots (bestRhythm rules a) ∧
    pitches (bestCall rules s a) =
      (bestCallNotes (seqLength rules) s (pitches a)).take (notes (bestRhythm rules a)).length := by
  have h : (notesFrom 0 (bestRhythm rules a)).length ≤
      (bestCallNotes (seqLength rules) s (pitches a)).length := by
    have := notesFrom_length_le 0 (bestRhythm rules a)
    have := bestCallNotes_length s (seqLength rules) (pitches a)
    rw [bestRhythm_length rules a hlen] at *
    omega
  exact fillNotes_notes 0 _ _ h

theorem bestCall_length (hlen : a.length = phraseSlots) :
    (bestCall rules s a).length = phraseSlots := by
  rw [bestCall_eq, fillNotes_length, bestRhythm_length rules a hlen]

/-- The number of notes of the best call: the answer's count with
`echoRhythm`, otherwise 24. -/
theorem bestRhythm_count :
    (notes (bestRhythm rules a)).length =
      if rules.contains .echoRhythm then (pitches a).length else phraseSlots := by
  unfold bestRhythm
  split
  · rw [pitches_length]
  · exact fullCall_notes_length

end BestCall

/-! ## The best call's notes, one by one -/

theorem bestCallNotes_get_lt (n : Nat) (s : Int) (ps : List Pitch) (i : Nat)
    (hi : i < min n ps.length) :
    (bestCallNotes n s ps)[i]? = ps[i]?.map (shiftDown s) := by
  unfold bestCallNotes
  rw [List.getElem?_append_left (by simp; omega)]
  simp only [List.getElem?_map, List.getElem?_take]
  simp [show i < n by omega]

theorem bestCallNotes_get_ge (n : Nat) (s : Int) (ps : List Pitch) (i : Nat)
    (hi : min n ps.length ≤ i) (hi2 : i < min n ps.length + phraseSlots) :
    (bestCallNotes n s ps)[i]? = some (ps.headD 60) := by
  unfold bestCallNotes
  rw [List.getElem?_append_right (by simp; omega)]
  simp [List.getElem?_replicate]
  omega

theorem shiftedOnGuitar_iff (s : Int) (p : Pitch) (h : shiftedOnGuitar s p = true) :
    OnGuitar (shiftDown s p) ∧ ((shiftDown s p : Nat) : Int) + s = p := by
  unfold shiftedOnGuitar at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  have e1 : ((guitarLow : Nat) : Int) = 40 := rfl
  have e2 : ((guitarHigh : Nat) : Int) = 88 := rfl
  rw [e1, e2] at h
  -- `Pitch` is `Nat`, but `omega` only reads `Nat` written as `Nat`.
  have key : ∀ x : Int, 40 ≤ x → x ≤ 88 →
      (40 ≤ x.toNat ∧ x.toNat ≤ 88) ∧ ((x.toNat : Nat) : Int) = x := by
    intro x h1 h2; omega
  obtain ⟨h1, h2⟩ := key _ h.1 h.2
  refine ⟨h1, ?_⟩
  unfold shiftDown
  rw [h2]
  omega

theorem distance_self (p : Pitch) : distance p p = 0 := by simp [distance]

theorem headD_of_head? (ps : List Pitch) (f d : Pitch) (h : ps.head? = some f) : ps.headD d = f := by
  cases ps <;> simp_all

theorem contains_echo_iff (rules : List Rule) :
    rules.contains .echoRhythm = true ↔ Rule.echoRhythm ∈ rules := by
  simp

/-! ## Sound: what the checker passes really works -/

/-- The best call is playable when its shifted notes are on the guitar. -/
theorem bestCall_playable (rules : List Rule) (s : Int) (a : Phrase) (hplay : Playable a)
    (hG : ∀ p ∈ (pitches a).take (seqLength rules), shiftedOnGuitar s p = true) :
    Playable (bestCall rules s a) := by
  have hlen := hplay.1
  obtain ⟨-, hpi⟩ := bestCall_notes rules s a hlen
  have hK := bestRhythm_count rules a
  have hL := bestCallNotes_length s (seqLength rules) (pitches a)
  have hm : 1 ≤ (pitches a).length := by
    rw [pitches_length]; exact List.length_pos_iff.mpr hplay.2.1
  have hm24 : (pitches a).length ≤ phraseSlots := by
    rw [pitches_length, ← hlen]; exact notes_length_le a
  refine ⟨bestCall_length rules s a hlen, ?_, ?_⟩
  · intro h
    have : (pitches (bestCall rules s a)).length = 0 := by simp [pitches, h]
    rw [hpi, List.length_take, hK] at this
    split at this <;> simp only [phraseSlots] at * <;> omega
  · intro p hp
    rw [hpi] at hp
    have hp := List.mem_of_mem_take hp
    simp only [bestCallNotes, List.mem_append, List.mem_map, List.mem_replicate] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨-, rfl⟩
    · exact (shiftedOnGuitar_iff s q (hG q hq)).1
    · obtain ⟨f, hf⟩ : ∃ f, (pitches a).head? = some f := by
        cases h : pitches a with
        | nil => rw [h] at hm; simp at hm
        | cons f _ => exact ⟨f, rfl⟩
      rw [headD_of_head? _ f 60 hf]
      exact hplay.2.2 f (List.mem_of_mem_head? hf)

/-- If an answer passes a rule's checker for the best call, it obeys that rule
against the best call. -/
theorem bestCall_rule_holds (ctx : Context) (rules : List Rule) (s : Int) (a : Phrase)
    (hplay : Playable a)
    (hG : ∀ p ∈ (pitches a).take (seqLength rules), shiftedOnGuitar s p = true)
    (hs : s ≠ 0) (r : Rule) (hr : r ∈ rules)
    (hacc : (bestCallRuleChecker ctx rules s r).accepts a = true) :
    RuleHolds ctx (bestCall rules s a) a r := by
  have hlen := hplay.1
  obtain ⟨hon, hpi⟩ := bestCall_notes rules s a hlen
  have hK := bestRhythm_count rules a
  have hL := bestCallNotes_length s (seqLength rules) (pitches a)
  have hm : 1 ≤ (pitches a).length := by
    rw [pitches_length]; exact List.length_pos_iff.mpr hplay.2.1
  have hm24 : (pitches a).length ≤ phraseSlots := by
    rw [pitches_length, ← hlen]; exact notes_length_le a
  -- The best call has `K` notes.
  have hKm : (pitches a).length ≤ (notes (bestRhythm rules a)).length ∧
      (notes (bestRhythm rules a)).length ≤ phraseSlots := by
    rw [hK]; split <;> omega
  have hcount : (pitches (bestCall rules s a)).length = (notes (bestRhythm rules a)).length := by
    rw [hpi, List.length_take]; omega
  cases r with
  | echoRhythm =>
    have hc : rules.contains .echoRhythm = true := (contains_echo_iff rules).mpr hr
    simp only [RuleHolds, hon, bestRhythm, hc, ite_true]
  | echoSomeRhythm k =>
    have hk := (fullCall_echoSome ctx a k hlen).mp hacc
    simp only [RuleHolds, hon, bestRhythm]
    split
    · rw [List.filter_eq_self.mpr (by simp), onsetSlots_length, ← pitches_length]; exact hk
    · rw [fullCall_onsets, range_filter_onsets a hlen, onsetSlots_length, ← pitches_length]
      exact hk
  | sequence n =>
    have hn := (fullCall_echoSome ctx a n hlen).mp hacc
    have hnN := le_seqLength rules n hr
    refine ⟨by omega, hn, s, hs, ?_⟩
    apply List.ext_getElem?
    intro i
    rw [hpi]
    simp only [List.getElem?_map, List.getElem?_take]
    by_cases hi : i < n
    · have hiK : i < (notes (bestRhythm rules a)).length := by omega
      simp only [hi, hiK, ite_true]
      rw [bestCallNotes_get_lt _ _ _ i (by omega)]
      cases hp : (pitches a)[i]? with
      | none => simp
      | some p =>
        have hpm : p ∈ (pitches a).take (seqLength rules) := by
          rw [List.mem_iff_getElem?]
          exact ⟨i, by rw [List.getElem?_take]; simp [show i < seqLength rules by omega, hp]⟩
        simp [(shiftedOnGuitar_iff s p (hG p hpm)).2]
    · simp [hi]
  | sayLess =>
    simp only [bestCallRuleChecker] at hacc
    split at hacc
    · simp [neverPass_accepts] at hacc
    · rename_i hc
      have h := (fullCall_sayLess ctx a).mp hacc
      have hK' : (notes (bestRhythm rules a)).length = phraseSlots := by
        rw [hK, ite_eq_right_of_eq_false _ _ (by simpa using hc)]
      simp only [RuleHolds]
      rw [← pitches_length, ← pitches_length, hcount, hK']
      exact h
  | startNear k =>
    have hcond : SNCond (seqLength rules) s k (!rules.contains .echoRhythm) (pitches a) := by
      simp only [bestCallRuleChecker] at hacc
      split at hacc
      · rename_i h
        simp only [nearIsFree, Bool.and_eq_true, decide_eq_true_eq] at h
        by_cases h24 : (pitches a).length < phraseSlots
        · exact Or.inr (Or.inl ⟨h.1, h24⟩)
        · exact Or.inl (by omega)
      · exact (startNearShifted_accepts _ _ _ _ a).mp hacc
    intro c f hc hf
    rw [hpi, List.getLast?_eq_getElem?, List.length_take, List.getElem?_take] at hc
    have hK1 : min (notes (bestRhythm rules a)).length
        (bestCallNotes (seqLength rules) s (pitches a)).length - 1 =
        (notes (bestRhythm rules a)).length - 1 := by omega
    have hK2 : (notes (bestRhythm rules a)).length - 1 < (notes (bestRhythm rules a)).length := by omega
    rw [hK1] at hc
    simp only [hK2, ↓reduceIte] at hc
    by_cases hlt : (notes (bestRhythm rules a)).length - 1 < min (seqLength rules) (pitches a).length
    · rw [bestCallNotes_get_lt _ _ _ _ hlt] at hc
      -- The best call has exactly the answer's notes, all shifted.
      have hKeq : (notes (bestRhythm rules a)).length = (pitches a).length ∧
          (rules.contains .echoRhythm = false → (pitches a).length = phraseSlots) := by
        rw [hK] at hlt ⊢
        by_cases he : rules.contains .echoRhythm = true
        · constructor
          · simp only [he, ite_true]
          · intro h; rw [he] at h; cases h
        · simp only [Bool.not_eq_true] at he
          simp only [he, Bool.false_eq_true, ite_false, phraseSlots] at hlt hm24 ⊢
          constructor
          · omega
          · intro _; omega
      rcases hcond with h | ⟨h1, h2⟩ | ⟨f', l, hf', hl, hd⟩
      · omega
      · simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h1
        have := hKeq.2 h1; omega
      · have hKeq := hKeq.1
        rw [hf] at hf'; cases hf'
        rw [List.getLast?_eq_getElem?, ← hKeq] at hl
        rw [hl] at hc
        simp only [Option.map_some, Option.some.injEq] at hc
        rw [← hc]; exact hd
    · rw [bestCallNotes_get_ge _ _ _ _ (by omega) (by omega)] at hc
      cases hc
      rw [headD_of_head? _ f 60 hf, distance_self]
      omega
  | maxLeap k => exact (ruleChecker_accepts_iff ctx fullCall a (.maxLeap k) hlen).mp hacc
  | chordToneOnBeat t b => exact (ruleChecker_accepts_iff ctx fullCall a (.chordToneOnBeat t b) hlen).mp hacc
  | avoid n => exact (ruleChecker_accepts_iff ctx fullCall a (.avoid n) hlen).mp hacc
  | stayBetween low high => exact (ruleChecker_accepts_iff ctx fullCall a (.stayBetween low high) hlen).mp hacc
  | maxNotesPerBar n => exact (ruleChecker_accepts_iff ctx fullCall a (.maxNotesPerBar n) hlen).mp hacc
  | leaveSpace k => exact (ruleChecker_accepts_iff ctx fullCall a (.leaveSpace k) hlen).mp hacc

/-! ## Complete: a working call gives a working best call -/

/-- `OnGuitar` with the numbers written out, at type `Nat` (so `omega` can use it). -/
theorem onGuitar_bounds (p : Nat) (h : OnGuitar p) : 40 ≤ p ∧ p ≤ 88 := h

/-- The shift of the call `c` and its answer `a`. With a `sequence` rule, all
sequence rules share this shift: `a`'s first note minus `c`'s first note. -/
def seqShift (rules : List Rule) (c a : Phrase) : Int :=
  if seqLength rules = 0 then 1 else ((pitches a).headD 0 : Int) - (pitches c).headD 0

/-- Read one note off a list equality "the answer's notes are the call's
notes moved by `sh`". -/
theorem shift_at (ps cs : List Pitch) (N : Nat) (sh : Int)
    (E : (ps.take N).map (fun (p : Pitch) => (p : Int)) =
      (cs.take N).map (fun (p : Pitch) => (p : Int) + sh))
    (i : Nat) (hi : i < N) (p : Pitch) (hp : ps[i]? = some p) :
    ∃ c, cs[i]? = some c ∧ (p : Int) = c + sh := by
  have := congrArg (·[i]?) E
  simp only [List.getElem?_map, List.getElem?_take, hi, ↓reduceIte, hp, Option.map_some] at this
  cases hc : cs[i]? with
  | none => simp [hc] at this
  | some c =>
    simp only [hc, Option.map_some, Option.some.injEq] at this
    exact ⟨c, rfl, this⟩

/-- With a `sequence` rule, the answer's first notes are the call's first
notes moved by `seqShift`. -/
theorem witness_seq (ctx : Context) (rules : List Rule) (c a : Phrase)
    (ha : Satisfies ctx c rules a) (hN : seqLength rules ≠ 0) :
    seqLength rules ≤ (pitches c).length ∧ seqLength rules ≤ (pitches a).length ∧
    seqShift rules c a ≠ 0 ∧
    ((pitches a).take (seqLength rules)).map (fun (p : Pitch) => (p : Int)) =
      ((pitches c).take (seqLength rules)).map
        (fun (p : Pitch) => (p : Int) + seqShift rules c a) := by
  have hmem : Rule.sequence (seqLength rules) ∈ rules := (seqLength_mem rules).resolve_left hN
  obtain ⟨h1, h2, sh, hsh, E⟩ := ha.2 _ hmem
  -- The shift is fixed by the first notes.
  have hwit : seqShift rules c a = sh := by
    obtain ⟨p0, hp0⟩ : ∃ p0, (pitches a)[0]? = some p0 :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨c0, hc0, hpc⟩ := shift_at _ _ _ sh E 0 (by omega) p0 hp0
    have ha0 : (pitches a).headD 0 = p0 := by
      cases h : pitches a with
      | nil => rw [h] at hp0; simp at hp0
      | cons q _ => rw [h] at hp0; simpa using hp0
    have hc0' : (pitches c).headD 0 = c0 := by
      cases h : pitches c with
      | nil => rw [h] at hc0; simp at hc0
      | cons q _ => rw [h] at hc0; simpa using hc0
    simp only [seqShift, hN, ↓reduceIte, ha0, hc0']
    omega
  rw [hwit]
  exact ⟨h1, h2, hsh, E⟩

theorem seqShift_mem' (ctx : Context) (rules : List Rule) (c a : Phrase) (hc : Playable c)
    (ha : Satisfies ctx c rules a) (hall : needsAllShifts rules = true) :
    seqShift rules c a ∈ callShifts rules := by
  by_cases hN : seqLength rules = 0
  · simp [seqShift, callShifts, hN]
  · obtain ⟨h1, h2, h0, -⟩ := witness_seq ctx rules c a ha hN
    have hgA : OnGuitar ((pitches a).headD 0) := by
      cases h : pitches a with
      | nil => rw [h] at h2; simp at h2; omega
      | cons q _ => exact ha.1.2.2 q (by simp [h])
    have hgC : OnGuitar ((pitches c).headD 0) := by
      cases h : pitches c with
      | nil => rw [h] at h1; simp at h1; omega
      | cons q _ => exact hc.2.2 q (by simp [h])
    have hA := onGuitar_bounds _ hgA
    have hC := onGuitar_bounds _ hgC
    apply mem_callShifts rules _ h0 _ _ hN hall
    · simp only [seqShift, hN, ↓reduceIte, guitarLow, guitarHigh]
      omega
    · simp only [seqShift, hN, ↓reduceIte, guitarLow, guitarHigh]
      omega

/-- The witness answer's first notes, moved down by `seqShift`, are the
call's first notes, so they are on the guitar. -/
theorem witness_onGuitar_seq (ctx : Context) (rules : List Rule) (c a : Phrase) (hc : Playable c)
    (ha : Satisfies ctx c rules a) :
    ∀ p ∈ (pitches a).take (seqLength rules), shiftedOnGuitar (seqShift rules c a) p = true := by
  intro p hp
  by_cases hN : seqLength rules = 0
  · simp [hN] at hp
  obtain ⟨-, -, -, E⟩ := witness_seq ctx rules c a ha hN
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  rw [List.getElem?_take] at hi
  split at hi
  · rename_i hiN
    obtain ⟨c', hc', hpc⟩ := shift_at _ _ _ _ E i hiN p hi
    have hg : OnGuitar c' := hc.2.2 c' (List.mem_of_getElem? hc')
    unfold shiftedOnGuitar
    have e1 : ((guitarLow : Nat) : Int) = 40 := rfl
    have e2 : ((guitarHigh : Nat) : Int) = 88 := rfl
    rw [e1, e2]
    have key : ∀ x y : Int, 40 ≤ y → y ≤ 88 → x = y →
        (decide (40 ≤ x) && decide (x ≤ 88)) = true := by
      intro x y h1 h2 h3; simp; omega
    have hg' : 40 ≤ (c' : Int) ∧ (c' : Int) ≤ 88 := by
      have := onGuitar_bounds _ hg
      omega
    exact key _ c' hg'.1 hg'.2 (by omega)
  · cases hi

/-- The witness answer passes each rule's checker for the best call. -/
theorem bestCall_rule_witness_seq (ctx : Context) (rules : List Rule) (c a : Phrase)
    (hc : Playable c) (ha : Satisfies ctx c rules a) (r : Rule) (hr : r ∈ rules) :
    (bestCallRuleChecker ctx rules (seqShift rules c a) r).accepts a = true := by
  have hlen := ha.1.1
  have hm : 1 ≤ (pitches a).length := by
    rw [pitches_length]; exact List.length_pos_iff.mpr ha.1.2.1
  have hm24 : (pitches a).length ≤ phraseSlots := by
    rw [pitches_length, ← hlen]; exact notes_length_le a
  have hc24 : (pitches c).length ≤ phraseSlots := by
    rw [pitches_length, ← hc.1]; exact notes_length_le c
  have hrule := ha.2 r hr
  cases r with
  | echoRhythm => exact alwaysPass_accepts a
  | echoSomeRhythm k =>
    simp only [bestCallRuleChecker]
    rw [fullCall_echoSome ctx a k hlen]
    have : ((onsetSlots c).filter (· ∈ onsetSlots a)).length ≤ (onsetSlots a).length := by
      apply List.Nodup.length_le_of_subset ((onsetSlots_nodup c).filter _)
      intro x hx
      simpa using (List.mem_filter.mp hx).2
    simp only [RuleHolds] at hrule
    rw [onsetSlots_length, ← pitches_length] at this
    omega
  | sequence n =>
    simp only [bestCallRuleChecker]
    rw [fullCall_echoSome ctx a n hlen]
    exact hrule.2.1
  | sayLess =>
    simp only [bestCallRuleChecker]
    split
    · rename_i he
      have hecho := ha.2 _ ((contains_echo_iff rules).mp he)
      simp only [RuleHolds] at hrule hecho
      have := congrArg List.length hecho
      rw [onsetSlots_length, onsetSlots_length] at this
      omega
    · rw [fullCall_sayLess]
      simp only [RuleHolds] at hrule
      rw [← pitches_length, ← pitches_length] at hrule
      omega
  | startNear k =>
    simp only [bestCallRuleChecker]
    split
    · exact alwaysPass_accepts a
    · rw [startNearShifted_accepts]
      by_cases h1 : seqLength rules < (pitches a).length
      · exact Or.inl h1
      by_cases h2 : (!rules.contains .echoRhythm) = true ∧ (pitches a).length < phraseSlots
      · exact Or.inr (Or.inl h2)
      right; right
      -- Here every note of the call is a `sequence` note.
      have hN : seqLength rules ≠ 0 := by omega
      obtain ⟨hNc, hNa, -, E⟩ := witness_seq ctx rules c a ha hN
      have hma : (pitches a).length = seqLength rules := by omega
      have hmc : (pitches c).length = seqLength rules := by
        by_cases he : rules.contains .echoRhythm = true
        · have hecho := ha.2 _ ((contains_echo_iff rules).mp he)
          simp only [RuleHolds] at hecho
          have := congrArg List.length hecho
          rw [onsetSlots_length, onsetSlots_length, ← pitches_length, ← pitches_length] at this
          omega
        · simp only [he, Bool.not_false, true_and] at h2
          omega
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at E
      obtain ⟨f, hf⟩ : ∃ f, (pitches a).head? = some f := by
        cases h : pitches a with
        | nil => rw [h] at hm; simp at hm
        | cons q _ => exact ⟨q, rfl⟩
      obtain ⟨l, hl⟩ : ∃ l, (pitches a).getLast? = some l := by
        cases h : (pitches a).getLast? with
        | none => simp [List.getLast?_eq_none_iff] at h; rw [h] at hm; simp at hm
        | some l => exact ⟨l, rfl⟩
      have hlast := congrArg List.getLast? E
      simp only [List.getLast?_map, hl, Option.map_some] at hlast
      cases hcl : (pitches c).getLast? with
      | none => rw [hcl] at hlast; simp at hlast
      | some cl =>
        rw [hcl] at hlast
        simp only [Option.map_some, Option.some.injEq] at hlast
        refine ⟨f, l, hf, hl, ?_⟩
        have hd := hrule cl f hcl hf
        have : shiftDown (seqShift rules c a) l = cl := by
          show (((l : Nat) : Int) - seqShift rules c a).toNat = (cl : Nat)
          omega
        rw [this]; exact hd
  | maxLeap k => exact (ruleChecker_accepts_iff ctx fullCall a (.maxLeap k) hlen).mpr hrule
  | chordToneOnBeat t b =>
    exact (ruleChecker_accepts_iff ctx fullCall a (.chordToneOnBeat t b) hlen).mpr hrule
  | avoid n => exact (ruleChecker_accepts_iff ctx fullCall a (.avoid n) hlen).mpr hrule
  | stayBetween low high =>
    exact (ruleChecker_accepts_iff ctx fullCall a (.stayBetween low high) hlen).mpr hrule
  | maxNotesPerBar n =>
    exact (ruleChecker_accepts_iff ctx fullCall a (.maxNotesPerBar n) hlen).mpr hrule
  | leaveSpace k => exact (ruleChecker_accepts_iff ctx fullCall a (.leaveSpace k) hlen).mpr hrule

/-! ## The whole checker -/

theorem bestCallRuleChecker_deadIsFinal (ctx : Context) (rules : List Rule) (s : Int) (r : Rule) :
    (bestCallRuleChecker ctx rules s r).DeadIsFinal := by
  cases r with
  | echoRhythm => exact alwaysPass_deadIsFinal
  | sayLess =>
    simp only [bestCallRuleChecker]
    split
    · exact neverPass_deadIsFinal
    · exact ruleChecker_deadIsFinal ctx _ _
  | startNear k =>
    simp only [bestCallRuleChecker]
    split
    · exact alwaysPass_deadIsFinal
    · exact startNearShifted_deadIsFinal _ _ _ _
  | _ => simp only [bestCallRuleChecker]; exact ruleChecker_deadIsFinal ctx _ _

/-- Dropping dead memories is safe for `bestCallChecker`. -/
theorem bestCallChecker_deadIsFinal (ctx : Context) (rules : List Rule) (s : Int) :
    (bestCallChecker ctx rules s).DeadIsFinal := by
  apply allOf_deadIsFinal
  intro ch hch
  simp only [List.mem_cons, List.mem_map] at hch
  rcases hch with rfl | rfl | ⟨r, -, rfl⟩
  · exact playableChecker_deadIsFinal
  · exact shiftedOnGuitarChecker_deadIsFinal _ _
  · exact bestCallRuleChecker_deadIsFinal ctx rules s r

/-- Dropping dead memories is safe for `quickChecker`. -/
theorem quickChecker_deadIsFinal (ctx : Context) (rules : List Rule) :
    (quickChecker ctx rules).DeadIsFinal := by
  apply allOf_deadIsFinal
  intro ch hch
  simp only [List.mem_cons, List.mem_map] at hch
  rcases hch with rfl | ⟨r, -, rfl⟩
  · exact playableChecker_deadIsFinal
  · cases r with
    | startNear k => exact alwaysPass_deadIsFinal
    | _ => simp only [quickRuleChecker]; exact bestCallRuleChecker_deadIsFinal ctx rules 1 _

/-- **Sound.** If `bestCallChecker` passes a 24-slot answer, the answer is
playable, the best call is playable, and the answer obeys every rule against
the best call. -/
theorem bestCallChecker_sound (ctx : Context) (rules : List Rule) (s : Int) (a : Phrase)
    (hlen : a.length = phraseSlots) (hs : s ≠ 0)
    (hacc : (bestCallChecker ctx rules s).accepts a = true) :
    Playable a ∧ Playable (bestCall rules s a) ∧
      ∀ r ∈ rules, RuleHolds ctx (bestCall rules s a) a r := by
  rw [bestCallChecker, allOf_accepts] at hacc
  have hp := hacc playableChecker (by simp)
  have hplay : Playable a := (isPlayable_iff a).mp (by simp [hlen, phraseSlots, hp])
  have hG := (shiftedOnGuitarChecker_accepts _ _ a).mp
    (hacc (shiftedOnGuitarChecker (seqLength rules) s) (by simp))
  refine ⟨hplay, bestCall_playable rules s a hplay hG, fun r hr => ?_⟩
  exact bestCall_rule_holds ctx rules s a hplay hG hs r hr
    (hacc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hr))))

/-- The shift we use for a call `c` and its answer `a`: its own shift when every
shift is tried, otherwise just its sign. -/
def witnessShift (rules : List Rule) (c a : Phrase) : Int :=
  if needsAllShifts rules then seqShift rules c a
  else if 0 < seqShift rules c a then 1 else -1

theorem witnessShift_mem (ctx : Context) (rules : List Rule) (c a : Phrase) (hc : Playable c)
    (ha : Satisfies ctx c rules a) : witnessShift rules c a ∈ callShifts rules := by
  unfold witnessShift
  split
  · rename_i hall; exact seqShift_mem' ctx rules c a hc ha hall
  · split
    · exact one_mem_callShifts rules
    · rename_i h
      by_cases hN : seqLength rules = 0
      · simp [seqShift, hN] at h
      · exact neg_one_mem_callShifts rules hN

theorem witness_onGuitar (ctx : Context) (rules : List Rule) (c a : Phrase) (hc : Playable c)
    (ha : Satisfies ctx c rules a) :
    ∀ p ∈ (pitches a).take (seqLength rules), shiftedOnGuitar (witnessShift rules c a) p = true := by
  intro p hp
  have hseq := witness_onGuitar_seq ctx rules c a hc ha p hp
  unfold witnessShift
  split
  · exact hseq
  · have hg := onGuitar_bounds _ (ha.1.2.2 p (List.mem_of_mem_take hp))
    have hN : seqLength rules ≠ 0 := by intro h; simp [h] at hp
    have h0 : seqShift rules c a ≠ 0 := (witness_seq ctx rules c a ha hN).2.2.1
    unfold shiftedOnGuitar at hseq ⊢
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hseq
    have e1 : ((guitarLow : Nat) : Int) = 40 := rfl
    have e2 : ((guitarHigh : Nat) : Int) = 88 := rfl
    rw [e1, e2] at hseq ⊢
    have hg' : 40 ≤ (p : Int) ∧ (p : Int) ≤ 88 := by omega
    generalize seqShift rules c a = t at hseq h0
    generalize (p : Int) = q at hseq hg' ⊢
    split <;> simp <;> omega

/-- A rule's checker for the best call depends on the shift only for `startNear`. -/
theorem bestCallRuleChecker_shift (ctx : Context) (rules : List Rule) (s s' : Int) (r : Rule)
    (h : ∀ k, r ≠ .startNear k) :
    bestCallRuleChecker ctx rules s r = bestCallRuleChecker ctx rules s' r := by
  cases r with
  | startNear k => exact absurd rfl (h k)
  | _ => rfl

theorem bestCall_rule_witness (ctx : Context) (rules : List Rule) (c a : Phrase)
    (hc : Playable c) (ha : Satisfies ctx c rules a) (r : Rule) (hr : r ∈ rules) :
    (bestCallRuleChecker ctx rules (witnessShift rules c a) r).accepts a = true := by
  have hw := bestCall_rule_witness_seq ctx rules c a hc ha r hr
  by_cases hnear : ∃ k, r = .startNear k
  · obtain ⟨k, rfl⟩ := hnear
    by_cases hfree : nearIsFree rules = true
    · simp only [bestCallRuleChecker, hfree, ↓reduceIte]; exact alwaysPass_accepts a
    · have hall : needsAllShifts rules = true := by
        simp only [needsAllShifts, Bool.and_eq_true, List.any_eq_true, hfree, Bool.not_false,
          and_true] at hfree ⊢
        exact ⟨.startNear k, hr, rfl⟩
      simp only [witnessShift, hall, ↓reduceIte]
      exact hw
  · rw [bestCallRuleChecker_shift ctx rules _ (seqShift rules c a) r
      (fun k h => hnear ⟨k, h⟩)]
    exact hw

/-- **Complete.** If some playable call `c` has an answer `a`, then for one of
the shifts we try, `bestCallChecker` passes `a`. -/
theorem bestCallChecker_complete (ctx : Context) (rules : List Rule) (c a : Phrase)
    (hc : Playable c) (ha : Satisfies ctx c rules a) :
    ∃ s ∈ callShifts rules, (bestCallChecker ctx rules s).accepts a = true := by
  refine ⟨witnessShift rules c a, witnessShift_mem ctx rules c a hc ha, ?_⟩
  rw [bestCallChecker, allOf_accepts]
  intro ch hch
  simp only [List.mem_cons, List.mem_map] at hch
  rcases hch with rfl | rfl | ⟨r, hr, rfl⟩
  · have := (isPlayable_iff a).mpr ha.1
    simp only [Bool.and_eq_true] at this
    exact this.2
  · exact (shiftedOnGuitarChecker_accepts _ _ a).mpr (witness_onGuitar ctx rules c a hc ha)
  · exact bestCall_rule_witness ctx rules c a hc ha r hr

/-- If some playable call `c` has an answer `a`, the quick test passes `a`. -/
theorem quickChecker_complete (ctx : Context) (rules : List Rule) (c a : Phrase)
    (hc : Playable c) (ha : Satisfies ctx c rules a) :
    (quickChecker ctx rules).accepts a = true := by
  rw [quickChecker, allOf_accepts]
  intro ch hch
  simp only [List.mem_cons, List.mem_map] at hch
  rcases hch with rfl | ⟨r, hr, rfl⟩
  · have := (isPlayable_iff a).mpr ha.1
    simp only [Bool.and_eq_true] at this
    exact this.2
  · have hw := bestCall_rule_witness ctx rules c a hc ha r hr
    cases r with
    | startNear k => exact alwaysPass_accepts a
    | _ =>
      simp only [quickRuleChecker]
      rw [bestCallRuleChecker_shift ctx rules 1 (witnessShift rules c a) _ (by simp)]
      exact hw

end Blues
