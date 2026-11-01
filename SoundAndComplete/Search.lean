import SoundAndComplete.Music
import Std.Data.HashMap

/-!
# Checkers and the search (generic, knows nothing about music rules)

A **checker** reads a phrase one slot at a time. It keeps a small memory
(its *state*), updates it after each slot, and at the end says pass or fail.

The **search** answers: is there any 24-slot phrase the checker passes?
It goes slot by slot. After `k` slots it keeps, for every state the checker
can be in, one example phrase that reaches it. Two phrases in the same state
pass or fail the same way from then on, so one example per state loses
nothing. That is why the search is exact.

The two facts we prove about the search (at the bottom of this file):

* **sound**: whatever it returns is a phrase of the right length that the checker passes;
* **complete**: if such a phrase exists (using notes on the guitar), it returns one.
-/

namespace Blues

/-- A checker over states of type `σ`.
`step i s x` is the new state after reading `x` in slot `i`, starting from state `s`. -/
structure Checker (σ : Type) where
  init : σ
  step : Nat → σ → Slot → σ
  accept : σ → Bool
  /-- States that can never lead to a pass. The search drops them to save time.
  `DeadIsFinal` (below) says this is safe. -/
  dead : σ → Bool := fun _ => false

namespace Checker

variable {σ : Type}

/-- Read `w` starting at slot `i` in state `s`; return the final state. -/
def runFrom (c : Checker σ) : Nat → σ → Phrase → σ
  | _, s, [] => s
  | i, s, x :: xs => c.runFrom (i + 1) (c.step i s x) xs

/-- The state after reading the whole phrase from the start. -/
def run (c : Checker σ) (w : Phrase) : σ := c.runFrom 0 c.init w

/-- The checker passes `w`. -/
def accepts (c : Checker σ) (w : Phrase) : Bool := c.accept (c.run w)

/-- Dropping dead states is safe: a dead state stays dead, and never passes. -/
def DeadIsFinal (c : Checker σ) : Prop :=
  (∀ i s x, c.dead s = true → c.dead (c.step i s x) = true) ∧
  (∀ s, c.dead s = true → c.accept s = false)

end Checker

/-! ## Running several checkers side by side -/

/-- Step every checker in the list on its own state. -/
def stepAll {σ : Type} (i : Nat) (x : Slot) : List (Checker σ) → List σ → List σ
  | c :: cs, s :: ss => c.step i s x :: stepAll i x cs ss
  | _, _ => []

/-- Every checker accepts its own state. -/
def acceptAll {σ : Type} : List (Checker σ) → List σ → Bool
  | c :: cs, s :: ss => c.accept s && acceptAll cs ss
  | [], [] => true
  | _, _ => false

/-- Some checker is in a dead state. -/
def anyDead {σ : Type} : List (Checker σ) → List σ → Bool
  | c :: cs, s :: ss => c.dead s || anyDead cs ss
  | _, _ => false

/-- All the checkers at once. Its state is the list of their states.
It passes a phrase exactly when every one of them does (`allOf_accepts`). -/
def allOf {σ : Type} (cs : List (Checker σ)) : Checker (List σ) where
  init := cs.map (·.init)
  step i ss x := stepAll i x cs ss
  accept := acceptAll cs
  dead := anyDead cs

/-! ## The search -/

/-- Notes of the A minor blues scale (A C D Eb E G). -/
def inBluesScale (p : Nat) : Bool := [9, 0, 2, 3, 4, 7].contains (p % 12)

/-- Every note on the guitar, in the order the search tries them: blues-scale
notes in the middle register first, then other scale notes, then the rest.
The order only changes which example answer the search shows; every note is
still tried, so the search stays complete. -/
def guitarNotes : List Nat :=
  let all := (List.range (guitarHigh - guitarLow + 1)).map (· + guitarLow)
  let first (p : Nat) := inBluesScale p && 55 ≤ p && p ≤ 72
  all.filter first ++ all.filter (fun p => !first p && inBluesScale p) ++
    all.filter (fun p => !first p && !inBluesScale p)

/-- Everything the search tries in a slot: a rest, or any note on the guitar. -/
def alphabet : List Slot :=
  .rest :: guitarNotes.map .note

section Search
variable {σ : Type} [DecidableEq σ] [Hashable σ]

/-- From the entries after `i` slots, all entries after `i + 1` slots:
try every slot value on every entry, and keep one example per new state
(the first one found). Examples are stored newest slot first. -/
def nextLayer (c : Checker σ) (i : Nat) (layer : List (σ × Phrase)) : List (σ × Phrase) :=
  let seen : Std.HashMap σ Phrase :=
    layer.foldl
      (fun m e => alphabet.foldl (fun m x =>
        let s := c.step i e.1 x
        if c.dead s then m else m.insertIfNew s (x :: e.2)) m)
      ∅
  seen.toList

/-- `layer c k`: one entry per state the checker can reach after `k` slots,
with an example phrase (newest slot first) that reaches it. -/
def layer (c : Checker σ) : Nat → List (σ × Phrase)
  | 0 => [(c.init, [])]
  | k + 1 => nextLayer c k (layer c k)

/-- Find a phrase of `n` slots that the checker passes, or `none` if there is none.
The result is checked again before it is returned. -/
def search (c : Checker σ) (n : Nat) : Option Phrase :=
  match (layer c n).find? (fun e => c.accept e.1) with
  | some e =>
    let w := e.2.reverse
    if w.length == n && c.accepts w then some w else none
  | none => none

end Search

/-! ## Facts about checkers and the search -/

/-! ### Small general lemmas -/

/-- A property that holds at the start of a fold and is kept by every step
holds at the end. -/
theorem foldl_invariant {α β : Type} (P : β → Prop) (f : β → α → β) (l : List α) (init : β)
    (h0 : P init) (hstep : ∀ acc a, a ∈ l → P acc → P (f acc a)) : P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih =>
    exact ih (f init a) (hstep init a (by simp) h0)
      (fun acc b hb hP => hstep acc b (by simp [hb]) hP)

/-- If a property, once true, stays true through every step, and processing
`a0` always makes it true, then it is true at the end of a fold over a list
containing `a0`. -/
theorem foldl_reaches {α β : Type} (Q : β → Prop) (f : β → α → β) (l : List α) (init : β)
    (a0 : α) (ha0 : a0 ∈ l) (hmono : ∀ acc a, Q acc → Q (f acc a))
    (hhit : ∀ acc, Q (f acc a0)) : Q (l.foldl f init) := by
  induction l generalizing init with
  | nil => simp at ha0
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha0 with h | h
    · subst h
      exact foldl_invariant Q f l _ (hhit init) (fun acc b _ hQ => hmono acc b hQ)
    · exact ih _ h

namespace Checker
variable {σ : Type}

/-- Reading `u ++ v` is reading `u`, then reading `v` from where `u` left off. -/
theorem runFrom_append (c : Checker σ) (i : Nat) (s : σ) (u v : Phrase) :
    c.runFrom i s (u ++ v) = c.runFrom (i + u.length) (c.runFrom i s u) v := by
  induction u generalizing i s with
  | nil => simp [runFrom]
  | cons x u ih =>
    simp only [List.cons_append, runFrom, ih, List.length_cons]
    congr 1
    omega

/-- Reading one more slot at the end is one more step. -/
theorem run_append_single (c : Checker σ) (u : Phrase) (x : Slot) :
    c.run (u ++ [x]) = c.step u.length (c.run u) x := by
  simp [run, runFrom_append, runFrom]

end Checker

/-! ### Running several checkers side by side -/

theorem allOf_runFrom_cons {σ : Type} (c : Checker σ) (cs : List (Checker σ))
    (i : Nat) (s : σ) (ss : List σ) (w : Phrase) :
    (allOf (c :: cs)).runFrom i (s :: ss) w = c.runFrom i s w :: (allOf cs).runFrom i ss w := by
  induction w generalizing i s ss with
  | nil => rfl
  | cons x w ih => exact ih (i + 1) _ _

theorem allOf_runFrom_nil {σ : Type} (i : Nat) (w : Phrase) :
    (allOf ([] : List (Checker σ))).runFrom i [] w = [] := by
  induction w generalizing i with
  | nil => rfl
  | cons x w ih => exact ih (i + 1)

/-- Running all checkers together gives each checker's own final state. -/
theorem allOf_run {σ : Type} (cs : List (Checker σ)) (w : Phrase) :
    (allOf cs).run w = cs.map (fun c => c.run w) := by
  induction cs with
  | nil => exact allOf_runFrom_nil 0 w
  | cons c cs ih =>
    simp only [Checker.run, List.map_cons] at ih ⊢
    show (allOf (c :: cs)).runFrom 0 (c.init :: cs.map (·.init)) w = _
    rw [allOf_runFrom_cons]
    exact congrArg (c.runFrom 0 c.init w :: ·) ih

theorem acceptAll_map {σ : Type} (cs : List (Checker σ)) (f : Checker σ → σ) :
    acceptAll cs (cs.map f) = true ↔ ∀ c ∈ cs, c.accept (f c) = true := by
  induction cs with
  | nil => simp [acceptAll]
  | cons c cs ih => simp [acceptAll, ih]

/-- Running all checkers together passes exactly when each one passes. -/
theorem allOf_accepts {σ : Type} (cs : List (Checker σ)) (w : Phrase) :
    (allOf cs).accepts w = true ↔ ∀ c ∈ cs, c.accepts w = true := by
  simp only [Checker.accepts, allOf_run]
  exact acceptAll_map cs _

/-- If dropping dead states is safe for each checker, it is safe for all of them together. -/
theorem allOf_deadIsFinal {σ : Type} (cs : List (Checker σ)) :
    (∀ c ∈ cs, c.DeadIsFinal) → (allOf cs).DeadIsFinal := by
  intro h
  constructor
  · intro i ss x hd
    show anyDead cs (stepAll i x cs ss) = true
    change anyDead cs ss = true at hd
    induction cs generalizing ss with
    | nil => simp [anyDead] at hd
    | cons c cs ih =>
      cases ss with
      | nil => simp [anyDead] at hd
      | cons s ss =>
        simp only [anyDead, stepAll, Bool.or_eq_true] at hd ⊢
        rcases hd with hd | hd
        · exact Or.inl ((h c (by simp)).1 i s x hd)
        · exact Or.inr (ih (fun c' hc' => h c' (by simp [hc'])) ss hd)
  · intro ss hd
    show acceptAll cs ss = false
    change anyDead cs ss = true at hd
    induction cs generalizing ss with
    | nil => simp [anyDead] at hd
    | cons c cs ih =>
      cases ss with
      | nil => simp [anyDead] at hd
      | cons s ss =>
        simp only [anyDead, acceptAll, Bool.or_eq_true, Bool.and_eq_false_iff] at hd ⊢
        rcases hd with hd | hd
        · exact Or.inl ((h c (by simp)).2 s hd)
        · exact Or.inr (ih (fun c' hc' => h c' (by simp [hc'])) ss hd)

/-! ### The search -/

section SearchProofs
variable {σ : Type} [DecidableEq σ] [Hashable σ]

/-- The inner loop of `nextLayer`: add every allowed next state from one entry. -/
private def addFrom (c : Checker σ) (i : Nat) (m : Std.HashMap σ Phrase) (e : σ × Phrase) :
    Std.HashMap σ Phrase :=
  alphabet.foldl (fun m x =>
    let s := c.step i e.1 x
    if c.dead s then m else m.insertIfNew s (x :: e.2)) m

private theorem nextLayer_eq (c : Checker σ) (i : Nat) (layer : List (σ × Phrase)) :
    nextLayer c i layer = (layer.foldl (addFrom c i) ∅).toList := rfl

/-- Every entry of the next layer extends some entry of this layer by one slot. -/
theorem mem_nextLayer (c : Checker σ) (i : Nat) (layer : List (σ × Phrase)) (e' : σ × Phrase) :
    e' ∈ nextLayer c i layer →
      ∃ e ∈ layer, ∃ x, e' = (c.step i e.1 x, x :: e.2) := by
  rw [nextLayer_eq]
  intro he'
  obtain ⟨k, v⟩ := e'
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at he'
  let P : Std.HashMap σ Phrase → Prop := fun m =>
    ∀ k v, m[k]? = some v → ∃ e ∈ layer, ∃ x, (k, v) = (c.step i e.1 x, x :: e.2)
  have hP : P (layer.foldl (addFrom c i) ∅) := by
    apply foldl_invariant
    · intro k v h; simp at h
    · intro m e he hm
      apply foldl_invariant (P := P)
      · exact hm
      · intro m' x _ hm' k' v' h
        simp only at h
        split at h
        · exact hm' k' v' h
        · rw [Std.HashMap.getElem?_insertIfNew] at h
          split at h
          · rename_i hk
            simp only [beq_iff_eq] at hk
            obtain ⟨rfl, -⟩ := hk
            cases h
            exact ⟨e, he, x, rfl⟩
          · exact hm' k' v' h
  exact hP k v he'

/-- If an entry of this layer can step to a live state, the next layer has an
entry with that state. -/
theorem nextLayer_covers (c : Checker σ) (i : Nat) (layer : List (σ × Phrase))
    (e : σ × Phrase) (he : e ∈ layer) (x : Slot) (hx : x ∈ alphabet)
    (hlive : c.dead (c.step i e.1 x) = false) :
    ∃ e' ∈ nextLayer c i layer, e'.1 = c.step i e.1 x := by
  rw [nextLayer_eq]
  let k := c.step i e.1 x
  have hk : k ∈ layer.foldl (addFrom c i) ∅ := by
    apply foldl_reaches (fun m => k ∈ m) _ layer ∅ e he
    · intro m e' hm
      apply foldl_invariant (fun m => k ∈ m)
      · exact hm
      · intro m' y _ hm'
        simp only
        split
        · exact hm'
        · exact Std.HashMap.mem_insertIfNew.mpr (Or.inr hm')
    · intro m
      apply foldl_reaches (fun m => k ∈ m) _ alphabet m x hx
      · intro m' y hm'
        simp only
        split
        · exact hm'
        · exact Std.HashMap.mem_insertIfNew.mpr (Or.inr hm')
      · intro m'
        simp only [k] at hlive ⊢
        simp only [hlive, Bool.false_eq_true, ↓reduceIte]
        exact Std.HashMap.mem_insertIfNew.mpr (Or.inl (by simp))
  refine ⟨(k, (layer.foldl (addFrom c i) ∅)[k]), ?_, rfl⟩
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
  exact Std.HashMap.getElem?_eq_some_getElem hk

/-- **The layer invariant, part 1.** Every entry is genuine: its example has
`k` slots, and reading it gives the entry's state. -/
theorem layer_sound (c : Checker σ) (k : Nat) (e : σ × Phrase) :
    e ∈ layer c k → e.2.length = k ∧ c.run e.2.reverse = e.1 := by
  induction k generalizing e with
  | zero =>
    intro he
    simp [layer] at he
    subst he
    simp [Checker.run, Checker.runFrom]
  | succ k ih =>
    intro he
    obtain ⟨e0, he0, x, rfl⟩ := mem_nextLayer c k _ e he
    obtain ⟨hlen, hrun⟩ := ih e0 he0
    refine ⟨by simp [hlen], ?_⟩
    simp only [List.reverse_cons]
    rw [Checker.run_append_single, List.length_reverse, hlen, hrun]

/-- **The layer invariant, part 2.** Nothing is lost: every live state that some
`k`-slot phrase (of rests and guitar notes) reaches is the state of some entry. -/
theorem layer_complete (c : Checker σ) (hdead : c.DeadIsFinal) (k : Nat) (u : Phrase)
    (hlen : u.length = k) (hu : ∀ x ∈ u, x ∈ alphabet) (hlive : c.dead (c.run u) = false) :
    ∃ e ∈ layer c k, e.1 = c.run u := by
  induction k generalizing u with
  | zero =>
    have : u = [] := List.eq_nil_of_length_eq_zero hlen
    subst this
    exact ⟨(c.init, []), by simp [layer], rfl⟩
  | succ k ih =>
    rcases List.eq_nil_or_concat u with h | ⟨u', x, rfl⟩
    · subst h; simp at hlen
    · simp only [List.concat_eq_append] at hlen hu hlive ⊢
      have hlen' : u'.length = k := by simp at hlen; omega
      have hrun : c.run (u' ++ [x]) = c.step k (c.run u') x := by
        rw [Checker.run_append_single, hlen']
      have hlive' : c.dead (c.run u') = false := by
        cases hd : c.dead (c.run u') with
        | false => rfl
        | true =>
          have := hdead.1 k _ x hd
          rw [← hrun, hlive] at this
          exact absurd this (by simp)
      obtain ⟨e, he, hes⟩ := ih u' hlen' (fun y hy => hu y (by simp [hy])) hlive'
      have hx : x ∈ alphabet := hu x (by simp)
      rw [hrun, ← hes] at hlive ⊢
      exact nextLayer_covers c k _ e he x hx hlive

end SearchProofs

/-- **Sound**: the search only returns phrases of the right length that pass. -/
theorem search_sound {σ : Type} [DecidableEq σ] [Hashable σ] (c : Checker σ) (n : Nat) (w : Phrase) :
    search c n = some w → w.length = n ∧ c.accepts w = true := by
  unfold search
  split
  · intro h
    dsimp only at h
    split at h
    · rename_i hok
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      exact hok
    · cases h
  · intro h; cases h

/-- **Complete**: if some phrase of `n` slots, using only rests and guitar notes,
passes the checker, the search returns something. Needs: dropping dead
states is safe for this checker. -/
theorem search_complete {σ : Type} [DecidableEq σ] [Hashable σ] (c : Checker σ) (n : Nat)
    (hdead : c.DeadIsFinal) :
    (∃ w : Phrase, w.length = n ∧ (∀ x ∈ w, x ∈ alphabet) ∧ c.accepts w = true) →
      (search c n).isSome := by
  rintro ⟨w, hlen, hw, hacc⟩
  -- The final state of `w` passes, so it is not dead.
  have hlive : c.dead (c.run w) = false := by
    cases hd : c.dead (c.run w) with
    | false => rfl
    | true =>
      have := hdead.2 _ hd
      simp [Checker.accepts, this] at hacc
  -- So some entry of the last layer has that state, and it passes.
  obtain ⟨e, he, hes⟩ := layer_complete c hdead n w hlen hw hlive
  have hfind : ((layer c n).find? (fun e => c.accept e.1)).isSome := by
    rw [List.find?_isSome]
    exact ⟨e, he, by rw [hes]; exact hacc⟩
  unfold search
  obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp hfind
  rw [he0]
  have hmem := List.mem_of_find?_eq_some he0
  have hpass := List.find?_some he0
  obtain ⟨hlen0, hrun0⟩ := layer_sound c n e0 hmem
  have hok : (e0.2.reverse.length == n && c.accepts e0.2.reverse) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, List.length_reverse]
    exact ⟨hlen0, by simp [Checker.accepts, hrun0, hpass]⟩
  simp only [hok, ↓reduceIte, Option.isSome_some]

end Blues
