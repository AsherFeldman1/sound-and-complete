import SoundAndComplete.Spec

/-!
# Properties of the rules

The main theorems show that the code matches the spec. They cannot show that
the spec itself is sensible. If `Spec.lean` had a mistake, the code would match
the mistake.

So here we prove things that any correct version of the rules must obey. If a
rule in `Spec.lean` were written wrongly, one of these would fail.

* A looser setting never turns a pass into a fail.
* Moving the call and the answer up by the same amount does not change the rules
  that are about the shape of a melody.
-/

namespace Blues

/-! ## A looser setting never hurts -/

/-- Allowing bigger jumps keeps every list of notes that passed before. -/
private theorem NoLeapBiggerThan.mono {k k' : Nat} (hk : k ≤ k') :
    ∀ l : List Pitch, NoLeapBiggerThan k l → NoLeapBiggerThan k' l
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: b :: rest, h =>
    ⟨Nat.le_trans h.1 hk, NoLeapBiggerThan.mono hk (b :: rest) h.2⟩

/-- Allowing bigger jumps keeps every answer that passed. -/
theorem maxLeap_looser (ctx : Context) (call answer : Phrase) {k k' : Nat} (hk : k ≤ k') :
    RuleHolds ctx call answer (.maxLeap k) → RuleHolds ctx call answer (.maxLeap k') :=
  NoLeapBiggerThan.mono hk _

/-- Starting further from the call's last note is allowed by a bigger setting. -/
theorem startNear_looser (ctx : Context) (call answer : Phrase) {k k' : Nat} (hk : k ≤ k') :
    RuleHolds ctx call answer (.startNear k) → RuleHolds ctx call answer (.startNear k') :=
  fun h c a hc ha => Nat.le_trans (h c a hc ha) hk

/-- Allowing more notes per bar keeps every answer that passed. -/
theorem maxNotesPerBar_looser (ctx : Context) (call answer : Phrase) {n n' : Nat} (hn : n ≤ n') :
    RuleHolds ctx call answer (.maxNotesPerBar n) →
      RuleHolds ctx call answer (.maxNotesPerBar n') :=
  fun h => ⟨Nat.le_trans h.1 hn, Nat.le_trans h.2 hn⟩

/-- Waiting less is easier: an answer that waited longer still passes. -/
theorem leaveSpace_looser (ctx : Context) (call answer : Phrase) {k k' : Nat} (hk : k' ≤ k) :
    RuleHolds ctx call answer (.leaveSpace k) → RuleHolds ctx call answer (.leaveSpace k') :=
  fun h s p hsp => Nat.le_trans hk (h s p hsp)

/-- A wider hand position keeps every answer that passed. -/
theorem stayBetween_looser (ctx : Context) (call answer : Phrase) {low low' high high' : Pitch}
    (hlow : low' ≤ low) (hhigh : high ≤ high') :
    RuleHolds ctx call answer (.stayBetween low high) →
      RuleHolds ctx call answer (.stayBetween low' high') :=
  fun h p hp => ⟨Nat.le_trans hlow (h p hp).1, Nat.le_trans (h p hp).2 hhigh⟩

/-- Sharing fewer of the call's note starts is easier. -/
theorem echoSomeRhythm_looser (ctx : Context) (call answer : Phrase) {k k' : Nat} (hk : k' ≤ k) :
    RuleHolds ctx call answer (.echoSomeRhythm k) →
      RuleHolds ctx call answer (.echoSomeRhythm k') :=
  fun h => Nat.le_trans hk h

/-- Copying the shape of fewer notes is easier. -/
theorem sequence_looser (ctx : Context) (call answer : Phrase) {n n' : Nat} (hn : n' ≤ n) :
    RuleHolds ctx call answer (.sequence n) → RuleHolds ctx call answer (.sequence n') := by
  rintro ⟨hcall, hanswer, shift, hshift, heq⟩
  refine ⟨Nat.le_trans hn hcall, Nat.le_trans hn hanswer, shift, hshift, ?_⟩
  have := congrArg (List.take n') heq
  simpa [List.take_take, List.map_take, Nat.min_eq_left hn] using this

/-- An exact echo of the rhythm is also a loose echo, of up to all the call's notes. -/
theorem echoRhythm_gives_echoSomeRhythm (ctx : Context) (call answer : Phrase) {k : Nat}
    (hk : k ≤ (onsetSlots call).length) :
    RuleHolds ctx call answer .echoRhythm → RuleHolds ctx call answer (.echoSomeRhythm k) := by
  intro h
  have h' : onsetSlots answer = onsetSlots call := h
  have hall : (onsetSlots call).filter (· ∈ onsetSlots call) = onsetSlots call :=
    List.filter_eq_self.mpr (by simp)
  simpa [RuleHolds, h', hall] using hk

/-! ## Moving to another key -/

private theorem notesFrom_moveUp (d i : Nat) (ph : Phrase) :
    notesFrom i (ph.moveUp d) = (notesFrom i ph).map fun n => (n.1, n.2 + d) := by
  induction ph generalizing i with
  | nil => rfl
  | cons x rest ih =>
    cases x with
    | rest => simpa [Phrase.moveUp, notesFrom] using ih (i + 1)
    | note p => simpa [Phrase.moveUp, notesFrom] using ih (i + 1)

private theorem pitches_moveUp (d : Nat) (ph : Phrase) :
    pitches (ph.moveUp d) = (pitches ph).map (· + d) := by
  simp [pitches, notes, notesFrom_moveUp, Function.comp_def]

private theorem distance_add (a b d : Nat) : distance (a + d) (b + d) = distance a b := by
  by_cases h : a ≤ b <;> simp [distance, h] <;> omega

private theorem noLeap_moveUp (k d : Nat) :
    ∀ l : List Pitch, NoLeapBiggerThan k (l.map (· + d)) ↔ NoLeapBiggerThan k l
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | a :: b :: rest => by
    have ih := noLeap_moveUp k d (b :: rest)
    simp only [List.map_cons, NoLeapBiggerThan, distance_add] at ih ⊢
    rw [ih]

/-- Moving your answer up does not change the size of its jumps. -/
theorem maxLeap_moveUp (ctx : Context) (call answer : Phrase) (k d : Nat) :
    RuleHolds ctx call (answer.moveUp d) (.maxLeap k) ↔ RuleHolds ctx call answer (.maxLeap k) := by
  simp only [RuleHolds, pitches_moveUp]
  exact noLeap_moveUp k d _

/-- Moving the call and the answer up together does not change how far apart
they are. -/
theorem startNear_moveUp (ctx : Context) (call answer : Phrase) (k d : Nat) :
    RuleHolds ctx (call.moveUp d) (answer.moveUp d) (.startNear k) ↔
      RuleHolds ctx call answer (.startNear k) := by
  simp only [RuleHolds, pitches_moveUp, List.getLast?_map, List.head?_map]
  cases (pitches call).getLast? <;> cases (pitches answer).head? <;> simp [distance_add]

/-- If every pair of notes differs by the same amount before moving, it differs
by that amount after. -/
private theorem shifted_moveUp (d : Nat) (shift : Int) :
    ∀ a c : List Pitch,
      a.map (fun (p : Pitch) => ((p + d : Nat) : Int)) =
          c.map (fun (p : Pitch) => ((p + d : Nat) : Int) + shift) ↔
        a.map (fun (p : Pitch) => (p : Int)) = c.map (fun (p : Pitch) => (p : Int) + shift)
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | x :: a, y :: c => by
    simp only [List.map_cons, List.cons.injEq, shifted_moveUp d shift a c]
    have : ((x + d : Nat) : Int) = ((y + d : Nat) : Int) + shift ↔
        (x : Int) = (y : Int) + shift := by omega
    rw [this]

/-- Moving the call and the answer up together keeps the melody shape, so
`sequence` gives the same result. -/
theorem sequence_moveUp (ctx : Context) (call answer : Phrase) (n d : Nat) :
    RuleHolds ctx (call.moveUp d) (answer.moveUp d) (.sequence n) ↔
      RuleHolds ctx call answer (.sequence n) := by
  simp only [RuleHolds, pitches_moveUp, List.length_map, ← List.map_take, List.map_map,
    Function.comp_def]
  constructor
  · rintro ⟨h1, h2, shift, hs, h⟩
    exact ⟨h1, h2, shift, hs, (shifted_moveUp d shift _ _).mp h⟩
  · rintro ⟨h1, h2, shift, hs, h⟩
    exact ⟨h1, h2, shift, hs, (shifted_moveUp d shift _ _).mpr h⟩

end Blues
