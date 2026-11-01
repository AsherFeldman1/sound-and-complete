import SoundAndComplete.Spec

/-!
# Spec examples: does the spec mean what we think?

`CLAUDE.md` asks for two kinds of checks on a spec:

1. **The rules can be satisfied.** A real answer that obeys a realistic set of
   rules, so the theorems built on this spec are not empty promises. Every rule
   is shown holding in a case where it really applies.
2. **The spec rejects bad answers.** Every rule that can fail has an answer
   proven to break it.

Plus a limit worth knowing (silence obeys some rules), and a rule pair that can
never hold together. The app should warn about those before you play.
-/

namespace Blues

/-- First exchange: the answer is in bars 3–4, over Am7. -/
def ctx0 : Context := ⟨0⟩

/-- A call: E4 on beat 1, D4 on beat 2, C4 on beat 3, then E4 on the shuffle
"and" of beat 3. It starts going down and ends going up. -/
def call1 : Phrase := Phrase.ofNotes [(0, 64), (3, 62), (6, 60), (8, 64)]

/-- An answer: D4 on beat 2, C4 on the "and" of beat 3, C4 on beat 5
(bar 2, beat 1). -/
def answer1 : Phrase := Phrase.ofNotes [(3, 62), (8, 60), (12, 60)]

theorem call1_notes : notes call1 = [(0, 64), (3, 62), (6, 60), (8, 64)] := by decide
theorem answer1_notes : notes answer1 = [(3, 62), (8, 60), (12, 60)] := by decide

/-- Almost every rule at once. -/
def rules1 : List Rule :=
  [ .echoSomeRhythm 2      -- shares the call's starts on slots 3 and 8
  , .sequence 2            -- D4 C4 is the call's E4 D4, moved down 2
  , .sayLess               -- 3 notes against the call's 4
  , .startNear 2           -- D4 is 2 frets from the call's last note E4
  , .maxLeap 5
  , .chordToneOnBeat .third 5   -- C4 on beat 5; C is the third of Am7
  , .avoid 10              -- no B♭
  , .stayBetween 52 69
  , .maxNotesPerBar 2
  , .leaveSpace 3 ]        -- first note on slot 3

/-! ## 1. The rules can be satisfied -/

/-- `answer1` obeys every rule in `rules1`. -/
theorem answer1_satisfies : Satisfies ctx0 call1 rules1 answer1 := by
  refine ⟨⟨by decide, by simp [answer1_notes], ?_⟩, ?_⟩
  · simp [pitches, answer1_notes, OnGuitar, guitarLow, guitarHigh]
  · intro r hr
    simp only [rules1, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [RuleHolds, onsetSlots, pitches, call1_notes, answer1_notes]
    · decide
    · exact ⟨by decide, by decide, -2, by decide, by decide⟩
    · decide
    · simp [distance]
    · simp [NoLeapBiggerThan, distance]
    · refine ⟨by decide, by decide, 60, by decide, by unfold IsTone; decide⟩
    · simp [pitchClass]
    · simp
    · decide
    · intro s p h; simp at h; omega

/-- So `call1` is a call the app may play under `rules1`. -/
theorem call1_good : GoodCall ctx0 rules1 call1 :=
  ⟨⟨by decide, by simp [call1_notes], by
      simp [pitches, call1_notes, OnGuitar, guitarLow, guitarHigh]⟩,
   answer1, answer1_satisfies⟩

/-! ## 2. The spec rejects bad answers -/

/-- Playing on slot 0 breaks "leave a beat of space". -/
example : ¬ RuleHolds ctx0 call1 (Phrase.ofNotes [(0, 60)]) (.leaveSpace 3) := by
  intro h
  exact absurd (h 0 60 (by decide)) (by decide)

/-- C is not the root of Am7, so C on beat 5 breaks "root on beat 5". -/
example : ¬ RuleHolds ctx0 call1 answer1 (.chordToneOnBeat .root 5) := by
  simp only [RuleHolds, answer1_notes]
  rintro ⟨_, _, p, hp, ht⟩
  simp [beatSlot] at hp
  subst hp
  revert ht; unfold IsTone; decide

/-- Copying the call exactly breaks "sequence": the move must not be zero. -/
example : ¬ RuleHolds ctx0 call1 call1 (.sequence 2) := by
  simp only [RuleHolds, pitches, call1_notes]
  rintro ⟨-, -, shift, hs, h⟩
  simp at h
  omega

/-- The call's first two notes, E4 D4, moved up 5 to A4 G4: this obeys
"sequence 2". -/
example : RuleHolds ctx0 call1 (Phrase.ofNotes [(0, 69), (3, 67)]) (.sequence 2) := by
  have : notes (Phrase.ofNotes [(0, 69), (3, 67)]) = [(0, 69), (3, 67)] := by decide
  simp only [RuleHolds, pitches, call1_notes, this]
  exact ⟨by decide, by decide, 5, by decide, by decide⟩

/-- Four notes do not "say less" than a four-note call. -/
example : ¬ RuleHolds ctx0 call1 call1 .sayLess := by
  simp [RuleHolds]

/-- `answer1` starts its notes in different slots from the call. -/
example : ¬ RuleHolds ctx0 call1 answer1 .echoRhythm := by
  simp only [RuleHolds, onsetSlots, call1_notes, answer1_notes]
  decide

/-- `answer1` shares only two starts with the call (slots 3 and 8), not three. -/
example : ¬ RuleHolds ctx0 call1 answer1 (.echoSomeRhythm 3) := by
  simp only [RuleHolds, onsetSlots, call1_notes, answer1_notes]
  decide

/-- `answer1` plays D C C. The call starts E D C. The first two notes move down
2, but the third moves by 0, so this is not one shift. -/
example : ¬ RuleHolds ctx0 call1 answer1 (.sequence 3) := by
  simp only [RuleHolds, pitches, call1_notes, answer1_notes]
  rintro ⟨-, -, shift, -, h⟩
  simp at h
  omega

/-- `answer1` starts on D4, 2 frets from the call's last note E4, not 1. -/
example : ¬ RuleHolds ctx0 call1 answer1 (.startNear 1) := by
  simp only [RuleHolds, pitches, call1_notes, answer1_notes]
  intro h
  exact absurd (h 64 62 (by decide) (by decide)) (by decide)

/-- `answer1` steps from D4 to C4: 2 frets, more than 1. -/
example : ¬ RuleHolds ctx0 call1 answer1 (.maxLeap 1) := by
  simp [RuleHolds, pitches, answer1_notes, NoLeapBiggerThan, distance]

/-- `answer1` plays C, so it breaks "never play C". -/
example : ¬ RuleHolds ctx0 call1 answer1 (.avoid 0) := by
  simp only [RuleHolds, pitches, answer1_notes]
  intro h
  exact absurd (h 60 (by decide)) (by decide)

/-- `answer1` plays C4 (60), below the bottom of the position (61). -/
example : ¬ RuleHolds ctx0 call1 answer1 (.stayBetween 61 69) := by
  simp only [RuleHolds, pitches, answer1_notes]
  intro h
  exact absurd (h 60 (by decide)).1 (by decide)

/-- `answer1` has two notes in bar 1 (slots 3 and 8), more than 1. -/
example : ¬ RuleHolds ctx0 call1 answer1 (.maxNotesPerBar 1) := by
  simp only [RuleHolds, answer1_notes]
  decide

/-- The empty answer is never playable. You have to play something. -/
example : ¬ Playable (Phrase.ofNotes []) := by
  rintro ⟨_, h, _⟩
  exact h (by decide)

/-! ## 3. A rule that `rules1` does not test

`rules1` leaves out `echoRhythm` (it conflicts with `sayLess`), so it gets its
own real example. -/

/-- Same four starts as `call1`, with different notes. -/
theorem echoRhythm_can_hold :
    RuleHolds ctx0 call1 (Phrase.ofNotes [(0, 57), (3, 57), (6, 57), (8, 57)]) .echoRhythm := by
  simp only [RuleHolds]
  decide

/-! ## 4. A limit: silence obeys some rules -/

/-- Playing nothing obeys "never play A". A rule alone does not ask you to play;
`Playable` does that. So `Satisfies` rejects silence, but the report card, which
judges one rule at a time, can give it a check mark. -/
theorem silence_obeys_avoid : RuleHolds ctx0 call1 (Phrase.ofNotes []) (.avoid 9) := by
  have h : notes (Phrase.ofNotes []) = [] := by decide
  simp [RuleHolds, pitches, h]

/-! ## 5. Rule pairs that can never hold together -/

/-- "Echo the rhythm exactly" and "say less" contradict each other, for every
call: the same note starts means the same number of notes. -/
theorem echoRhythm_sayLess_conflict (ctx : Context) (call answer : Phrase) :
    ¬ (RuleHolds ctx call answer .echoRhythm ∧ RuleHolds ctx call answer .sayLess) := by
  rintro ⟨h1, h2⟩
  simp only [RuleHolds, onsetSlots] at h1 h2
  have := congrArg List.length h1
  simp at this
  omega

end Blues
