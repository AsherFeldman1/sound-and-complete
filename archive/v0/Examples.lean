import SoundAndComplete.Theorems

/-!
# Examples: checking that the spec means what we think

`CLAUDE.md` asks for three kinds of checks on a spec:

1. **The hypotheses can hold.** Each main theorem should apply to a real case,
   or it says nothing.
2. **The spec rejects bad behavior.** We prove that known-bad answers fail.
3. **Unit tests.** `#guard` fails the build if the code gives a wrong result.

All examples here are in A (key = 9).
-/

namespace Blues

/-- First exchange in A. The answer ends in bar 4, over A7. -/
def ctxA : Context := ⟨9, 0⟩

/-- The turnaround in A. The answer ends in bar 12, over E7. -/
def ctxATurn : Context := ⟨9, 2⟩

/-- A call: A3 then C4. -/
def callAC : Phrase := [57, 60]

/-- Rules: start within 3 frets of the call, no leaps over 5 frets, land on the root. -/
def rulesBasic : List Rule := [.startNear 3, .maxLeap 5, .landOn .root]

/-! ## 1. The hypotheses can hold -/

/-- A3 alone is a correct answer: it is 3 frets from C4 and it is the root of A7. -/
example : Satisfies ctxA callAC rulesBasic [57] := by
  refine ⟨⟨by simp, by decide, ?_⟩, ?_⟩
  · simp [OnGuitar, guitarLow, guitarHigh]
  · simp [rulesBasic, RuleHolds, NoLeapBiggerThan, EndsOn, IsTone, Context.endChord,
      Context.answerEndBar, chordAtBar, chordStep, ctxA, callAC, distance, pitchClass,
      ChordTone.semitones]

/-- So `callAC` is a good call under `rulesBasic`. `chooseCall_safe` can apply. -/
example : GoodCall ctxA rulesBasic callAC := by
  refine ⟨⟨by simp [callAC], by decide, ?_⟩, ⟨[57], ?_⟩⟩
  · simp [callAC, OnGuitar, guitarLow, guitarHigh]
  · refine ⟨⟨by simp, by decide, ?_⟩, ?_⟩
    · simp [OnGuitar, guitarLow, guitarHigh]
    · simp [rulesBasic, RuleHolds, NoLeapBiggerThan, EndsOn, IsTone, Context.endChord,
        Context.answerEndBar, chordAtBar, chordStep, ctxA, callAC, distance, pitchClass,
        ChordTone.semitones]

/-! ## 2. The spec rejects bad answers -/

/-- E4 is not a correct answer: it is the fifth of A7, not the root. -/
example : ¬ Satisfies ctxA callAC rulesBasic [64] := by
  intro ⟨_, h⟩
  have := h (.landOn .root) (by simp [rulesBasic])
  simp [RuleHolds, EndsOn, IsTone, Context.endChord, Context.answerEndBar, chordAtBar,
    chordStep, ctxA, pitchClass, ChordTone.semitones] at this

/-- A two-octave jump breaks a 5-fret leap limit. -/
example : ¬ RuleHolds ctxA callAC [45, 69] (.maxLeap 5) := by
  simp [RuleHolds, NoLeapBiggerThan, distance]

/-- An empty answer is never correct. You have to play something. -/
example : ¬ Satisfies ctxA callAC [] [] := by
  intro ⟨⟨h, _⟩, _⟩
  exact h rfl

/-- In A, "land on the root" plus "never play A" cannot both hold. -/
example : ¬ Answerable ctxA callAC [.landOn .root, .avoid 9] := by
  intro ⟨answer, ⟨hne, _⟩, h⟩
  have hland := h (.landOn .root) (by simp)
  have havoid := h (.avoid 9) (by simp)
  simp only [RuleHolds, EndsOn] at hland havoid
  match hlast : answer.getLast? with
  | none => simp_all
  | some p =>
    have hp : p ∈ answer := List.mem_of_getLast? hlast
    have := hland p hlast
    have := havoid p hp
    simp_all [IsTone, Context.endChord, Context.answerEndBar, chordAtBar, chordStep, ctxA,
      ChordTone.semitones]

/-! ## 3. Unit tests on the running code -/

#guard findAnswer ctxA callAC rulesBasic == some [57]
#guard checkAnswer ctxA callAC rulesBasic [57]
#guard !checkAnswer ctxA callAC rulesBasic [64]

-- Impossible rules: no answer, and `rulesWorkable` warns about it.
#guard findAnswer ctxA callAC [.landOn .root, .avoid 9] == none
#guard !rulesWorkable ctxA [.landOn .root, .avoid 9]
#guard rulesWorkable ctxA rulesBasic

-- The turnaround rule only matters on the turnaround.
#guard checkRule ctxA callAC [57] (.turnaroundEndsOn 4)
#guard !checkRule ctxATurn callAC [57] (.turnaroundEndsOn 4)

-- Gate: with your hand kept between E3 and E4, a call ending on F2 is too far
-- away to start near, so the gate skips it and picks the second proposal.
def rulesInPosition : List Rule := rulesBasic ++ [.stayBetween 52 64]
#guard chooseCall ctxA rulesInPosition [[40, 41], [57, 60]] == some [57, 60]
#guard chooseCall ctxA rulesInPosition [[40, 41]] == none
-- Without the position rule, F2 is fine: e.g. E2 then A2 works.
#guard match findAnswer ctxA [40, 41] rulesBasic with
  | some a => checkAnswer ctxA [40, 41] rulesBasic a
  | none => false

-- A longer answer is needed when the start and end are far apart.
#guard (findAnswer ctxA [72] [.startNear 0, .maxLeap 2, .landOn .root]).map List.length
  == some 3  -- C5, then B4 or Bb4, then A4

end Blues
