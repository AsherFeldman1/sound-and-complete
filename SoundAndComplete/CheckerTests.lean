import SoundAndComplete.App
import SoundAndComplete.SpecExamples

/-!
# Tests: the running code agrees with the spec examples

Each `#guard` fails the build if the code gives the wrong result. These are
tests, not proofs: they check particular cases. The proofs in `Theorems.lean`
cover every case.
-/

namespace Blues

/-! ## Checkers agree with `SpecExamples.lean` -/

-- `answer1_satisfies` proves `answer1` obeys all of `rules1`. The checkers agree:
#guard rules1.all (checkRule ctx0 call1 answer1)
#guard isPlayable answer1 && isPlayable call1

-- The spec rejects these; so must the checkers.
#guard !checkRule ctx0 call1 (Phrase.ofNotes [(0, 60)]) (.leaveSpace 3)
#guard !checkRule ctx0 call1 answer1 (.chordToneOnBeat .root 5)
#guard !checkRule ctx0 call1 (Phrase.ofNotes [(0, 57), (3, 60)]) .syncopate
#guard !checkRule ctx0 call1 call1 .sayLess
#guard !checkRule ⟨2⟩ call1 answer1 (.turnaroundTarget 4 5)
#guard !isPlayable (Phrase.ofNotes [])

/-! ## One check per rule, pass and fail -/

-- echoRhythm: same starts as the call passes, one moved start fails.
#guard checkRule ctx0 call1 (Phrase.ofNotes [(0, 57), (3, 57), (6, 57), (8, 57)]) .echoRhythm
#guard !checkRule ctx0 call1 (Phrase.ofNotes [(0, 57), (3, 57), (6, 57), (9, 57)]) .echoRhythm
-- sequence 3: E4 D4 C4 moved up 5 is A4 G4 F4.
#guard checkRule ctx0 call1 (Phrase.ofNotes [(0, 69), (5, 67), (7, 65)]) (.sequence 3)
#guard !checkRule ctx0 call1 (Phrase.ofNotes [(0, 69), (5, 67), (7, 64)]) (.sequence 3)
-- startNear 2: the call ends on E4 (64).
#guard checkRule ctx0 call1 (Phrase.ofNotes [(0, 62)]) (.startNear 2)
#guard !checkRule ctx0 call1 (Phrase.ofNotes [(0, 61)]) (.startNear 2)
-- maxLeap 5
#guard checkRule ctx0 call1 (Phrase.ofNotes [(0, 57), (3, 62)]) (.maxLeap 5)
#guard !checkRule ctx0 call1 (Phrase.ofNotes [(0, 57), (3, 63)]) (.maxLeap 5)
-- maxNotesPerBar 2: three notes in bar 1 fails, two per bar passes.
#guard checkRule ctx0 call1 (Phrase.ofNotes [(0, 57), (3, 57), (12, 57), (15, 57)]) (.maxNotesPerBar 2)
#guard !checkRule ctx0 call1 (Phrase.ofNotes [(0, 57), (3, 57), (6, 57)]) (.maxNotesPerBar 2)
-- chordToneOnBeat over E7 in the turnaround: G# (68) is its third.
#guard checkRule ⟨2⟩ call1 (Phrase.ofNotes [(12, 68)]) (.chordToneOnBeat .third 5)
#guard !checkRule ⟨2⟩ call1 (Phrase.ofNotes [(12, 67)]) (.chordToneOnBeat .third 5)
-- An out-of-range beat can never be satisfied.
#guard !checkRule ctx0 call1 answer1 (.chordToneOnBeat .third 9)
-- turnaroundTarget does nothing outside the turnaround.
#guard checkRule ctx0 call1 (Phrase.ofNotes [(0, 57)]) (.turnaroundTarget 4 5)

/-! ## The search -/

-- `call1` has an answer under `rules1`, and the answer really passes.
#guard match findAnswer ctx0 call1 rules1 with
  | some a => a.length == phraseSlots && isPlayable a && rules1.all (checkRule ctx0 call1 a)
  | none => false

-- Proven impossible in `SpecExamples.lean`: echo exactly + say less.
#guard findAnswer ctx0 call1 [.echoRhythm, .sayLess] == none
-- Sequence 4 needs at least 4 notes, but say less allows at most 3 against a
-- 4-note call: impossible.
#guard findAnswer ctx0 call1 [.sequence 4, .sayLess] == none
-- Land on the root (A) on beat 1, but never play A: impossible.
#guard findAnswer ctx0 call1 [.chordToneOnBeat .root 1, .avoid 9] == none

/-! ## The gate -/

-- With "start within 2 frets", a call ending on A2 (45) can only be answered
-- from 43 to 47; "stay between E3 and E4" (52–64) rules that out. The gate skips
-- it and picks the second proposal.
def lowCall : Phrase := Phrase.ofNotes [(0, 40), (3, 45)]
def rulesHigh : List Rule := [.startNear 2, .stayBetween 52 64]
#guard chooseCall ctx0 rulesHigh [lowCall, call1] == some call1
#guard chooseCall ctx0 rulesHigh [lowCall] == none
-- An unplayable proposal (too short) is skipped even if it could be answered.
#guard chooseCall ctx0 [] [[.note 60], call1] == some call1

/-! ## Grading and warnings -/

#guard grade ctx0 call1 [.sayLess, .syncopate] answer1 == [(.sayLess, true), (.syncopate, true)]
#guard grade ctx0 call1 [.sayLess, .leaveSpace 6] answer1 == [(.sayLess, true), (.leaveSpace 6, false)]
#guard knownConflict ctx0 [.echoRhythm, .maxLeap 3, .sayLess]
#guard knownConflict ctx0 [.chordToneOnBeat .third 0]
#guard !knownConflict ctx0 rules1

end Blues
