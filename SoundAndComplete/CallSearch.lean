import SoundAndComplete.App

/-!
# Can any call work with these rules? (`findCall`)

Before you play, the app asks: is there any call at all that is playable and
has an answer obeying all your rules? If not, the rules are impossible, and the
app says so.

There are far too many calls to try one by one. But a call only matters
through a few things: where its notes start, how many notes it has, its first
few notes (for `sequence`), and its last note (for `startNear`). So for each
answer we build one "best" call (`bestCall`) and search over answers only.

The best call depends on a shift `s`: its first notes are the answer's first
notes moved down by `s` (this is what `sequence` asks for). We try the shifts
in `callShifts`. `CallSearchProofs.lean` proves that if any call works, the
best call works for one of these shifts, with some answer.

The best call is only evidence that the rules can be played. It is not meant to
sound good: without `echoRhythm` it has a note in every slot.

Speed: a quick test that is the same for every shift runs first
(`quickChecker`), and only some rule sets need all 96 shifts (`needsAllShifts`).
-/

namespace Blues

/-- The longest `sequence n` rule in the list, or 0 if there is none. -/
def seqLength : List Rule → Nat
  | [] => 0
  | .sequence n :: rs => max n (seqLength rs)
  | _ :: rs => seqLength rs

example : seqLength [.sayLess, .sequence 2, .sequence 3] = 3 := rfl

/-- A call with a note in every one of its 24 slots. -/
def fullCall : Phrase := List.replicate phraseSlots (.note 60)

/-- Put the notes `ps`, in order, into the note slots of `w`. Rests stay rests.
If `ps` runs out, the remaining notes of `w` stay as they are. -/
def fillNotes : List Pitch → Phrase → Phrase
  | _, [] => []
  | ps, .rest :: w => .rest :: fillNotes ps w
  | p :: ps, .note _ :: w => .note p :: fillNotes ps w
  | [], .note q :: w => .note q :: fillNotes [] w

example : fillNotes [50, 52] [.note 60, .rest, .note 61] = [.note 50, .rest, .note 52] := rfl

/-- Move a note down by `s` frets (up, if `s` is negative). -/
def shiftDown (s : Int) (p : Pitch) : Pitch := ((p : Int) - s).toNat

/-- The notes of the best call, in order: the answer's first `n` notes moved
down by `s`, then the answer's first note again and again. -/
def bestCallNotes (n : Nat) (s : Int) (ps : List Pitch) : List Pitch :=
  (ps.take n).map (shiftDown s) ++ List.replicate phraseSlots (ps.headD 60)

/-- The best call for `answer`. With `echoRhythm` it has the answer's rhythm;
otherwise it has a note in every slot. Its notes are `bestCallNotes`. -/
def bestCall (rules : List Rule) (s : Int) (answer : Phrase) : Phrase :=
  fillNotes (bestCallNotes (seqLength rules) s (pitches answer))
    (if rules.contains .echoRhythm then answer else fullCall)

/-! ## Checkers that read only the answer

Each one says whether the answer obeys a rule when the call is `bestCall`. -/

/-- Note `p` moved down by `s` is still on the guitar. -/
def shiftedOnGuitar (s : Int) (p : Pitch) : Bool :=
  (guitarLow : Int) ≤ (p : Int) - s && (p : Int) - s ≤ (guitarHigh : Int)

/-- The answer's first `n` notes, moved down by `s`, are all on the guitar.
(Then the best call is playable.) -/
def shiftedOnGuitarChecker (n : Nat) (s : Int) : Checker Mem where
  init := Mem.start
  step _ m x :=
    match x with
    | .rest => m
    | .note p =>
      if !m.ok || n ≤ m.count then m
      else if shiftedOnGuitar s p then { count := m.count + 1 } else Mem.fail
  accept m := m.ok
  dead m := !m.ok

/-- `startNear k` against the best call. Passes when the answer has more than
`n` notes, or (if `restOk`) fewer than 24 notes, or else when its last note,
moved down by `s`, is within `k` frets of its first note. It remembers the
note count (up to `n + 1`), the first note, and whether the latest note is near
enough (`count2 = 1`). -/
def startNearShifted (n : Nat) (s : Int) (k : Nat) (restOk : Bool) : Checker Mem where
  init := Mem.start
  step _ m x :=
    match x with
    | .rest => m
    | .note p =>
      if n < m.count then m
      else if n ≤ m.count then { count := n + 1 }
      else
        let first := m.note.getD p
        { count := m.count + 1, note := some first,
          count2 := if distance (shiftDown s p) first ≤ k then 1 else 0 }
  accept m := n < m.count || (restOk && m.count < phraseSlots) || m.count2 == 1

/-- Without `echoRhythm` (and with short sequences), the best call ends on the
answer's first note, so `startNear` always holds. -/
def nearIsFree (rules : List Rule) : Bool :=
  !rules.contains .echoRhythm && seqLength rules < phraseSlots

/-- For each rule: a checker on the answer alone that passes exactly when the
answer obeys the rule against the best call (with shift `s`). -/
def bestCallRuleChecker (ctx : Context) (rules : List Rule) (s : Int) :
    Rule → Checker Mem
  | .echoRhythm => alwaysPass
  | .echoSomeRhythm k => ruleChecker ctx (CallInfo.of fullCall) (.echoSomeRhythm k)
  -- The answer has at least `n` notes.
  | .sequence n => ruleChecker ctx (CallInfo.of fullCall) (.echoSomeRhythm n)
  | .sayLess =>
    if rules.contains .echoRhythm then neverPass
    else ruleChecker ctx (CallInfo.of fullCall) .sayLess
  | .startNear k =>
    if nearIsFree rules then alwaysPass
    else startNearShifted (seqLength rules) s k (!rules.contains .echoRhythm)
  | r => ruleChecker ctx (CallInfo.of fullCall) r

/-- All the checkers for an answer to the best call with shift `s`: the answer
is playable, the best call is playable, and every rule holds. -/
def bestCallChecker (ctx : Context) (rules : List Rule) (s : Int) : Checker (List Mem) :=
  allOf (playableChecker :: shiftedOnGuitarChecker (seqLength rules) s ::
    rules.map (bestCallRuleChecker ctx rules s))

/-- The shift matters for more than "is the best call on the guitar": there is a
`startNear` rule, and the best call's last note may be a moved answer note. -/
def needsAllShifts (rules : List Rule) : Bool :=
  rules.any (fun r => match r with | .startNear _ => true | _ => false) && !nearIsFree rules

/-- The shifts to try. Without a `sequence` rule the shift does not matter.
Usually only its sign matters (1 or -1 keeps the moved notes on the guitar,
unless they reach both ends). Otherwise: every nonzero shift up to the
guitar's range, smallest first. -/
def callShifts (rules : List Rule) : List Int :=
  if seqLength rules = 0 then [1]
  else if needsAllShifts rules then
    (List.range (guitarHigh - guitarLow)).flatMap fun i =>
      [((i + 1 : Nat) : Int), -((i + 1 : Nat) : Int)]
  else [1, -1]

/-- One rule's part of `quickChecker`: `startNear` always passes; every other
rule uses its checker for the best call (which does not depend on the shift). -/
def quickRuleChecker (ctx : Context) (rules : List Rule) : Rule → Checker Mem
  | .startNear _ => alwaysPass
  | r => bestCallRuleChecker ctx rules 1 r

/-- A quick first test, the same for every shift: the answer is playable and
passes every rule's checker, except that `startNear` is skipped. If no answer
passes this, no call can work, and we need not try the shifts. -/
def quickChecker (ctx : Context) (rules : List Rule) : Checker (List Mem) :=
  allOf (playableChecker :: rules.map (quickRuleChecker ctx rules))

/-- Find a call the app may play and an answer to it, or `none` if no call can
work with these rules. The result is checked again with the proven checks
before it is returned. -/
def findCall (ctx : Context) (rules : List Rule) : Option (Phrase × Phrase) :=
  if (search (quickChecker ctx rules) phraseSlots).isNone then none else
  (callShifts rules).findSome? fun s =>
    match search (bestCallChecker ctx rules s) phraseSlots with
    | none => none
    | some answer =>
      let call := bestCall rules s answer
      if isPlayable call && isCorrectAnswer ctx call rules answer then some (call, answer)
      else none

end Blues
