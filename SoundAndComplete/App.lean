import SoundAndComplete.Checkers

/-!
# What the app calls

* `findAnswer`: find an answer to a call that obeys every rule, or say there is none.
* `checkRule` and `grade`: judge what you played.
* `isCorrectAnswer`: does a suggested answer keep every rule?
* `chooseCall`: the gate. Pick the first LLM-proposed call you can answer.
* `findCall` (in `CallSearch.lean`): before you play, decide whether any call
  at all can work with your rules.
-/

namespace Blues

/-- Does `answer` obey `rule`? -/
def checkRule (ctx : Context) (call answer : Phrase) (r : Rule) : Bool :=
  (ruleChecker ctx (CallInfo.of call) r).accepts answer

/-- The end-of-song report: each rule, and whether what you played obeyed it. -/
def grade (ctx : Context) (call : Phrase) (rules : List Rule) (played : Phrase) :
    List (Rule × Bool) :=
  rules.map fun r => (r, checkRule ctx call played r)

/-- Runnable version of `Playable`. -/
def isPlayable (ph : Phrase) : Bool :=
  ph.length == phraseSlots && playableChecker.accepts ph

/-- `answer` is playable and keeps every rule. Runnable version of `Satisfies`.
The app uses this to pick the musical answer it shows after a song. -/
def isCorrectAnswer (ctx : Context) (call : Phrase) (rules : List Rule) (answer : Phrase) : Bool :=
  isPlayable answer && (grade ctx call rules answer).all (·.2)

/-- All the checkers for an answer to `call`: playable, plus every rule. -/
def answerChecker (ctx : Context) (call : Phrase) (rules : List Rule) : Checker (List Mem) :=
  allOf (playableChecker :: rules.map (ruleChecker ctx (CallInfo.of call)))

/-- Find a correct answer to `call`, or `none` if there is none. -/
def findAnswer (ctx : Context) (call : Phrase) (rules : List Rule) : Option Phrase :=
  search (answerChecker ctx call rules) phraseSlots

/-- The call is playable and has a correct answer. Runnable version of `GoodCall`. -/
def callIsGood (ctx : Context) (rules : List Rule) (call : Phrase) : Bool :=
  isPlayable call && (findAnswer ctx call rules).isSome

/-- The gate. Given the calls the LLM proposed, in order, pick the first one
you can answer. `none` means: ask the LLM again. -/
def chooseCall (ctx : Context) (rules : List Rule) (proposals : List Phrase) : Option Phrase :=
  proposals.find? (callIsGood ctx rules)

end Blues
