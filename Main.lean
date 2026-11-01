import SoundAndComplete
import Lean.Data.Json

/-!
# The Lean program the app runs

* `sound-and-complete serve`: the bridge to the browser app. Reads one JSON
  request per line on stdin, writes one JSON reply per line on stdout. Every
  decision (the gate, the hint answer, the report card, the conflict warning)
  is made by the proven functions in `App.lean`. This file only converts JSON.
* `sound-and-complete` with no arguments: a short terminal demo.

This JSON glue is trusted, not proven (see the README).

## Requests

```
{"op":"conflict","exchange":0,"rules":[RULE...]}
  -> {"conflict":true|false}
{"op":"gate","exchange":0,"rules":[RULE...],"proposals":[PHRASE...]}
  -> {"chosen":index|null,"hint":PHRASE|null}
{"op":"grade","exchange":0,"rules":[RULE...],"call":PHRASE,"played":PHRASE}
  -> {"results":[true|false...]}      (one per rule, same order)
{"op":"gradeMany","exchange":0,"rules":[RULE...],"call":PHRASE,"answers":[PHRASE...]}
  -> {"first":index|null}             (first playable answer that keeps every rule)
```

PHRASE: an array of 24 entries, each `null` or a MIDI note number.
RULE: `{"rule":"startNear","frets":2}` and so on; see `parseRule`.
-/

open Blues Lean

/-! ## JSON to Lean -/

def parsePhrase (j : Json) : Except String Phrase := do
  let arr ← j.getArr?
  arr.toList.mapM fun x =>
    match x with
    | .null => pure .rest
    | _ => do let p ← x.getNat?; pure (.note p)

def phraseToJson (ph : Phrase) : Json :=
  .arr <| ph.toArray.map fun
    | .rest => Json.null
    | .note p => toJson p

def parseTone : String → Except String ChordTone
  | "root" => pure .root
  | "third" => pure .third
  | "fifth" => pure .fifth
  | "seventh" => pure .seventh
  | t => throw s!"unknown chord tone {t}"

def parseRule (j : Json) : Except String Rule := do
  let nat (k : String) : Except String Nat := j.getObjValAs? Nat k
  match ← j.getObjValAs? String "rule" with
  | "echoRhythm" => pure .echoRhythm
  | "echoSomeRhythm" => return .echoSomeRhythm (← nat "k")
  | "sequence" => return .sequence (← nat "n")
  | "sayLess" => pure .sayLess
  | "startNear" => return .startNear (← nat "frets")
  | "maxLeap" => return .maxLeap (← nat "frets")
  | "chordToneOnBeat" => return .chordToneOnBeat (← parseTone (← j.getObjValAs? String "tone")) (← nat "beat")
  | "turnaroundTarget" => return .turnaroundTarget (← nat "note") (← nat "beat")
  | "avoid" => return .avoid (← nat "note")
  | "stayBetween" => return .stayBetween (← nat "low") (← nat "high")
  | "maxNotesPerBar" => return .maxNotesPerBar (← nat "n")
  | "syncopate" => pure .syncopate
  | "leaveSpace" => return .leaveSpace (← nat "slots")
  | r => throw s!"unknown rule {r}"

def parseContext (j : Json) : Except String Context := do
  let e ← j.getObjValAs? Nat "exchange"
  if h : e < 3 then pure ⟨⟨e, h⟩⟩ else throw "exchange must be 0, 1 or 2"

/-! ## Answering one request -/

def handle (j : Json) : Except String Json := do
  let ctx ← parseContext j
  let rules ← (← j.getObjValAs? (Array Json) "rules").toList.mapM parseRule
  match ← j.getObjValAs? String "op" with
  | "conflict" =>
    return Json.mkObj [("conflict", toJson (knownConflict ctx rules))]
  | "gate" =>
    let proposals ← (← j.getObjValAs? (Array Json) "proposals").toList.mapM parsePhrase
    -- The proven gate picks the call; we only report which proposal it was.
    match chooseCall ctx rules proposals with
    | none => return Json.mkObj [("chosen", Json.null), ("hint", Json.null)]
    | some call =>
      let idx := proposals.idxOf call
      let hint := match findAnswer ctx call rules with
        | some a => phraseToJson a
        | none => Json.null
      return Json.mkObj [("chosen", toJson idx), ("hint", hint)]
  | "grade" =>
    let call ← parsePhrase (← j.getObjVal? "call")
    let played ← parsePhrase (← j.getObjVal? "played")
    let results := (grade ctx call rules played).map (·.2)
    return Json.mkObj [("results", toJson results)]
  | "gradeMany" =>
    -- The first candidate answer that keeps every rule, judged by the proven grader.
    let call ← parsePhrase (← j.getObjVal? "call")
    let answers ← (← j.getObjValAs? (Array Json) "answers").toList.mapM parsePhrase
    let ok (a : Phrase) := isPlayable a && (grade ctx call rules a).all (·.2)
    return Json.mkObj [("first", match answers.findIdx? ok with
      | some i => toJson i
      | none => Json.null)]
  | op => throw s!"unknown op {op}"

partial def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break  -- end of input
    if line.trimAscii.isEmpty then continue
    let reply := match Json.parse line >>= handle with
      | .ok r => r
      | .error e => Json.mkObj [("error", toJson e)]
    stdout.putStrLn reply.compress
    stdout.flush

/-! ## Terminal demo -/

def showPhrase (ph : Phrase) : String :=
  " ".intercalate ((notes ph).map fun (s, p) => s!"{noteName p}@{s}")

def demo : IO Unit := do
  let ctx : Context := ⟨0⟩
  let rules : List Rule :=
    [.startNear 2, .sayLess, .maxLeap 5, .chordToneOnBeat .third 5, .stayBetween 52 69, .syncopate]
  IO.println "A minor blues, first exchange: you answer in bars 3-4 over Am7."
  IO.println s!"Your rules: {repr rules}"
  if knownConflict ctx rules then
    IO.println "These rules can never all hold. Change them before playing."
    return
  let proposals : List Phrase := [lowCall, call1]
  for p in proposals do
    let verdict := if callIsGood ctx rules p then "accepted" else "rejected (no valid answer)"
    IO.println s!"  LLM proposes {showPhrase p}: {verdict}"
  match chooseCall ctx rules proposals with
  | none => IO.println "No proposal can be answered. Ask the LLM again."
  | some call =>
    IO.println s!"App plays: {showPhrase call}"
    match findAnswer ctx call rules with
    | some ans => IO.println s!"One answer that obeys your rules: {showPhrase ans}"
    | none => IO.println "(cannot happen if the theorems hold)"

def main (args : List String) : IO Unit := do
  match args with
  | ["serve"] => serve
  | _ => demo
