import SoundAndComplete
open Blues

def timeIt (label : String) (f : Unit → IO String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r ← f ()
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1 - t0} ms  {r}"

def layerSizes (c : Checker (List Mem)) (n : Nat) : IO Unit := do
  let mut l := [(c.init, ([] : Phrase))]
  let mut sizes := #[]
  for k in [0:n] do
    l := nextLayer c k l
    sizes := sizes.push l.length
  IO.println s!"  layer sizes: {sizes}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let which := (args.head?.bind String.toNat?).getD 99
  let cases : List (String × List Rule) :=
    [ ("maxLeap 3", [.maxLeap 3]),
      ("sayLess+maxLeap", [.sayLess, .maxLeap 5]),
      ("rules1 (12 rules)", rules1),
      ("seq4+maxLeap+perBar4+chordTone",
        [.sequence 4, .maxLeap 5, .maxNotesPerBar 4, .chordToneOnBeat .third 5]) ]
  for (name, rules) in (if which == 99 then cases else [cases[which]!]) do
    layerSizes (answerChecker ctx0 call1 rules) 24
    timeIt name fun _ => pure s!"{(findAnswer ctx0 call1 rules).map notes}"
