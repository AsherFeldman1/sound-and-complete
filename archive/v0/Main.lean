import SoundAndComplete

/-!
Placeholder demo for the terminal. It runs one turnaround exchange with fake
LLM proposals. The real app will put a browser UI (audio, pitch detection,
LLM calls) in front of this Lean core.
-/

open Blues

def showPhrase (ph : Phrase) : String := " ".intercalate (ph.map noteName)

def main : IO Unit := do
  let ctx : Context := ⟨9, 2⟩  -- A blues, turnaround
  let rules : List Rule := [.startNear 3, .maxLeap 4, .landOn .root, .turnaroundEndsOn 4, .stayBetween 52 64]
  IO.println s!"Key of A, turnaround. Your answer ends over {letterName ctx.endChord.root}7."
  IO.println s!"Rules: {repr rules}"
  if !rulesWorkable ctx rules then
    IO.println "Your rules can't be satisfied here, whatever the AI plays."
    return
  -- Stand-in for the LLM: some proposals the gate should reject, then a good one.
  let proposals : List Phrase := [[45, 48, 50, 52, 41], [69, 72, 74, 76, 79], [57, 60, 62, 64]]
  for p in proposals do
    IO.println s!"  LLM proposes {showPhrase p}: {if callIsGood ctx rules p then "accepted" else "rejected"}"
  match chooseCall ctx rules proposals with
  | none => IO.println "No proposal can be answered. Ask the LLM again."
  | some call =>
    IO.println s!"App plays: {showPhrase call}"
    match findAnswer ctx call rules with
    | some ans => IO.println s!"One answer that obeys your rules: {showPhrase ans}"
    | none => IO.println "(unreachable if the theorems hold)"
    let played : Phrase := [62, 60, 57, 52]
    IO.println s!"You played: {showPhrase played}"
    for (r, ok) in grade ctx call rules played do
      IO.println s!"  {if ok then "✓" else "✗"} {repr r}"
