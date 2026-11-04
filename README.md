# Sound and Complete

A hackathon project for Vibecheck, the formal methods hackathon. It won first place.

Blues call-and-response practice in A minor. You pick rules for your playing
("start near the AI's last note", "say less than the call", "land on the third
on beat 1 of bar 2"). An LLM plays a 2-bar call over a shuffle backing track.
You answer on your guitar. At the end you see which rules you kept.

The LLM is not trusted. Before its call is played, a checker written in Lean
confirms that at least one answer obeys all your rules. If none of its calls
passes, the app plays a call the proof found. The proofs show this check is
exact: the gate picks the first call that is playable and can be answered.

```
make install && make run    # build, then open the app at http://localhost:8765
make audit                  # what each theorem depends on, and its axioms
make comparator             # lake check + lake comparator in Docker (needs Docker)
make test                   # browser-side tests (audio, rules, fretboard)
make demo                   # terminal demo of the Lean core
make bench                  # time the answer search
```

To have Claude write the calls, put `ANTHROPIC_API_KEY=...` in a `.env` file in the
project root (it is git-ignored), or set it in your shell, before `make run`.
Without a key, each call is the one found by the proven search (`findCall`): always answerable, but plain.
Use Chrome, wear headphones, and calibrate latency once in the **Input lab**
(link at the top right). Set the Mode switch to **Demo** to play without a guitar.

## How it works

1. **Spec.** Each rule has a short readable definition (`Spec.lean`).
2. **Checkers.** Each rule also has a checker that reads an answer slot by slot,
   keeping a small memory (`Checkers.lean`). A theorem says each checker passes
   exactly the answers that obey its rule.
3. **Search.** To decide whether a call can be answered, the search builds
   answers slot by slot, keeping one example per distinct memory
   (`Search.lean`). Two partial answers with the same memory finish the same
   way, so nothing is lost: the search is sound and complete.
4. **Impossible rules.** Before you play, the app decides whether any call at
   all could work with your rules (`CallSearch.lean`). A call only matters
   through its rhythm, its first few notes and its last note, so for each
   answer one "best" call is enough, and the same search runs over answers.
   If no call can work, the app says so. There is no list of known bad
   combinations: the answer comes from proof, for every rule set.

## Where things are

| File | What it is |
|---|---|
| `SoundAndComplete/Music.lean` | Notes, the shuffle grid, the A minor blues. Part of the spec. |
| `SoundAndComplete/Spec.lean` | **What the rules mean.** Read this to trust the app. |
| `SoundAndComplete/SpecExamples.lean` | Proofs that the spec accepts real answers, rejects bad ones, and catches rule conflicts. |
| `SoundAndComplete/Search.lean` | Generic checkers and the search. |
| `SoundAndComplete/Checkers.lean` | One checker per rule. |
| `SoundAndComplete/App.lean` | Answer search, grading, the gate. |
| `SoundAndComplete/CallSearch.lean` | `findCall`: can any call work with these rules? |
| `SoundAndComplete/CallSearchProofs.lean` | Why one "best" call per answer is enough. |
| `SoundAndComplete/Theorems.lean` | **The promises**, each explained in plain words. |
| `SoundAndComplete/TheoremExamples.lean` | Each promise used on a real call, so none of them is empty. |
| `SoundAndComplete/Challenge.lean` | The statements alone. Comparator checks that the proofs match them. |
| `SoundAndComplete/CheckerTests.lean` | Tests that run on every build. |
| `Main.lean` | The bridge the app runs: JSON in, JSON out. Every decision comes from the proven functions. |
| `web/` | Browser app: `server.js` (API + Claude), `main.js` (UI), `audio/band.js` (backing band and lead guitar), `audio/input.js` (mic → notes). `lab.html` tunes detection. |

## The promises

1. **Each checker means its rule** (`ruleChecker_correct`).
2. **Honest report card**: each mark is right (`grade_correct`), and each mark sits next to its own rule (`grade_keeps_rule_order`).
3. **Exact search**: suggested answers are real (`findAnswer_sound`), and none are missed (`findAnswer_complete`).
4. **Safe calls**: every call the app plays can be answered, whatever the LLM proposes. That covers a call the gate picks (`chooseCall_safe`) and the call the proof found (`findCall_sound`).
5. **Exact gate**: it picks the first proposal that is playable and can be answered (`chooseCall_eq_some_iff`). If it picks none, every proposal was bad (`chooseCall_rejects_only_bad`).
6. **Impossible rules, decided**: "no call can work with these rules" is said exactly when it is true. A found call is a real good call with a real answer (`findCall_sound`), and if any call could work, one is found (`findCall_complete`).
7. **Honest hint**: the "answer that keeps every rule" shown after a song does keep every rule (`isCorrectAnswer_iff`).

The promises hold for all 11 rules, with no `sorry` (`make audit`).

The report card judges each rule alone, so silence passes rules that only forbid
something, such as "never play A". A call or answer the app suggests always has
at least one note.

## Trusted (not proven)

- Pitch and onset detection: the notes and timings the app hears are what you played.
- Snapping your timing to the 24-slot grid.
- The JSON bridge (`Main.lean`, `web/server.js`, `web/lean.js`) that passes data to and from the Lean core.
- The LLM is **not** trusted: its calls only play if the proven gate accepts them. If none
  passes, the server plays the call `findCall` found. The server chooses between those two,
  and both are proven good. The
  "answer that keeps every rule" comes from unproven code, but the proven check picks it
  (falling back to the proven search's own answer).
- The Lean compiler, runtime and kernel. The proofs use only Lean's three standard
  axioms: `propext`, `Classical.choice` and `Quot.sound`.
- `Challenge.lean` imports the real definitions, so Comparator pins the theorem
  statements, not `Spec.lean`. A person must review changes to the spec.

## Sound credits

The band plays recorded samples. `make install` downloads them (`web/samples/fetch.mjs`; the list is in `web/audio/sounds.js`).
Pick the instruments on the **Band sounds** page (`/sounds.html`).

- Lead guitars "Epiphone" and "Archtop": [Karoryfer](https://github.com/sfzinstruments) Emilyguitar and Shinyguitar by D. Smolken (CC0). They were recorded direct, so the app plays them through the amp below.
- Amp: a Fender Deluxe Reverb [Neural Amp Modeler](https://github.com/sdatkinson/neural-amp-modeler) capture, a Celestion speaker cabinet impulse response and a spring reverb impulse response (`web/tone/`), from [TONE3000](https://www.tone3000.com)'s [neural-amp-modeler-wasm](https://github.com/tone-3000/neural-amp-modeler-wasm) demo library (MIT), run in the browser by its WebAssembly engine (npm `neural-amp-modeler-wasm`, MIT). Both your guitar and the AI's guitar play through it.
- Other guitars, electric bass, organ: [midi-js-soundfonts](https://github.com/gleitz/midi-js-soundfonts) by Benjamin Gleitzman. The FluidR3 GM set is MIT; the MusyngKite set is CC BY-SA 3.0.
- Upright bass: d. smolken's double bass, via [smpldsnds](https://github.com/smpldsnds) (CC0).
- Rhodes: jRhodes3d by Jeff Learman, via smpldsnds (samples CC BY-NC: non-commercial use only).
- Studio drum kit: Hydrogen GM kit, via smpldsnds (GPL-2.0).
- "Old" sounds: [tonejs-instruments](https://github.com/nbrosowsky/tonejs-instruments) by Nicholas Brosowsky (no license stated) and the [Tone.js audio](https://github.com/Tonejs/audio) drum kits.

If the samples are missing, the band falls back to its built-in synthesized sounds.

## Comparator

`SoundAndComplete/Challenge.lean` restates the eleven main theorems with no
proof; `comparator.json` lists them and allows only the standard axioms
(`propext`, `Quot.sound`, `Classical.choice`). `make comparator` runs
`lake check` and `lake comparator` in a Linux container (they need the Linux
`bwrap` sandbox). Both pass, and `comparator/run.sh --paranoid` also passes on
every bundled kernel: Lean default and paranoid, lean4lean, nanoda, con-leche
and con-ron.
