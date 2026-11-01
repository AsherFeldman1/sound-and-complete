# Lean 4 verification route: sound and complete search over length-24 sequences constrained by DFA rules

Scope: precedent for verified automata, regex and DP; certificate-based alternatives; concrete Lean 4 (v4.35, core and possibly Batteries, no Mathlib) design; effort estimates.
Note on sourcing: claims under "Cited Findings" have links. "Inferences" are my engineering judgement (design advice, effort guesses) and are not sourced. Version-sensitive API names are flagged.

## Q1. Verified automata, regex and DP precedent, and the proof patterns they use for product-automaton emptiness

### Takeaway
Product construction and emptiness are well trodden. Mathlib's `DFA` is the closest Lean 4 template: `evalFrom` is defined as `List.foldl step`, `inter` builds the product, and `accepts_inter` states that it recognises the intersection. Copy that shape into your own small file instead of importing Mathlib. Your problem then reduces to bounded-length emptiness of one product DFA, which a layered reachability DP decides. No existing Lean 4 library ships a verified "bounded-length DFA emptiness with witness" procedure, so you will write that part, but it is small.

### Cited Findings
- **Mathlib `DFA`:** the structure has three fields: `step : σ → α → σ`, `start : σ`, `accept : Set σ` ([Mathlib.Computability.DFA](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/DFA.html)).
  - `DFA.evalFrom M s : List α → σ` is defined as `List.foldl M.step s`.
  - Lemmas: `evalFrom_nil`, `evalFrom_cons`, `evalFrom_append_singleton`, and `evalFrom_of_append : M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y` (same page).
- **Mathlib product constructions:** `DFA.inter (M1 : DFA α σ1) (M2 : DFA α σ2) : DFA α (σ1 × σ2)` steps componentwise and accepts only when both components accept, with theorem `accepts_inter` (= `M1.accepts ⊓ M2.accepts`). The page also has `DFA.union`, complement and `comap`. `Language.IsRegular` is closed under `inf` ([Mathlib DFA docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/DFA.html)).
  - The page fetched has no emptiness-decision procedure.
  - Its `accept` is a `Set σ`, which is not computable as-is. That is one reason to roll your own `accept : σ → Bool`.
- **Lean 4 verified regex matchers (derivative-based):**
  - Microsoft Research formalised an extended-regex matcher (intersection, complement, lookarounds) in Lean 4. It is proven correct against standard matching semantics ([MSR](https://www.microsoft.com/en-us/research/?p=1115526)).
  - ITP 2025, "Finiteness of Symbolic Derivatives in Lean" (Zhuchko, Maarand, Veanes, Ebner), proves that the set of derivatives is finite ([LIPIcs ITP 2025](https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/html/LIPIcs.ITP.2025.16/LIPIcs.ITP.2025.16.html)).
  - katydid's `regex-deriv-lean` has correctness and decidability proofs for the derivative algorithm ([GitHub adomani/regex-deriv-lean](https://github.com/adomani/regex-deriv-lean); [Reservoir](https://reservoir.lean-lang.org/@katydid/regexderiv)).
  - These all target matching (membership), not emptiness or search over a bounded length.
- **Isabelle AFP "Functional Automata" (Nipkow):** transition functions and finality predicates are plain functions, so the state space may be infinite. The entry covers regex-to-automaton conversion, a scanner generator, and conversion of finite deterministic automata into regular sets. It builds on AFP "Regular-Sets" ([AFP Functional-Automata](https://devel.isa-afp.org/entries/Functional-Automata.html); [document PDF](https://www.isa-afp.org/browser_info/current/AFP/Functional-Automata/document.pdf)).
  - The "plain function step plus Bool final" representation is exactly the shape recommended below.
- **Coq, Doczkal and Smolka:**
  - CPP 2013 (with Kaiser): a constructive theory of regular languages in about 1400 lines of Coq/Ssreflect, covering regexes, DFAs, NFAs, Myhill-Nerode, and decidability of language equivalence ([paper](https://www.ps.uni-saarland.de/Publications/documents/DoczkalEtAl_2013_A-Constructive.pdf)).
  - JAR 2018, "Regular Language Representations": covers DFAs, NFAs, two-way automata, regexes and WS1S, with about 3000 lines of Coq ([paper](https://www.ps.uni-saarland.de/Publications/documents/DozkalSmolka2018.pdf)).
  - I could not see the text of their emptiness section, so I cannot report which emptiness method they use.
- **Verbatim / Verbatim++ (Egolf, Lasser, Fisher):** a Coq-verified lexer based on Brzozowski derivatives, proven against a maximal-munch specification ([Verbatim paper](https://cflmark.nms.kcl.ac.uk/hg/lexing/raw-file/tip/Literature/Verbatim-2021-paper.pdf)). Verbatim++ (CPP 2022) adds verified DFA compilation and semantic actions ([CPP 2022](https://popl22.sigplan.org/details/CPP-2022-papers/24/Verbatim-Verified-Optimized-and-Semantically-Rich-Lexing-with-Derivatives)).
- **Verified DP (Wimmer, Hu, Nipkow, ITP 2018):** an Isabelle/HOL framework that automatically memoizes recursive functions (functional or imperative) and proves a correspondence theorem with the original function, including bottom-up computation ([Nipkow page](https://www.proof.cit.tum.de/~nipkow/pubs/itp18dp.html); [AFP Monad_Memo_DP](https://isa-afp.org/entries/Monad_Memo_DP.html)).
  - For size calibration, the paper notes that an earlier hand-built CYK formalization needed about 1000 lines of Isabelle ([paper PDF](https://home.cit.tum.de/~wimmers/papers/Memoization_DP.pdf), as summarized by search).
  - Nothing equivalent exists for Lean 4 that I found.

### Inferences
- **Common proof pattern:** every one of these developments reduces "run a product machine" to a componentwise fold. They then prove a correspondence between the computed object and the spec. Emptiness of a finite DFA is classically decided by reachability: the language is non-empty iff some reachable state is accepting. For a fixed length n, the analogue is the layered reachable set `R_k = {eval p | p.length = k}`.
- **Collapse the rules into one DFA:** define `Checker.inter` exactly as Mathlib's `DFA.inter`, and prove the analogue of `accepts_inter` once. Then the whole conjunction of rules is one checker, and the search proof is a proof about a single DFA (see Q3).
- **Imitate, don't import:** the Mathlib DFA file is about the right size to copy-adapt (`evalFrom = foldl`, `evalFrom_of_append`, `inter`) with `accept : σ → Bool`.

### Gaps
- I found no Lean 4 repo that proves bounded-length emptiness or witness search for DFAs. The Lean 4 regex projects verify matching only.
- I did not verify the exact method in Doczkal and Smolka's emptiness section.

## Q2. The certificate route: invariant certificates vs proving the DP, and reusing Lean core's LRAT checker

### Takeaway
The natural certificate for "no answer exists" is a layered inductive invariant: a list `R_0..R_n` of state sets with `init ∈ R_0`, each `R_{k+1}` closed under `step` from `R_k` for every letter, and no accepting state in `R_n`. Checking it takes a very short proof.

However, the completeness proof of a forward DP is essentially the same proof: the DP's layers *are* such an invariant by construction. So a separate certificate pipeline saves little effort. The "validate at the end" trick makes soundness almost free in either design.

Lean core does ship a reusable, verified LRAT checker (`Std.Tactic.BVDecide.LRAT.check` with `check_sound`). Using it would require proving your SAT encoding faithful, which is far more work than the DP.

### Cited Findings
- **Lean core's LRAT checker:**
  - Signature: `def Std.Tactic.BVDecide.LRAT.check (lratProof : Array IntAction) (cnf : Sat.CNF Nat) : Bool`.
  - Soundness theorem: `check_sound … : check lratProof cnf = true → cnf.Unsat` ([Lean API: LRAT.Checker](https://lean-lang.org/doc/api/Std/Tactic/BVDecide/LRAT/Checker.html)).
  - Internal version: `Std.Tactic.BVDecide.LRAT.Internal.check` with `unsat_of_check` ([Internal Checker](https://lean-lang.org/doc/api/Std/Tactic/BVDecide/LRAT/Internal/Checker.html)).
- **Version flag, `Std.Sat.CNF` representation:** in the current API docs, `Std.Sat.CNF α` is a structure `clauses : Array (Clause α)`, and `Clause` stores `atoms : Array α` plus `polarities : ByteArray` with size and boolean-ness invariants ([Std.Sat.CNF.Basic](https://lean-lang.org/doc/api/Std/Sat/CNF/Basic.html)).
  - I believe (unverified) that this is a recent change from an older list-of-literal-lists representation, so tutorials or older code may not match v4.35.
  - `CNF.eval` and `CNF.Unsat` were not on the Basic page, so check the exact file in your toolchain.
- **`bv_decide`:** reduces BitVec/Bool goals to SAT, has an external solver (CaDiCaL, bundled) produce an LRAT proof, and checks that proof in Lean. Because it uses `Lean.ofReduceBool`, the Lean compiler is part of the trusted base ([LRAT checker docs / search summary](https://lean-lang.org/doc/api/Std/Tactic/BVDecide/LRAT/Checker.html); [v4.12.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.12.0/)).
- **LRAT-Catcher:** a third-party tool that runs the same core checker by reflection as compiled native code, to import SAT certificates into Lean 4 ([arXiv 2602.08692](https://arxiv.org/pdf/2602.08692v1)).
- **External precedent for verified certificate checking:** cake_lpr (Tan, Heule, Myreen, TACAS 2021) is a CakeML-verified LPR/LRAT checker with binary-level guarantees. It was used to validate unsatisfiability proofs in SAT Competition 2020 ([PMC](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7984575/); [journal version](https://research.chalmers.se/publication/534843)).

### Inferences
- **Certificate for UNSAT:** `cert : List (List σ)` (layers `R_0..R_n`) plus a Bool checker `checkInv`:
  - `cert.length = n+1`
  - `init ∈ R_0`
  - for every k < n, s ∈ R_k and a ∈ alphabet: `step s a ∈ R_{k+1}`
  - for every s ∈ R_n: `accept s = false`
  - Theorem: `checkInv cert = true → ∀ w, w.length = n → ¬ AllSpecs w`.
  - Proof: induction on w (or on k) that `evalFrom init p ∈ R_{p.length}`, then a contradiction with the acceptance spec.
  - My guess is about 40–80 lines of Lean using only `List.mem`/`List.all` lemmas. With `List.all` and `decide` on membership, `List.all_eq_true` turns the Bool check into a ∀.
- **Certificate for SAT:** the witness itself, re-run through the checkers. "Run the checkers on w and test `accept`" equals the specs via the per-rule lemmas.
- **What certificates do and don't buy:** the certificate approach gives "every answer is correct" but not, by itself, a total procedure with a completeness theorem in the user's form (`(∃ w, …) → (search …).isSome`). An untrusted solver could fail to produce either certificate.
  - To get the completeness theorem you must still prove something about a procedure that produces the certificate. That is exactly the DP whose layers already satisfy `checkInv` by construction.
  - Recommended hybrid if time is short:
    - prove soundness via end-validation (trivial);
    - prove completeness directly via the closure property of DP layers (Q3);
    - optionally expose `checkInv` as a separately checkable artifact (nice for demos, and a fallback if the DP completeness proof stalls).
- **Fallback statement if the completeness proof stalls:** "if search returns none and checkInv(layers) = true then no solution exists", with `checkInv` actually run at runtime. That is a fully proven "sound UNSAT answer" whose completeness is established empirically per run. It is weaker than the requested theorem, so present it honestly as a fallback.
- **LRAT route cost:** you would have to encode 24 slots × ~50 letters (one-hot or log encoding) plus every rule's transition relation into CNF, and prove the encoding correct (`CNF.Unsat ↔ ¬∃ w, AllSpecs w`). That encoding-correctness proof is the expensive part and dwarfs the DP proof.
  - Using `bv_decide` directly would require stating the problem as a fixed-width BitVec formula: unrolled transitions, 24 symbol variables of 6 bits, states as BitVecs, transition tables as nested ifs. That is plausible but brittle.
  - It also only proves universally quantified (UNSAT) goals, gives counterexamples rather than proof-carrying witnesses for SAT, and adds the compiler (`ofReduceBool`) to the trusted base.
  - Verdict: not the cheapest route.

### Gaps
- I did not locate the exact definitions of `Std.Sat.CNF.eval`/`Unsat` for v4.35, or confirm when the Array/ByteArray CNF representation landed.
- I found no precedent for an "inductive invariant certificate for bounded DFA emptiness" in Lean specifically. The idea is standard model-checking practice, but I have no citation for it.

## Q3. Concrete Lean 4 design (definitions, data structures, recursion, decide pitfalls, the DP invariant)

### Takeaway
Use one generic `Checker σ` structure with `[DecidableEq σ]`. Combine the rules with a binary `inter` (product type `σ1 × σ2`, which derives `DecidableEq` automatically). Write the DP by structural recursion on `k : Nat` over `List (σ × List Sym)` with a hand-written "insert if key absent" dedup.

Return a witness only after re-validating it (soundness is then a two-line proof). Prove completeness from one layer invariant. Keep `n` generic and instantiate 24 at the end. Avoid `partial`, avoid HashMap in the proven core unless performance forces it, and never rely on `decide`/`native_decide` for the main theorems.

### Cited Findings
- **Std.HashMap / HashSet lemma libraries:**
  - Core now has substantial lemma libraries for Std.HashMap/HashSet, e.g. `Std.HashMap.Raw.getElem?_insert`, `getElem?_insert_self`, `mem_insert`, `contains_insert_self` ([RawLemmas](https://lean-lang.org/doc/api/Std/Data/HashMap/RawLemmas.html)).
  - HashSet has `mem_insert`, `contains_insert`, `toList_insert_perm`, `fold_eq_foldl_toList`, `mem_ofList`, `mem_insertMany_list` ([HashSet Lemmas](https://lean-lang.org/doc/api/Std/Data/HashSet/Lemmas.html)).
  - Most of these lemmas require `EquivBEq α` and `LawfulHashable α` (same page). The `Raw` variants additionally need a well-formedness proof `m.WF` ([RawLemmas](https://lean-lang.org/doc/api/Std/Data/HashMap/RawLemmas.html)).
  - `Std.ExtHashMap` provides extensional versions of lemmas such as `getElem?_insert` without `WF` side conditions ([ExtHashMap Lemmas](https://lean-lang.org/doc/api/Std/Data/ExtHashMap/Lemmas.html)).
- **Well-founded recursion and `decide`:** since Lean 4.9, functions defined by well-founded recursion are `@[irreducible]` by default, which blocks kernel/defeq unfolding, so `decide` on them stalls. `unseal` can locally override this ([v4.9.0 release notes](https://lean-lang.org/doc/reference/stable/releases/v4.9.0/); [lean4 PR #4674](https://github.com/leanprover/lean4/pull/4674); [issue #3988](https://github.com/leanprover/lean4/issues/3988)).
- **`native_decide`:** trusts the compiler via `Lean.ofReduceBool (a b : Bool) : Lean.reduceBool a = b → a = b` ([Lean reference: Axioms, 4.25](https://lean-lang.org/doc/reference/4.25.0/Axioms/)).
  - In 4.30+ references, `native_decide` creates a bespoke axiom per invocation, auditable with `#print axioms` ([Lean reference: Axioms, 4.30-rc](https://lean-lang.org/doc/reference/4.30.0-rc1/Axioms/)). This is a behaviour change across versions.
- **Model for a no-dependency verified codebase:** `leanprover/human-eval-lean` is a repo of hand-written, formally verified Lean 4 solutions that deliberately takes no Batteries dependency and adds missing lemmas inline ([GitHub](https://github.com/leanprover/human-eval-lean)). It is a good style model for "core only" verified algorithms.

### Inferences (recommended design)

**1. Checker type.** Use a homogeneous structure, not a typeclass and not Sigma lists:
```lean
structure Checker (Sym : Type) (σ : Type) where
  init : σ
  step : σ → Sym → σ
  accept : σ → Bool

def Checker.run (c : Checker Sym σ) (w : List Sym) : σ := w.foldl c.step c.init
def Checker.Accepts (c : Checker Sym σ) (w : List Sym) : Prop := c.accept (c.run w) = true

def Checker.inter (c₁ : Checker Sym σ₁) (c₂ : Checker Sym σ₂) : Checker Sym (σ₁ × σ₂) :=
  ⟨(c₁.init, c₂.init), fun (s₁, s₂) a => (c₁.step s₁ a, c₂.step s₂ a),
   fun (s₁, s₂) => c₁.accept s₁ && c₂.accept s₂⟩
```
- **Key lemma:** `(inter c₁ c₂).run w = (c₁.run w, c₂.run w)`. Prove it by generalising the initial state: first prove `foldl (inter.step) (s₁,s₂) w = (foldl c₁.step s₁ w, foldl c₂.step s₂ w)` by induction on `w` with `generalizing s₁ s₂`. Then `accepts_inter ↔ ∧` follows by `simp [Bool.and_eq_true]`.
- **Build the full product at definition time:** `rule1.inter (rule2.inter (rule3 ...))`. The state type is a nested product, `DecidableEq` (and `Hashable`, if wanted) are inferred, and there are no heterogeneous lists.
- **Pair specs with checkers:** a `structure Rule` with `σ`, `checker`, `spec : List Sym → Prop`, and `correct : ∀ w, checker.Accepts w ↔ spec w`. Its conjunction lemma is `Rule.inter` with spec `fun w => r₁.spec w ∧ r₂.spec w`. Because the type `σ` is a field, `Rule` lives in `Type 1`. That is fine as long as you never put Rules of different σ in a `List`; nest `inter` instead.
- **Alternative if dependent types bite:** encode every rule's state as `Nat` (or a small fixed structure) so the product state is `List Nat`. This is simpler for hashing but loses type-level documentation, and per-rule proofs become slightly messier (states outside the intended range).

**2. Alphabet.** Use `Sym := Fin 50` (or a custom inductive) plus an explicit `alphabet : List Sym` with a completeness lemma `∀ a, a ∈ alphabet`. Completeness of search depends on this lemma.
- For `Fin n`, `List.finRange n` with `List.mem_finRange` should be in core in recent versions. That is version-sensitive, so verify it in v4.35. Otherwise define `alphabet` by hand and prove membership with `decide` (50 cases are fine for `decide` because there is no well-founded recursion).

**3. The DP.** Use structural recursion on `k : Nat`. No `partial`, no `termination_by`, no `Fin 24` indices:
```lean
def insertNew [DecidableEq σ] (acc : List (σ × List Sym)) (x : σ × List Sym) :=
  if acc.any (·.1 == x.1) then acc else x :: acc   -- or: if ∃ check via find?

def layer (c : Checker Sym σ) (alphabet : List Sym) : Nat → List (σ × List Sym)
  | 0     => [(c.init, [])]
  | k + 1 => ((layer c alphabet k).flatMap fun (s, p) =>
               alphabet.map fun a => (c.step s a, p ++ [a])).foldl insertNew []
```
- For speed you can store prefixes reversed (`a :: p`) and reverse at the end. The proofs barely change if the invariant uses `p.reverse`.
- With 24 layers × |states| × 50, the List-based `insertNew` is O(m²) per layer. That is fine up to a few thousand product states per layer, and too slow for ~10^5.

**4. Search with end-validation.** Soundness costs about 5 lines and does not depend on the DP being right:
```lean
def search c alphabet n : Option (List Sym) :=
  (layer c alphabet n).find? (fun (s, _) => c.accept s) |>.bind fun (_, p) =>
    if p.length = n ∧ c.accept (c.run p) then some p else none
```
- **Soundness:** `search … = some w → w.length = n ∧ spec w`. Unfold, use `Option.bind_eq_some`/`if` splits, then apply the per-rule `correct`.

**5. The one invariant to prove**, by induction on `k`:
- (a) Genuineness: `∀ s p, (s, p) ∈ layer k → p.length = k ∧ c.run p = s`.
- (b) Coverage: `∀ p, p.length = k → ∃ q, (c.run p, q) ∈ layer k`.
- Facts you need about `foldl insertNew`, each by induction on the input list with the accumulator generalised:
  - (i) every output element is an input element, which preserves (a);
  - (ii) every input key appears as some output key, which gives (b).
- The step for (b): write `p = p' ++ [a]` (`List.eq_nil_or_concat` or induction on the length), use `foldl_append`/`run_append` (`c.run (p' ++ [a]) = c.step (c.run p') a`), take q' from the IH, and note that `(c.step (c.run p') a, q' ++ [a])` is in the flatMap (`a ∈ alphabet`). Then (ii) applies.
- **Completeness:** given `w` with `w.length = n ∧ spec w`, (b) gives `(c.run w, q) ∈ layer n`. `c.accept (c.run w) = true` makes `find?` succeed on *some* element `(s', p')` (`List.find?_isSome` / `List.find?_eq_none`, by contradiction). By (a), `p'.length = n` and `c.run p' = s'`, so the validation `if` passes and `isSome` holds.
- **Phrasing tip:** state completeness as `(∃ w, w.length = n ∧ spec w) → (search c alphabet n).isSome = true`, and add the corollary `search … = none ↔ ¬∃ w, …`. Prove everything for generic `n`, then specialise to 24. Avoid `Fin 24` in statements; `w.length = 24` is easier for simp.

**6. foldl lemmas.**
- Always generalise the accumulator: `induction l generalizing acc`. This is the single most common stumbling block, also noted in an LLM-proof planning paper's Lean `listMax` example ([arXiv 2608.09277](https://arxiv.org/pdf/2608.09277)).
- Core has `List.foldl_cons`, `List.foldl_nil`, and `List.foldl_append` (names believed stable; verify in v4.35).
- Alternatively, define `run` by explicit structural recursion instead of `foldl` to get simpler equation lemmas. Then prove `run (p ++ [a]) = step (run p) a` once.

**7. HashMap / HashSet if performance needs it.**
- Options:
  - Keep the List-based proven DP but deduplicate by key with `Std.HashMap σ (List Sym)` via `insertIfNew`, and prove (i) and (ii) with `Std.HashMap` lemmas (`mem_insertIfNew`, `getElem?_insertIfNew`, `toList` membership lemmas). These need `EquivBEq` and `LawfulHashable`.
  - With `BEq` derived from `DecidableEq` (`instBEqOfDecidableEq`), `LawfulBEq` holds. I believe (unverified) that core provides the instances giving `EquivBEq` and `LawfulHashable` from `LawfulBEq`, but check that for your derived `Hashable` instances.
- Expect proof friction around `toList` (permutations, membership) rather than around insert itself.
- A pragmatic split: prove the List version, keep the HashMap version as an unproven fast path, and at runtime cross-check it or fall back to the List version. Don't claim the HashMap version is verified.

**8. `decide` / `native_decide`.**
- The main theorems are universally quantified over checkers and n, so they need neither tactic. Running the solver is `#eval search …`.
- If you want a *theorem* that a specific instance is UNSAT:
  - kernel `decide` over 24 layers × states × 50 will almost certainly time out;
  - `native_decide` works but adds a compiler-trust axiom (visible in `#print axioms`; per-invocation axiom in recent versions).
  - Presenting `#eval` output backed by the general theorem is the honest and cheap approach.
- Keep all DP functions structurally recursive. Well-founded definitions are irreducible by default and break `decide`/`rfl` on small test cases.

**9. Batteries.**
- Not needed. Core `List` lemmas (`List.mem_flatMap`, `List.mem_map`, `List.find?_some`, `List.any_eq_true`, `List.all_eq_true`) cover the proofs. Names have shifted across 2024–2025 (e.g. `bind` → `flatMap`, `List.join` → `flatten`), so let `exact?`/`simp?` find the current names.

### Gaps
- I did not confirm v4.35-specific names (`List.finRange` and `mem_finRange` in core, `insertIfNew` lemma names on non-Raw `Std.HashMap`, or which instances provide `LawfulHashable` for derived `Hashable`).
- I did not find any Zulip thread specifically about verified DFA emptiness or a DP in Lean 4.

## Q4. Effort estimates and examples to imitate

### Takeaway
There are no published effort numbers for this exact task in Lean 4. The closest calibration points are:
- an Isabelle hand-built CYK verification: about 1000 lines;
- a whole constructive theory of regular languages in Coq: about 1400 lines.

Our problem is a much narrower slice (a single DFA, bounded-length reachability). My estimate is roughly 200–450 lines of Lean for the checker framework plus the DP soundness and completeness proofs, excluding the per-rule spec proofs. That is about 0.5–1.5 working days for a competent Lean user with AI assistance. The per-rule "checker ↔ spec" proofs are likely to be the real time sink and should be budgeted separately.

### Cited Findings
- A hand-built CYK formalization took about 1000 lines of Isabelle, per Wimmer, Hu and Nipkow ([Memoization DP paper](https://home.cit.tum.de/~wimmers/papers/Memoization_DP.pdf)).
- Doczkal, Kaiser and Smolka's constructive regular-language theory is about 1400 lines of Coq/Ssreflect. The 2018 extension with two-way automata and WS1S is about 3000 lines ([CPP 2013](https://www.ps.uni-saarland.de/Publications/documents/DoczkalEtAl_2013_A-Constructive.pdf); [JAR 2018](https://www.ps.uni-saarland.de/Publications/documents/DozkalSmolka2018.pdf)).
- Examples to imitate:
  - Mathlib `DFA.lean`: the inter, evalFrom and foldl lemmas ([docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/DFA.html)).
  - `leanprover/human-eval-lean`: core-only verified algorithms ([GitHub](https://github.com/leanprover/human-eval-lean)).
  - katydid `regex-deriv-lean`: correctness and decidability proofs for a derivative matcher ([GitHub](https://github.com/adomani/regex-deriv-lean)).
  - `cslib-community/fad`: algorithm-design examples including DP in Lean 4 ([Reservoir](https://reservoir.lean-lang.org/@cslib-community/fad/_payload.json)). I have not verified that its DP proofs use fold invariants.
  - AlgoVeri, a benchmark of verified classical algorithms in Lean 4 ([arXiv 2602.09464](https://arxiv.org/pdf/2602.09464)).

### Inferences
- **Suggested hackathon order:**
  1. `Checker`, `run`, `inter` plus the `inter` lemma (about 1–2 hours).
  2. Per-rule checkers and specs, starting with the simplest rule to shake out spec style. Specs phrased over `List` indices (`∀ i, i+1 < w.length → …w[i]…w[i+1]`) are much harder to connect to a fold than specs phrased recursively (`inductive`, or a `def` by pattern matching on `a :: b :: rest`). Where possible, write the readable spec recursively and prove it equivalent to the index form if you want that form for the audience.
  3. DP plus end-validation soundness (about 1 hour).
  4. Completeness invariant (a half to a full day).
  5. Optional `checkInv` certificate checker as a demo and fallback (about 2 hours).
- **Rules whose checker needs "lookback" state:** for example "no repeated note within the last k positions", or counts. Prove each with a generalised invariant: "after processing prefix p, the state equals f(p)", where f is an abstraction such as the last k symbols or a count. Then conclude `accept (f w) ↔ spec w`. This "state = abstraction of prefix" lemma is the reusable pattern for every rule.
- **Risks:**
  - the product state count blowing up and the List DP getting slow (mitigate by keeping rule state spaces small, or with an unverified HashMap fast path);
  - fighting simp-normal forms of `List.find?`/`flatMap` lemmas that have been renamed across versions;
  - specs over `Fin`-indexed accesses.

### Gaps
- I found no first-hand effort reports (blogs or Zulip) for verified DFA emptiness or a DP in Lean 4 with AI assistance. The time estimates above are my own judgement.
