# Automata / REGULAR-constraint framing for "does any answer satisfy all chosen rules?" — theory and per-rule classification

Problem shape being analysed throughout: an answer is a word of length n = 24 (2 bars x 12 triplet slots) over the alphabet
Sigma = {rest} ∪ {onset(p) | p ∈ 40..88}, so |Sigma| = 50. The call (same shape) is fixed before search. We want a sound and complete
decision procedure that also returns a witness.

Note on sourcing: I could not fetch Pesant's CP 2004 paper itself (no open copy reachable), nor Beldiceanu–Carlsson–Petit's CP 2004 full text, nor
the Global Constraint Catalog pages (the guessed `sofdem.github.io/gccat/gccat/C*.html` URLs returned 404). Their content below is taken from
secondary papers by the same authors (Pesant–Quimper–Zanarini JAIR 2012; van Hoeve–Pesant–Rousseau 2004) that restate it, and is flagged where so.
Per-rule state counts are my own derivations (marked as Inferences) — they are elementary counting arguments, not literature claims.

## Q1. Pesant's REGULAR constraint, layered graph, complexity, domain consistency; automata with counters (Beldiceanu et al.)

### Takeaway
REGULAR(x, M) unrolls a DFA M over the n positions into a layered DAG (layer i = copy of the state set Q; arc q→δ(q,v) for each v in D_i). Paths from (layer 1, q0) to (layer n+1, F) are in one-to-one correspondence with solutions, so "is there a solution?" = reachability, a witness = any such path, domain consistency = keep only arcs on some source→sink path (one forward + one backward pass), all in time linear in the graph size, O(n·|δ|) ⊆ O(n·|Q|·|Sigma|). Counters (Beldiceanu et al.) lose the arc-consistency guarantee unless you fold the counter values into the state, which for our bounded, small counters is exactly what we should do.

### Cited Findings
- Definition (as restated by Pesant et al.): "The regular(X, Π) constraint holds if the values taken by the sequence of finite domain variables X = ⟨x1,...,xk⟩ spell out a word belonging to the regular language defined by the deterministic finite automaton Π = (Q, Σ, δ, q0, F) ... δ : Q × Σ → Q is a partial transition function." Original: G. Pesant, "A Regular Language Membership Constraint for Finite Sequences of Variables", CP 2004, LNCS 3258, pp. 482–495. — [Pesant, Quimper, Zanarini, JAIR 43 (2012)](https://arxiv.org/pdf/1401.4601)
- Layered-graph construction (restated by Pesant's co-authored paper): "a domain consistency algorithm for the regular constraint processed the sequence x with the automaton M, building a layered directed multi-graph G = (N1, N2, ..., Nn+1, A) where each layer Ni = {q^i_0, ..., q^i_{|Q|-1}} contains a different node for each state of M and arcs only appear between consecutive layers. ... there is an arc from q^i_k to q^{i+1}_ℓ if and only if there exists some vj ∈ Di such that δ(qk, vj) = qℓ and the arc belongs to a path from q0 in the first layer to a member of F in the last layer. The existence of such an arc, labeled vj, constitutes a support for variable xi taking value vj." — [van Hoeve, Pesant, Rousseau, "On Global Warming (Softening Global Constraints)", 2004](https://arxiv.org/pdf/cs/0408023)
- Worked example in the same paper: 5 variables, the pruning removes value b from D2 and D4 because no accepting path uses those arcs. — [van Hoeve, Pesant, Rousseau](https://arxiv.org/pdf/cs/0408023)
- Complexity: shortest paths from the initial node and to final nodes in this layered graph "can be done in O(n|δ|) time through topological sorts because of the special structure of the graph", and the computation "can also be made incremental in the same way as in [Pesant 2004]". Since |δ| ≤ |Q|·|Σ|, this gives the familiar O(n·|Q|·|Σ|). — [van Hoeve, Pesant, Rousseau](https://arxiv.org/pdf/cs/0408023)
- The regular and (domain-consistent) knapsack filtering algorithms "are both based on the computation of paths in a layered acyclic directed graph (Pesant, 2004; Trick, 2003). This graph has the property that paths from the first layer to the last are in one-to-one correspondence with solutions of the constraint." — [Pesant, Quimper, Zanarini JAIR 2012](https://arxiv.org/pdf/1401.4601)
- Domain consistency definition used: a constraint is domain consistent if every value d in every domain Di belongs to some solution (= generalized/hyper-arc consistency). — [van Hoeve, Pesant, Rousseau](https://arxiv.org/pdf/cs/0408023)
- Counting: in-path / out-path recursions #ip(i+1,b') = Σ #ip(i,b), #op(i,b) = Σ #op(i+1,b'); total solutions = #op(0,0) "in time linear in the size of the graph even though there may be exponentially many of them"; solution density of (xi,d) = Σ over arcs labelled d of #ip·#op / total. Exact counting for regular is attributed to Zanarini & Pesant (2009). — [Pesant, Quimper, Zanarini JAIR 2012](https://arxiv.org/pdf/1401.4601)
- Regular generalises Pesant's earlier stretch constraint; regular was announced/implemented in Gecode in Nov 2004, with the Gecode author noting a simpler propagator than Pesant's. — [Gecode users archive, Nov 2004](https://www.gecode.org/users-archive/2004-November/000200.html)
- Beldiceanu, Carlsson, Petit, "Deriving Filtering Algorithms from Constraint Checkers", CP 2004, LNCS 3258, pp. 107–122 (SICS TR T2004-08): checker automata may carry counters "initialized to a value in the start state and can be modified at each transition"; a final state can require a condition on counter values; the arc-consistency result "only holds for automata which do not involve counters". — [Raiser 2008, summarising BCP04](https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.170/home/raiser/publications/Raiser2008a.pdf)
- SICStus Prolog's `automaton/3,8` constraint is credited to the techniques of [Beldiceanu, Carlsson & Petit 04]. — [SICStus manual, Automata Constraints](https://sicstus.sics.se/sicstus/docs/4.3.0/html/sicstus/Automata-Constraints.html)
- Combining weighted automata: the product of two weighted automata is the cross product of the underlying automata with cost matrices added (stated in the context of MULTICOSTREGULAR). — [RegularGcc matrix constraint paper](https://arxiv.org/pdf/1201.0564)

### Inferences
- For our purposes the CP "propagation" machinery is overkill: the decision procedure is just a forward reachability DP over the layered graph (R_0 = {q0}; R_{i+1} = {δ_i(q,a) | q ∈ R_i, a ∈ D_i}); answer exists iff R_24 ∩ F ≠ ∅; witness by back-pointers. Soundness + completeness reduce to one lemma: q ∈ R_i ⇔ ∃ prefix w of length i with δ*(q0,w) = q. That lemma is proved once for a generic checker, independent of the rule set — attractive for Lean.
- The layered graph is position-indexed, so the transition function can depend on the layer i (time-varying δ_i). Rules that mention specific slots (beats, bars, off-beats, chord per bar) therefore cost no extra states — the slot index is "free memory". (Pesant states δ as stationary with per-position domains Di; per-layer δ_i is a trivial generalisation since the graph is unrolled anyway.)
- Backward pass (co-reachability to F) gives Pesant-style domain consistency = "which (slot, pitch/rest) choices still extend to a valid answer", useful for UI hints (grey out impossible notes), at the same O(n·|δ|) cost.
- BCP04's loss of arc consistency with counters only matters when counters are left symbolic. With n = 24 every counter is bounded by 24, so unrolling counter values into the state restores exactness (and Pesant's guarantee) at a multiplicative state cost = counter range.

### Gaps
- Could not read Pesant CP 2004 directly; the exact wording of its complexity theorem (often quoted as O(n·|Q|·|Σ|) time and space) is reconstructed from the O(n|δ|) statement in van Hoeve–Pesant–Rousseau plus |δ| ≤ |Q||Σ|.
- Global Constraint Catalog automaton descriptions (and the `automaton_with_counters` entry) not retrieved: URLs guessed from the catalog's naming convention 404'd.
- Quimper & Walsh "Global Grammar Constraints" (CP 2006) not retrieved; only the follow-up [Katsirelos, Maneth, Narodytska, Walsh, "Restricted Global Grammar Constraints"](https://arxiv.org/abs/0906.5233) was found (shows weighted linear GRAMMAR encodes EDITDISTANCE and its conjunction with REGULAR).

## Q2. Per-rule minimal checker memory (rules a–l)

### Takeaway
Every rule here is a left-to-right checker with tiny memory. Unary/positional rules (a-exact, g, h, i, l) need 0 extra states (pure per-slot domain restriction). Rules about consecutive notes need "last pitch" (≤ 50 values: 49 pitches + "no note yet"), which can be shared. Counting rules need a saturating counter (d: ≤ c_call values, j: N+1 per bar, a-shared-K: K+1, k: 2). Only (b) needs a remembered value pair (note index × offset ≈ N·49). The rule set is cheap; the product is the only thing to watch.

### Cited Findings
- Automaton states can be augmented with counters that are initialised in the start state, updated on transitions and tested at the end — the standard way to express counting rules in automaton-based global constraints. — [Raiser 2008, summarising Beldiceanu–Carlsson–Petit CP 2004](https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.170/home/raiser/publications/Raiser2008a.pdf)
- Per-position domain restrictions (Di ⊆ Σ) are part of the REGULAR setup itself, so unary per-slot rules are handled by shrinking domains rather than adding states. — [van Hoeve, Pesant, Rousseau](https://arxiv.org/pdf/cs/0408023)

### Inferences (my derivations; n = 24, 49 pitches, alphabet 50)
Notation: "LP" = last sounded pitch ∈ {none} ∪ 40..88 (50 values). "Local" = decided by the current symbol and slot index alone.

| Rule | Kind | Minimal memory | States | Notes |
|---|---|---|---|---|
| (a) echo rhythm, exact | unary per slot (call onset set is fixed) | none | 1 | slot i allowed ∈ onsets iff call has onset at i |
| (a') share ≥ K onset slots | counter | #shared so far, saturating at K | K+1 (≤ 25) | can prune: fail early if shared + remaining call onsets < K |
| (b) first N notes = call's first N transposed by one offset | remembered value + index | (j = notes placed, 0..N) × offset d (fixed by 1st note: d = p1 − c1, ≤ 49 values) | 1 + 49·N + 1 ("done") → e.g. N=4: 198 | while j<N, next note forced to c_{j+1}+d, so LP is determined by (j,d) and need not be stored separately |
| (c) contrary motion | binary on first two notes | phase {no note, 1 note with pitch p, done} | 1 + 49 + 1 = 51, and the "pitch p" part is just LP (shareable) | vacuous if call's last interval is not "up" (decide at build time, call is known) |
| (d) say less | counter | #onsets, must stay ≤ c_call − 1 | c_call (≤ 24; e.g. 8 for an 8-note call) | |
| (e) first note within K semitones of call's last note | unary on first note | flag "any note yet?" | 2 | shares with any "note count ≥1" info |
| (f) max leap L | binary on consecutive notes (not slots: rests intervene) | LP | 50 | |
| (g) chord tone on slot s | unary at slot s (onset version) | none | 1 | chord per bar known from 12-bar form → time-varying δ. If "sounding at s" (sustain), needs LP (shared with f) |
| (h) avoid pitch class | unary | none | 1 | |
| (i) pitch range | unary | none | 1 | |
| (j) ≤ N notes per bar | per-bar counter, reset at slot 12 | 0..N | N+1 (e.g. 5) | reset is free because slot index = layer |
| (k) ≥ 1 off-beat onset | flag | seen-offbeat? | 2 | |
| (l) no onsets in first K slots | unary | none | 1 | |

## Q3. Product automata: blow-up, keeping it small, and a concrete estimate (f + b + d + j + g)

### Takeaway
The conjunction of rules = intersection of languages = product automaton, whose state set is (a subset of) the Cartesian product, so the naive size is the product of the per-rule sizes. But with on-the-fly reachability plus sharing "last pitch", the realistic worst case for f+b+d+j+g is ~3×10^3 states per layer, ~7×10^4 layered nodes and ~3.5×10^6 transitions for the whole 24-slot search — milliseconds in compiled code, and comfortably runnable in compiled Lean.

### Cited Findings
- The product of two DFAs recognises the intersection of their languages (closure of regular languages under intersection); DFAs have canonical minimal forms. — [Wikipedia: Deterministic finite automaton](https://en.wikipedia.org/wiki/Deterministic_finite_automaton)
- Weighted automata compose by cross product with cost matrices summed. — [RegularGcc paper](https://arxiv.org/pdf/1201.0564)
- Total DP cost is linear in graph size: O(n·|δ|). — [van Hoeve, Pesant, Rousseau](https://arxiv.org/pdf/cs/0408023)

### Inferences
Techniques to keep the product small (in order of payoff for this app):
1. Don't build the product; explore it. Forward BFS layer by layer storing only reachable product states in a hash set (dedupe is what turns 50^24 ≈ 6×10^40 words into a polynomial search). Only rules the user enabled contribute components.
2. Factor shared memory: one LP field serves (c), (f), (g-sustain), and is implied by (b) while (b) is active.
3. Drop dead components: (b)'s offset is irrelevant after note N; (c) collapses to "done" after 2 notes; (e) after 1 note; saturate counters at their threshold.
4. Use positional knowledge: slot index is free; counters bounded by min(slot index, cap) — reachability prunes automatically.
5. Unary rules as domain filters (h, i, l, g, a-exact) shrink |Sigma_i| per slot, cutting arcs, not states.
6. Backward (co-reachability) pass: prune states that cannot reach acceptance (e.g. count rules that can no longer be met); gives domain consistency.
7. Minimisation (Hopcroft-style) of each component or of the reachable layered graph is possible but unnecessary at this size; symbolic BDD/MDD representations likewise unnecessary (they help only at ~10^7+ states).
8. Independent rules (no shared memory and no shared variables) cannot be decomposed here — all rules talk about the same 24 slots — so decomposition doesn't apply; but rules with 0 memory are effectively decomposed into domain filters.

Concrete estimate, f + b(N=4) + d(c_call = 8) + j(≤4/bar) + g:
- Naive product: LP 50 × b 198 × d 8 × j 5 = 396,000 states per layer; × 24 layers ≈ 9.5 M nodes; × 50 symbols ≈ 475 M arc evaluations (upper bound, before any pruning). Still finite and feasible in compiled code, but wasteful.
- With sharing: phase "inside b" (j = 1..3 notes placed): LP determined by (j,d), total note count = j (determined), bar count ≤ 5 → ≤ 3 × 49 × 5 ≈ 735; phase "after b" (≥ 4 notes): LP 49 × total count {4..7} (4 values) × bar count 5 ≈ 980; plus start state. ≈ 1.7k states per layer (using count ∈ 0..7 without the j-determination gives ≈ 2.9k; I'll quote ≤ 3k as a safe bound). Over 24 layers ≤ ~7×10^4 nodes; × 50 symbols ≤ ~3.5×10^6 transitions. (g) adds 0 states (restricts the alphabet at one slot). With (f) of max leap L, after b each state reaches ≤ 2L+1 pitches, cutting arcs further.
- Rule interactions are discovered for free: e.g. (a-exact) + (d) is always unsatisfiable (same onset count vs strictly fewer); (b, N≥2) fixes the first interval to the call's first interval, which may contradict (c); (e) + (b) restricts the offset d to ≤ 2K+1 values.

### Gaps
- No literature benchmark found for product-DFA sizes in melody generation specifically; the estimates above are my arithmetic.

## Q4. Rules that are not naturally small-memory finite-state, and how to restrict them

### Takeaway
"Hard" rules are those whose checker must remember an unbounded or large set of past values (all seen motifs, all used pitches, the whole first half). Over n = 24 they are still technically regular but the state count is 49^k or 2^49. The fix is always: bound the lookback, bound the counter, compare against the fixed call (unary per slot) instead of against the answer itself, or fix positions. Several rules that sound global are actually tiny.

### Cited Findings
- Non-regular structure (e.g. nested/mirrored patterns) is the domain of the GRAMMAR (context-free) constraint; Katsirelos et al. study GRAMMAR over restricted CFG classes and show a weighted linear GRAMMAR encodes EDITDISTANCE and EDITDISTANCE ∧ REGULAR. — [Katsirelos, Maneth, Narodytska, Walsh](https://arxiv.org/abs/0906.5233)
- General CFG membership via CYK is cubic in the input length (O(n^3)) and requires CNF conversion, which can blow up the grammar. — [Isabelle AFP CYK entry](https://isa-afp.org/entries/CYK.html) / [HMC CS81 notes](https://cs.hmc.edu/courses/2023/fall/cs81/cyk)
- Arithmetic (sum) constraints have a pseudo-polynomial layered graph with a node per (position, partial sum) (Trick 2003), cost O(k·u·max|Di|). — [Pesant, Quimper, Zanarini JAIR 2012](https://arxiv.org/pdf/1401.4601)

### Inferences
- "Answer is not a copy of the call" — actually tiny: aligned slot-by-slot it's a 2-state flag "differs so far"; "not a transposed copy" = offset (49) × flag; "call does not occur as a contiguous note-substring" = KMP/Aho–Corasick automaton with |call notes|+1 states.
- "No repeated motif anywhere" (no length-m note n-gram occurs twice): must remember the set of seen m-grams → exponential. Restrict to "no immediate repetition" (lookback m notes → 49^m states; m=2 ≈ 2.4k, m=3 ≈ 118k) or to intervals instead of pitches (≈ 25^m), or to fixed positions ("bar 2 doesn't repeat bar 1" = remember bar 1, still large unless restricted to rhythm: 2^12 = 4096).
- Global contour rules: "arch/unimodal" = {rising, falling} × LP ≈ 100 states; "ends on the phrase's lowest note" = running min × LP ≈ 49²; "peak ≥ X above first note" = first pitch × running max ≈ 49². Each remembered value multiplies by ≈ 49; keep k ≤ 2.
- Arbitrary non-adjacent comparisons: "note 5 = note 2" = remember one pitch (49). "Retrograde/palindrome of itself" = remember first half → 49^12 (ww^R is context-free, not regular for unbounded n → GRAMMAR/CYK). But "retrograde of the call" is unary per slot because the call is fixed — the fixed-reference trick turns most call-relative rules into domain filters.
- "All pitches distinct" = set of used pitches (2^49) — blow-up; restricting to pitch classes gives 2^12 = 4096 (acceptable); otherwise use alldifferent/SAT.
- Sum/average rules (mean pitch, total duration) = counter up to ~24·88 ≈ 2,100 values — pseudo-polynomial, acceptable alone but multiplies everything else.
- Rule of thumb: state count ≈ Π (range of each remembered value) over rules active at the same time; keep it ≲ 10^6 per layer.

### Gaps
- Quimper & Walsh CP 2006 GRAMMAR paper and its exact complexity not retrieved (only general CYK O(n^3) sources).

## Q5. Alternative exact approaches; weighted variants

### Takeaway
DP over the (implicitly built) product automaton is the simplest exact method here: one generic algorithm, one soundness/completeness proof, witnesses for free, and it extends to counting, best-answer optimisation and per-slot "what is still possible" hints at the same linear cost. SAT/SMT/ILP are viable but bring encoding work and (for UNSAT ⇒ "no answer") trust in an external solver unless certificates are checked.

### Cited Findings
- Counting all solutions and per-value solution densities via in/out path counts in linear time in the graph size. — [Pesant, Quimper, Zanarini JAIR 2012](https://arxiv.org/pdf/1401.4601)
- Weighted/soft REGULAR: add costs to arcs and compute shortest paths from the source and to the sink layer in O(n|δ|); a value is consistent iff the best path through its arc is within the cost bound. — [van Hoeve, Pesant, Rousseau](https://arxiv.org/pdf/cs/0408023)
- COST-REGULAR (Demassey, Pesant, Rousseau, Constraints 11(4):315–333, 2006) and MULTICOSTREGULAR extend REGULAR with assignment costs / resource vectors; weighted automata combine by product with summed costs. — [RegularGcc paper](https://arxiv.org/pdf/1201.0564); [Polytechnique Montréal publications listing](https://publications.polymtl.ca/view/year/2006/Rousseau,_Louis-Martin.divisions.html)
- ILP: Côté, Gendron, Rousseau, "Grammar-Based Integer Programming Models for Multiactivity Shift Scheduling", Management Science 57(1):151–163 (2011): derive an IP from a context-free grammar whose LP relaxation equals that of the classical set-covering model; automaton/grammar → network-flow-style IP. — [CIRRELT-2010-01](https://www.cirrelt.ca/DocumentsTravail/CIRRELT-2010-01.pdf); [Dagstuhl seminar abstract](https://drops.dagstuhl.de/entities/document/10.4230/DagSemProc.09261.9)

### Inferences
- Weighted variants are near-free on the same layered graph: replace "∃" by "Σ" (count answers, e.g. "there are 1.2 M valid answers"), by "min/max" (Viterbi: best answer under an additive score such as closeness to the call's rhythm, stepwise motion preference, chord-tone bonus), or by sampling (uniform random valid answer by walking forward weighted by #op counts — great for "give me a different answer").
- SAT encoding: 24 × 50 one-hot vars (1,200) + cardinality constraints for (d),(j),(a') + clauses; offset in (b) as 49 auxiliary vars. Solvers return SAT witnesses quickly, but proving "no answer" soundly in Lean requires checking an UNSAT certificate (e.g. LRAT/DRAT) — more infrastructure than verifying a DP. SMT (linear integer arithmetic) is natural for offsets/leaps but has the same trust issue. ILP: the layered graph is literally a network-flow model (one unit of flow, arcs = transitions), so it is totally unimodular for a single automaton; side constraints break that.
- Recommended Lean architecture: a `Checker` structure (State type with DecidableEq/Hashable, init, step : slot → State → Symbol → Option State, accept) with a proof `accepts w ↔ Rule w`; a generic product combinator with proof `accepts(prod) ↔ both`; a generic layered reachability DP with proof `dp returns some w → accepts w` (sound) and `dp returns none → ∀ w, ¬ accepts w` (complete). Per-rule work is then only the small "checker ↔ rule" lemma.

### Gaps
- No source retrieved comparing DP vs SAT/ILP on problems of exactly this size; the "DP is simplest" verdict is reasoning, not a cited benchmark.
- Lean-specific tooling (e.g. certified SAT via LRAT checking in Lean 4's `bv_decide`) not researched here — outside this scope; verify separately if SAT is considered.
- Decision-diagram (MDD) optimisation literature (the layered graph is an exact MDD) not retrieved.
