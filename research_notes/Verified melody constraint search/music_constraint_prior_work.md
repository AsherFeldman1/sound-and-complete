# Prior Work: Constraint-Based Melody Generation and Exact Existence Checks

Scope: which problem representations in the music-constraint literature make "does any valid melody exist?" decidable exactly (sound + complete) and efficiently, and how directly they map to a 2-bar blues call-and-response answer on a 24-slot grid with MIDI pitches about 40-88.

Note on sourcing: full texts were read for Pachet/Roy/Barbieri IJCAI 2011 (PDF text extracted), Anders & Miranda ACM CSUR 2011 (PDF text extracted), and Fremont/Donzé/Seshia arXiv 1704.06319 (ar5iv HTML). Other items come from abstracts, publisher pages or secondary summaries, as marked.

---

## Q1. Pachet/Roy Markov constraints line: what was proved about arc consistency, backtrack-free generation, and the role of REGULAR/automata?

### Takeaway
For constraints that stay within the Markov scope (unary constraints on any position plus binary constraints between adjacent positions, for order 1), arc consistency alone is enough for backtrack-free generation. The argument is Freuder's 1982 theorem for tree-structured, width-1 networks: after AC, a domain is non-empty exactly when a solution exists, and every consistent prefix extends to a full sequence. Later work packages richer constraints (no-plagiarism, meter) as automata or the REGULAR constraint. Pesant's REGULAR gets generalized arc consistency in O(n·|transitions|), so existence is again exact and polynomial in automaton size. Constraints that tie non-adjacent positions (binary equalities) or grammar membership make sampling and counting #P-complete in general.

### Cited Findings
- **Pachet & Roy, "Markov constraints: steerable generation of Markov sequences," *Constraints* 16(2):148-172, 2011.** Recasts Markov generation as a branch-and-bound CSP built from "Elementary Markov Constraints". It gives domain-consistent propagators, and "arbitrary additional constraints" can express control. The cost is that it is more expensive than greedy generation. It finds optimal or singular solutions through complete search-optimization, not polynomial-time existence. — [Springer](https://link.springer.com/article/10.1007/s10601-010-9101-4); [Goldsmiths repository](https://research.gold.ac.uk/id/eprint/9519); characterization of it as "a complete search-optimization algorithm, which limits real-time use" is in [Pachet, Roy, Barbieri IJCAI 2011](https://www.ijcai.org/Proceedings/11/Papers/113.pdf)
- **Pachet, Roy, Barbieri, "Finite-Length Markov Processes with Constraints," IJCAI 2011.** Defines *Binary-Sequential CSPs (BSC)*, which contain "only constraints whose scope remains within the scope of the Markov order". For order 1, these are "1) unary constraints and 2) binary constraints among adjacent variables". — [IJCAI PDF](https://www.ijcai.org/Proceedings/11/Papers/113.pdf)
- Key proposition (IJCAI 2011): if the BSC P is arc-consistent, then every consistent partial sequence s1..si (P1) has an extension s_{i+1}, and (P2) s1..si s_{i+1} is consistent iff s_i s_{i+1} is consistent. Proof: "P is of width 2 as its constraint network is a tree; [Freuder, 1982] proved that arc-consistency enables a backtrack-free resolution of a CSP of width 2". (Note: the paper says "width 2", but standard terminology calls a chain or tree a width-1 network. See Gaps.) — [IJCAI PDF](https://www.ijcai.org/Proceedings/11/Papers/113.pdf)
- Consequence: after AC, the constrained process can be compiled into a non-homogeneous Markov model that generates exactly the satisfying sequences, with probabilities proportional to the originals. Renormalization costs O(L·n²) and each sample costs O(L·n) (n = alphabet size, L = length). — [IJCAI PDF](https://www.ijcai.org/Proceedings/11/Papers/113.pdf)
- On constraints beyond the Markov scope, the same paper says a "necessary and sufficient condition is that the induced CSP should be made backtrack-free" and that "propagation is needed after each instantiation". Its example is AllDiff on consecutive triples, handled by path consistency (strong 3-consistency) in O(n³). It concludes: "More complex constraints can be handled provided they can be filtered to obtain backtrack-free CSPs, at the cost of inaccurate probabilities." — [IJCAI PDF](https://www.ijcai.org/Proceedings/11/Papers/113.pdf)
- Musical uses in that paper are all unary: "Continuation" (last note must be terminal), "Variation" (first and last notes equal those of the input), "Answer" (last note equals the first input note, "producing a sense of closure"), plus anchor notes in the "Virtuoso" bebop system. They show "how unary constraints can have a global effect on the structure of the generated melodies." — [IJCAI PDF](https://www.ijcai.org/Proceedings/11/Papers/113.pdf)
- **Papadopoulos, Roy, Pachet, "Avoiding Plagiarism in Markov Sequence Generation," AAAI 2014.** The MaxOrder constraint (no corpus chunk longer than a bound) is compiled into a "maximum order automaton" and enforced via the REGULAR constraint. Build time and automaton size are linear in the corpus. — [AAAI OJS](https://ojs.aaai.org/index.php/AAAI/article/view/9126); [full text mirror](https://object.cloud.sdsc.edu/v1/AUTH_da4962d3368042ac8337e2dfdd3e7bf3/ml-papers-txt/AAAI/2014/avoiding_plagiarism_in_markov_sequence_generation__15f5df81.txt)
- In that paper, generalized arc consistency of REGULAR on n variables is "achieved in O(n.T) time" (T = number of automaton transitions). Resolution is "backtrack-free", and the authors claim "Our model enables us to make exact solution counting." — [full text mirror](https://object.cloud.sdsc.edu/v1/AUTH_da4962d3368042ac8337e2dfdd3e7bf3/ml-papers-txt/AAAI/2014/avoiding_plagiarism_in_markov_sequence_generation__15f5df81.txt)
- **Pesant, "A Regular Language Membership Constraint for Finite Sequences of Variables," CP 2004, LNCS 3258:482-495.** Filtering works on a layered acyclic graph. Paths from the first to the last layer correspond one-to-one with solutions. A Gecode implementation is domain-consistent and runs in O(n·t) per invocation. — [Gecode mailing list](https://www.gecode.org/users-archive/2004-November/000200.html); [counting-based search, arXiv 1401.4601](https://arxiv.org/pdf/1401.4601); [DOI landing for related CP work](https://www.doi.org/10.1007/11889205_38)
- **Roy & Pachet, "Enforcing Meter in Finite-Length Markov Sequences," AAAI 2013.** The Meter constraint (Markovian, plus metrical rules expressed as cumulative cost functions, which can also enforce cardinality) has a domain-consistency algorithm of *pseudo-polynomial* complexity, via Khovanskii's theorem on sumset growth. — [AAAI OJS](https://ojs.aaai.org/index.php/AAAI/article/view/8661); [Sony CSL PDF](https://csl.sony.fr/wp-content/uploads/2013/06/roy-13a.pdf)
- **Rivaud & Pachet, "Sampling Markov Models under Constraints: Complexity Results for Binary Equalities and Grammar Membership," arXiv 1711.10436 (2017, preprint).** Sampling under binary-equality constraints (equalities between arbitrary, possibly non-adjacent positions) is #P-complete (proof sketched), with three polynomial sub-cases. Grammar membership is #P-complete, and it is tractable for unambiguous grammars and a broader class the paper identifies. — [arXiv](https://arxiv.org/abs/1711.10436)

### Inferences
- In our setting the call is a fixed input, so every "relative" rule (start within K semitones of the call's last note, echo the call's rhythm, contrary motion relative to the call's ending direction) becomes an *absolute* unary or adjacent-binary constraint once the call is substituted. That puts most of our rules in the Pachet-Roy-Barbieri BSC class, where AC is a complete existence test.
- Counting rules ("fewer notes than the call", "at most N notes per bar") are global cardinality constraints. Because the bounds are tiny (24 slots), they fit as an extra counter in automaton state, which is the pseudo-polynomial meter-style approach. Product states stay small (slot × last-pitch × counters).
- "Transpose or sequence the call's first N notes" ties answer notes 1..N to a single unknown offset t, a binary equality among non-adjacent positions (Rivaud & Pachet's #P-hard class in general). With pitch range bounded (about 49 values), the clean exact route is a finite disjunction: enumerate each t, build or check one DFA or chain per t, and take the union. The cost stays polynomial with a constant factor of about 100.

### Gaps
- I did not access the full text of the 2011 *Constraints* paper or Roy & Pachet 2013. Their exact propagator complexities come from abstracts and secondary sources.
- The IJCAI 2011 paper's "width 2" wording conflicts with the usual statement of Freuder's theorem (tree means width 1, so AC gives backtrack-free search). I could not fetch Freuder 1982 (JACM) to verify the exact phrasing.
- Rivaud & Pachet 1711.10436 is a preprint with a "sketched" #P-completeness proof. I found no peer-reviewed version.
- I did not find the paper "Markov constraints for generating lyrics with style" (Barbieri et al., ECAI 2012) in this pass, so I cannot report its results.

---

## Q2. Music constraint systems (Strasheela, PWConstraints/PMC/Score-PMC, Cluster Engine, OMClouds, Situation, BackTalk): complete or heuristic?

### Takeaway
Most classical music CP systems use *complete* search (backtracking, possibly with forward checking or propagation), so they decide existence exactly but in worst-case exponential time. OMClouds (adaptive or local search) is explicitly *incomplete*. None of them provide a polynomial-time existence guarantee for their general rule languages.

### Cited Findings
- Anders & Miranda, "Constraint Programming Systems for Modeling Music Theories and Composition," *ACM Computing Surveys* 43(4), Art. 30, 2011. — [Plymouth portal](https://researchportal.plymouth.ac.uk/en/publications/constraint-programming-systems-for-modeling-music-theories-and-co/); [PDF copy](https://cm-mail.stanford.edu/pipermail/cmdist/attachments/20111228/c7bd1856/attachment.pdf)
- **PWConstraints (PMC, Score-PMC; Laurson):** "performs a chronological backtracking (BT) search … BT performs a complete search (i.e., if there exist solutions, the algorithm finds one)". There is no domain filtering. "Heuristic constraints" affect only value ordering, not completeness. — [Anders & Miranda PDF](https://cm-mail.stanford.edu/pipermail/cmdist/attachments/20111228/c7bd1856/attachment.pdf)
- **Situation (Rueda et al.):** uses a variation of forward checking (minimal forward checking with lazy evaluation). — [Anders & Miranda PDF](https://cm-mail.stanford.edu/pipermail/cmdist/attachments/20111228/c7bd1856/attachment.pdf)
- **BackTalk (MusES):** uses arc consistency "only once for prefiltering the domains before the actual search starts". — [Anders & Miranda PDF](https://cm-mail.stanford.edu/pipermail/cmdist/attachments/20111228/c7bd1856/attachment.pdf)
- **Strasheela (Anders; Oz/Mozart):** "combines constraint propagation with search … before every single decision made by the search, constraint propagation runs". Domains are restricted to integers and integer sets. Table II of the survey: the PMC, Score-PMC, Situation, BackTalk and Oz/Strasheela solvers can find all solutions, and OMClouds cannot. — [Anders & Miranda PDF](https://cm-mail.stanford.edu/pipermail/cmdist/attachments/20111228/c7bd1856/attachment.pdf)
- **OMClouds (Truchet, Assayag, Codognet):** "Whereas most music constraint systems support a complete search, OMClouds is based solely on a heuristic search strategy" (adaptive or local search with tabu). "Adaptive search does not execute a complete search … the system cannot output all solutions … may never find a true all-interval series." — [Anders & Miranda PDF](https://cm-mail.stanford.edu/pipermail/cmdist/attachments/20111228/c7bd1856/attachment.pdf); original: Truchet & Codognet, "Solving musical constraints with adaptive search," *Soft Computing* 8(9), 2004 (cited in the survey)
- **Ebcioglu's BSL / CHORAL** used backtracking with backjumping (intelligent backtracking) for Bach chorale harmonization. — [Anders & Miranda PDF](https://cm-mail.stanford.edu/pipermail/cmdist/attachments/20111228/c7bd1856/attachment.pdf)
- **Cluster Engine (Sandred, 2010, PWGL; now in MOZlib for Max):** "runs several search engines in parallel", which makes decision order more flexible. It descends from OMRC and PWMC. — [Sandred research page](https://sandred.com/research-1); [Beds portal: PWGL libraries Cluster Engine/Cluster Rules](https://researchportal.beds.ac.uk/en/publications/a-novel-music-constraint-programming-system-the-pwgl-libraries-cl-3/)

### Inferences
- These systems answer "does a solution exist?" correctly only because they explore the full tree (exponential worst case). Our bounded, mostly chain-structured problem can do better: a forward DP over automaton states, or AC on the chain, is complete *and* polynomial.
- OMClouds-style and other local-search tools should not be used as the existence decider in a verified app. A failure to find a solution there proves nothing.

### Gaps
- I did not find a primary source stating whether Cluster Engine's search is complete. Its backtracking or backjumping design suggests it is, but this is unverified.
- No formal verification (in Coq, Lean or Isabelle) of any music constraint solver turned up in this pass.

---

## Q3. Metaheuristic music generation (Herremans & Sörensen, GenJam, etc.): completeness

### Takeaway
These methods optimize a rule-based or learned objective and are incomplete. They cannot certify that no valid melody exists.

### Cited Findings
- Herremans & Sörensen, "Composing first species counterpoint with a variable neighbourhood search algorithm," *J. Mathematics and the Arts* 6(4):169-189, 2012. It starts from a random melody and changes one or two notes per move. The objective quantifies Fux's counterpoint rules, and VNS beat their GA. — [SUTD repository](https://repository.sutd.edu.sg/esploro/outputs/journalArticle/Composing-first-species-counterpoint-with-a/9911708209846); [Herremans site](https://dorienherremans.com/node/19); [RePEc working paper](https://ideas.repec.org/p/ant/wpaper/2011017.html)
- Follow-ups extended this to fifth species and replaced the rule-based objective with a learned model (with Conklin, 2014). — [Herremans site](https://www.dorienherremans.com/node/20)
- **GenJam (Biles):** an interactive genetic algorithm (human-provided fitness) that can "trade fours or eights interactively with a human soloist", which is a call-and-response setting, but by evolutionary search. — [GenJam ICMC'98 PDF](https://genjam.org/wp-content/uploads/2019/07/bilesicmc98.pdf); [AAAI AIIDE demo](https://ojs.aaai.org/index.php/AIIDE/article/view/12640)

### Inferences
- VNS, GA and adaptive search are all local or stochastic and make no completeness claims. At most they are useful as *generators*, with a separate exact checker gating the output.

### Gaps
- I did not verify the exact objective or rule list in Herremans 2012 (full PDF not opened).

---

## Q4. Call-and-response, jazz improvisation, and Control Improvisation (Donzé, Fremont, Seshia)

### Takeaway
Control Improvisation is the closest formal precedent. Improvisations are words of bounded length in a hard-spec language H, a fraction of at least 1−ε must also lie in a soft spec S, and each word must have probability between λ and ρ. When both specs are DFAs, feasibility and sampling are polynomial. With NFAs or general CFGs they are #P-hard. For our "does any valid answer exist?" question (hard spec only, no randomness bounds), feasibility is just bounded-length non-emptiness of a DFA (or product DFA), which is polynomial.

### Cited Findings
- **Donzé, Valle, Akkaya, Libkind, Seshia, Wessel, "Machine Improvisation with Formal Specifications," ICMC 2014, pp. 1277-1284.** Generates monophonic jazz solos over a given harmonization in two phases. A "generalization" phase learns an automaton from a training melody, and a "supervision" phase enforces a formal specification on pitch and rhythm. — [Seshia pub page](https://people.eecs.berkeley.edu/~sseshia/pubs/b2hd-donze-icmc14.html); [PDF](https://people.eecs.berkeley.edu/~sseshia/pubdir/icmc14.pdf); [ICMC proceedings PDF](https://speech.di.uoa.gr/ICMC-SMC-2014/images/VOL_2/1277.pdf)
- Follow-up: Valle et al., "Specification Mining for Machine Improvisation with Formal Specifications," *ACM Computers in Entertainment*, 2016. — [Seshia pub page](https://people.eecs.berkeley.edu/~sseshia/pubs/b2hd-valle-msm16.html)
- **Fremont, Donzé, Seshia, (Wessel), "Control Improvisation," FSTTCS 2015 (arXiv 1411.0698).** Identifies efficiently solvable cases and cases that are #P-hard or undecidable, and proposes SAT-based approximations for intractable cases. — [arXiv 1411.0698](https://arxiv.org/abs/1411.0698v2); [Seshia pub page](https://people.eecs.berkeley.edu/~sseshia/pubs/b2hd-fremont-fsttcs15.html)
- **Extended version (arXiv 1704.06319), definitions.** An improvisation is w ∈ L(H) with m ≤ |w| ≤ n, and an admissible one is also in L(S). A distribution is an improvising distribution if it puts all its mass on I (hard), at least 1−ε on A (soft), and λ ≤ D(w) ≤ ρ for every w ∈ I (randomness). The CI problem asks whether one exists and, if so, for a sampler. — [ar5iv 1704.06319](https://ar5iv.labs.arxiv.org/html/1704.06319)
- **Thm 3.1:** feasible iff 1/ρ ≤ |I| ≤ 1/λ, (1−ε)/ρ ≤ |A|, and |I|−|A| ≤ ε/λ. Feasibility therefore reduces to *counting* |I| and |A|. — [ar5iv 1704.06319](https://ar5iv.labs.arxiv.org/html/1704.06319)
- **Complexity results:**
  - Thm 4.4: polynomial-time scheme for CI(DFA, DFA).
  - Thm 4.6: CI(NFA, DFA) and CI(DFA, NFA) are #P-hard.
  - Thm 5.1: CI with a general CFG in either role is #P-hard.
  - Thms 5.9 and 5.11: polynomial for an unambiguous CFG paired with a DFA.
  - Thm 5.13: CI(UCFG, UCFG) is #P-hard.
  - Thm 6.6: approximate scheme for symbolic (Boolean-formula) specs using an NP oracle.
  - Sec. 7: with multiple soft constraints, feasibility is #P-hard even for DFAs.
  - The earlier unbounded-length formulation was undecidable for probabilistic automata. The bounded-length version is solvable with a #P oracle.
  — [ar5iv 1704.06319](https://ar5iv.labs.arxiv.org/html/1704.06319); [arXiv 1704.06319](https://arxiv.org/abs/1704.06319)
- **Impro-Visor (Keller & Morrison, "A Grammatical Approach to Automatic Improvisation," SMC 2007)** generates jazz solos from probabilistic grammars, and grammars can be learned from transcribed solos. It is generative, not a constraint decider. — [HMC PDF](https://www.cs.hmc.edu/~keller/jazz/improvisor/ImprovingImprovisationSkills.pdf); [Wikipedia](https://wikipedia.com/wiki/Impro-Visor)
- **Pachet's "Answer" melody type** (last note equals the first input note, enforced as a unary constraint over a Markov model) is a direct call-and-response precedent in the exact AC-based framework. — [IJCAI 2011 PDF](https://www.ijcai.org/Proceedings/11/Papers/113.pdf)

### Inferences
- The #P-hardness in CI comes from *counting* (needed for the λ/ρ randomness bounds) when specs are nondeterministic or ambiguous. Plain non-emptiness of an NFA or CFG is polynomial. So for a pure existence check, NFAs and CFGs would also be fine. Determinism matters only if we later want exact uniform sampling or counting.
- Our rule set can be expressed as an intersection of DFAs over a per-slot alphabet ({rest} ∪ {pitch 40..88}, about 50 symbols, 24 positions). With the call fixed, each rule is a small DFA:
  - max-leap: state = last pitch;
  - per-bar count: a counter of at most 12;
  - fewer-than-call: a counter up to the call's count;
  - avoid pitch class, range, and chord tone on a beat: unary masks;
  - start within K of the call's last note: a first-note flag;
  - contrary motion: state = first or last pitch plus direction.
  Their product can be explored by forward DP or BFS without materializing the product (layered-graph reachability as in Pesant's REGULAR). That is a sound and complete existence check, polynomial for fixed rule parameters, and it fits the Lean 4 proof style "DP reachable-set equals set of valid prefixes" by induction on length.
- Features that break polynomial tractability in this literature are:
  - arbitrary-arity constraints linking non-adjacent positions without a bounded parameter (binary equalities, Rivaud & Pachet);
  - ambiguous grammars or NFAs, but only *when counting or sampling*;
  - multiple soft constraints (Fremont et al. Sec. 7).
  Global counting with small numeric bounds is pseudo-polynomial (Roy & Pachet meter), and harmless here because the bounds are ≤ 24.

### Gaps
- I did not read the final reference list or the Sec. 7 details of 1704.06319 in full (the page was truncated at 100k characters).
- I found no published work specifically on *verified* (proof-assistant) melody constraint solvers or on call-and-response rule sets of the kind we need. This appears to be novel territory.

---

## Q5. Which representations give polynomial existence checks, and what breaks it?

### Takeaway
A chain of variables with only unary and adjacent-binary constraints is a tree, so AC decides existence and gives backtrack-free generation. A DFA/REGULAR encoding gives GAC in O(n·|δ|) with exact counting. Bounded-lookback constraints (window k) can be reduced to the chain case by grouping k-grams, or handled with stronger consistency (path consistency for windows of 3). The things that break tractability are constraints linking arbitrary positions (binary equalities, #P-complete for sampling), nondeterministic or ambiguous specs (for counting), and multiple soft specs. General CSPs with arbitrary-arity constraints need complete search (exponential worst case, as in all classical music CP systems).

### Cited Findings
- Tree-structured (chain) CSP + AC means backtrack-free search (Freuder 1982, as applied in Pachet et al.). AllDiff on consecutive triples is handled via path consistency in O(n³). — [IJCAI 2011 PDF](https://www.ijcai.org/Proceedings/11/Papers/113.pdf)
- REGULAR GAC in O(n·T), the layered-graph or path view, and exact counting. — [Papadopoulos et al. AAAI 2014 text](https://object.cloud.sdsc.edu/v1/AUTH_da4962d3368042ac8337e2dfdd3e7bf3/ml-papers-txt/AAAI/2014/avoiding_plagiarism_in_markov_sequence_generation__15f5df81.txt); [Gecode note](https://www.gecode.org/users-archive/2004-November/000200.html)
- Higher-order Markov is handled by an alphabet of k-grams ("a valid Markov transition is a pair of overlapping k-grams"). — [Papadopoulos et al. AAAI 2014 text](https://object.cloud.sdsc.edu/v1/AUTH_da4962d3368042ac8337e2dfdd3e7bf3/ml-papers-txt/AAAI/2014/avoiding_plagiarism_in_markov_sequence_generation__15f5df81.txt)
- Cumulative-cost (meter) and cardinality: pseudo-polynomial domain consistency. — [Roy & Pachet AAAI 2013](https://ojs.aaai.org/index.php/AAAI/article/view/8661)
- Binary equalities and grammar membership: #P-complete sampling in general, with tractable sub-cases (unambiguous grammars). — [Rivaud & Pachet arXiv 1711.10436](https://arxiv.org/abs/1711.10436)
- DFA vs NFA/CFG in control improvisation: polynomial vs #P-hard. — [ar5iv 1704.06319](https://ar5iv.labs.arxiv.org/html/1704.06319)
- Grammar constraints as an extension of REGULAR: Quimper & Walsh "Global Grammar Constraints" (CP 2006); Sellmann "The Theory of Grammar Constraints". — referenced via [Pesant search summary / arXiv 1401.4601](https://arxiv.org/pdf/1401.4601)

### Inferences
- **Recommended representation for our app:** the answer is a length-24 word over Σ = {rest, hold?, 40..88}. Each rule is a deterministic automaton with explicit small state, instantiated with the fixed call. The decider is forward reachability over the product state space, which is the same as the layered graph in REGULAR or the AC fixpoint on the chain. Soundness: every accepted path is a valid answer. Completeness: every valid answer is a path, by induction over slots.
- **Handling the hard rules:**
  - "Echo the call's rhythm" makes the onset mask a unary constraint (onset/rest per slot fixed).
  - "Transpose or sequence the first N notes" should be existentially quantified over a finite offset set, as a union of DFAs. Alternatively, put the offset in automaton state (fixed once at the first note), which multiplies the state space by about 100.
- Rough state bound: 24 slots × (last pitch ≈ 50) × (notes-in-bar ≤ 13) × (total notes ≤ 25) × (offset ≤ ~97) × small flags. That is about 10⁷ worst case, but in practice far smaller with pruning. It is easily decidable exactly in a hackathon setting.

### Gaps
- I did not find a primary statement of Freuder 1982 or a textbook citation (Dechter 2003) in this pass. The chain-AC claim relies on the IJCAI 2011 paper's restatement.
- No literature found applying REGULAR or Control Improvisation specifically to rhythm-grid (onset-slot) representations with triplet/shuffle grids. The modeling above is my own inference.
