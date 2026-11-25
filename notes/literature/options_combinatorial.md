# Attack options for the two open residuals: combinatorics, structure, probability, extremal

Librarian sweep, 2026-11-25. Literature only, plus small evidence checks (marked *evidence*).
**Nothing here is checked, and nothing here closes a residual.** Targets:
`conj_kelly_ulam__connected_dominating_or_diam2__{diam2_impure,dominating_edge_impure}`.
Residual = G, Ḡ connected; dominating edge, or both diameters ≤ 2; no pure degree class; no
unique-copy factorizing pair. Not repeated here: `attack_map.md`, `structural_reductions.md`
(GMP, Aravind–Monikandan, Clifton, ℓ-decks), `algebraic_methods.md` (Kocay, Nash-Williams,
Lovász/Müller), `groups_and_harmonic.md`, `novelty_open_core_lemmas.md`, sketches t1–t4.
Tags: **read** (full text or relevant section), **abstract** (abstract or metadata only),
**secondary** (quoted by another paper), **UNVERIFIED** (not seen).

## 0. The face of the residual (*evidence*, for scoring "does it bite")
- The known members are t4 §8: `GhdYLc`, `GhEKzW`, `GhEJ]o` (n = 8), ``K[N_ZpBVe`q{``,
  `KbcrMZwA~c@r` (n = 12) and ``OpyHvCM]IFJpsMdwu`pJp`` (n = 16). My checks
  (scratchpad scripts, networkx) find all six:
  - **prime** (no nontrivial module) and **p-connected** (Jamison–Olariu);
  - non-chordal, with **no clique separator**;
  - vertex connectivity = δ = n/2 − 1 in G and in Ḡ;
  - degrees (n/2 − 1)^{n/2} (n/2)^{n/2}.
- Full residual at n = 8 (dominating edge 26, D2 5; counts agree with t4 §7):
  - decomposable: 4 (DE) and 0 (D2), all of them through twins;
  - p-disconnected: 0 and 0; chordal: 3 and 0; self-complementary: 1 and 1.
- At n = 7 the residual is 15 graphs, all DE; 1 is decomposable, 0 are p-disconnected.
- **Consequence:** structure theory that needs a module, a P₄-split or a clique separator
  misses every known hard member. These checks are on small graphs only, so they are not an
  argument for all n.

## 1. Options

**O1. Modular decomposition, P₄-structure, Tyshkevich decomposition.**
1. Idea: a nontrivial module M gives G as a quotient (skeleton) inflated by G[M]. Recover the
   skeleton and the modules from the deck, then glue them.
2. Sources:
   - Brignall, Georgiou, Waters, *Modular decomposition and the Reconstruction Conjecture*,
     arXiv:1112.1509 (2011, no journal ref on arXiv). **read** via ar5iv: Thm 3.2 (the
     skeleton is reconstructible), Cor 4.2 (Aut(skeleton) trivial and |K| ≤ n − 2
     ⇒ reconstructible), Cor 4.3 (vertex-transitive skeleton). Open: a single interval of
     size 2 with pseudosimilar structure, and hereditary orbits (their §5).
   - Ille, "indecomposable graphs are recognisable"; Basso-Gerbelli–Ille, two nontrivial
     intervals ⇒ the skeleton and the intervals correspond. Both **secondary** via BGW
     Thm 2.6 and [1]. Schmerl–Trotter critical-indecomposability: **secondary**.
   - P. Skums, *Reconstruction of p-disconnected graphs*, arXiv:0804.4093 (2008). **read**.
     p-disconnected graphs are reconstructible. Lemma 2.5: G is p-disconnected iff G is not
     a spider and at most one card is p-connected. Corollaries: 1-decomposable graphs (Turin
     1987, Vestsi AN BSSR, **secondary**) and P₄-tidy graphs. Thatte, JGT 19 (1995) 549–561,
     P₄-reducible graphs: **secondary**.
   - Hemminger: no module or reconstruction result found in these sources. UNVERIFIED.
3. Bite: small. It removes the 4 twin-type DE members at n = 8. It misses every D2 member and
   the whole face (§0).
4. Graph-specific? Partly.
   - *Evidence*: in the repo's Stockmeyer construction (`t1_stockmeyer_check.py`, n = 5), C₂
     has the module {0, 2, 3} and B₂ is prime, yet they are hypomorphic. So the tournament
     analogue of Ille's recognizability fails.
   - BGW gluing (Thm 4.1) is orbit counting and probably transfers.
5. Lean: high. Mathlib has no modules, quotients by modules or P₄-connectivity. Expect
   800+ lines for Skums.
6. First lemma: `kelly_twin_pair_recognizable`, i.e. "G has two vertices with
   N(x) ∖ {y} = N(y) ∖ {x} iff every H hypomorphic to G does". This is guessed true (the
   graph case of Ille's theorem) but has no source.

**O2. Pseudosimilarity and removal-similar pairs.**
1. Idea: impurity is a two-vertex pseudosimilarity: G − x − y ≅ G − x′ − y′ with x ~ y,
   x′ ≁ y′. A structure theory of how such pairs arise (constructions, group actions on
   cosets) could restrict the residual to explicit families.
2. Sources:
   - Harary–Palmer, *On similar points of a graph*, J. Math. Mech. 15 (1966) 623–630.
     **secondary** (Kocay's bibliography).
   - Kimble–Schwenk–Stockmeyer, JGT 1981. **secondary**.
   - Godsil–Kocay, *Constructing graphs with pairs of pseudo-similar vertices*, JCTB (1982;
     volume UNVERIFIED). Every graph with a pseudosimilar pair comes from the
     Herndon–Ellzey construction. **secondary**.
   - Kocay, *Graphs, groups and pseudo-similar vertices*, J. Austral. Math. Soc.: k
     mutually pseudosimilar vertices arise from a group acting on cosets. **abstract**.
   - Lauri, *Pseudosimilarity in graphs – a survey*, Ars Combin. 46 (1997) 77–95.
     **abstract** (dblp).
   - Lauri, *Constructing graphs with several pseudosimilar vertices or edges*, Discrete
     Math. (2003). **abstract**.
   - S. Ivanov, arXiv:2609.00394 (Aug 2026), long pseudosimilarity chains. **abstract**.
3. Bite: direct, since the residual is *defined* by such pairs in every degree class. But no
   source studies pairs whose adjacency differs. Vertex pseudosimilarity alone is generic.
4. Graph-specific? No. Pseudosimilar vertices exist in tournaments, and Kocay's coset
   construction is group-theoretic. It can only help through the bit law (t4 §10).
5. Lean: medium for single-graph lemmas; high for the Godsil–Kocay characterisation.
6. First lemma (paper, guess): "an impure pair (x, y), (x′, y′) with deg x = deg x′ forces
   deg y = deg y′ + 1, and the isomorphism G − x − y ≅ G − x′ − y′ carries N(x) ∖ y onto a
   set with the same degree profile in the card". This is a red-team target before any
   proposal.

**O3. Refined pair parameters: codegree typing of the (n − 2)-deck.**
1. Idea: refine t4's Lemma G type (deg x, G − x − y) by the codegree |N(x) ∩ N(y)|. Pair
   counts by codegree, split by adjacency, are recognizable, which gives a "refined pure"
   class.
2. Sources:
   - Gupta–Mangal–Paliwal, Discrete Math. 272 (2003) 291–296: pv(G, i) and pav(G, i) are
     reconstructible. **secondary** via arXiv:2601.00620 Thm 1.
   - Aravind–Monikandan, arXiv:2601.00620 (Jan 2026), **read** (HTML): dv/dav (common and
     exclusive neighbour counts) are reconstructible when γ ≥ 3 (Thms 15, 18). The proofs
     have gaps: Cor 14 is unjustified, Thm 16 cites theorems that do not exist, and
     uniqueness in Thms 20–21 is asserted, not proved. Problems 1 and 2 (weak
     reconstruction of γ = 2 and of diam = co-diam = 2) are open.
   - Manvel 1974 (typed ℓ-deck counts by back-substitution), via Kostochka–West
     arXiv:2004.05527 Lemma 2.3. **read**.
3. Bite (*evidence*): with the key (deg x, type F, codeg(x, y)), 4 of the 6 face members
   have a pure class. Using G or Ḡ, 5 of 6 do; `KbcrMZwA~c@r` stays impure. **Guess:** the
   triple count is not known to be a deck invariant. t4 §9.2 explains why the telescoping
   breaks: the triangle correction is [x ~ y]·codeg, not a bit.
   - Caveat: hypomorphic non-isomorphic graph pairs do not exist for n ≤ 13, so test any
     invariance claim in t4's single-card extension form, never on graph pairs.
4. Graph-specific? The unsplit counts are generic. The adjacency split rests on the bit law
   (graph-specific; it fails on Stockmeyer pairs per t4).
5. Lean: medium, the same pattern as the checked Kelly files, 400–700 lines.
6. First lemma: `kelly_pair_codegree_count`, "for each i, #{non-adjacent pairs with i common
   neighbours} is a deck invariant". This is GMP's theorem: t2 §1 gives the recurrence,
   pinned by q_{n−2} = 0 when Ḡ is connected. Then test the triple invariant before proposing
   "codegree-refined pure ⇒ reconstructible".

**O4. Separations (Heinrich–Kiyomi–Otachi–Schweitzer 2025).**
1. Idea: split along a clean clique separation (A, C, B). Recover each side, annotated with
   the original degrees of C, from suitable cards. Gluing is then forced (their Lemma 24,
   "reconstruction-by-separation", and the distant-vertex Lemma 25).
2. Sources:
   - *Interval graphs are reconstructible*, arXiv:2504.02353 (v2 May 2026). **read**
     (intro and overview). Thm 1 covers interval graphs on ≥ 3 vertices. The authors claim
     the first technique that is compatible with separators of more than one vertex, and
     say it "may be adapted to graphs of bounded treewidth".
   - Earlier: von Rimscha 1983 (unit interval graphs), Giles 1974 (outerplanar).
     **secondary**.
3. Bite: none on the face (no clique separator, connectivity n/2 − 1). It could bite on DE
   members with small separators: by t1 F5 the cut vertices are u and v.
4. Graph-specific? Yes. Tournaments have no separators, and the technique uses undirected
   clique separators and degrees.
5. Lean: very high (structure theory, annotated cards).
6. First lemma: the gluing half of Lemma 24 as a single-graph statement: "two graphs with a
   common clique separator and isomorphic annotated sides that respect the order of
   neighbourhoods on C are isomorphic". Useful only if a class with clique separators is
   carved out of DE.

**O5. Self-complementary and two-degree structure (the observed face).**
1. Idea: exploit an antimorphism τ (G → Ḡ, exchanging the degree classes d and n − 1 − d),
   so that Lemma G and its complement version both apply.
2. Sources:
   - Gupta, Singla, Khandelwal, Tiwari, Srilekha, *Exhaustive verification of weak
     reconstruction for self complementary graphs*, arXiv:1012.5995 (2010; poster ICRTGC
     2010). Computational, up to n = 17. "Weak" is not defined in the abstract. **abstract**.
   - No theorem on reconstructing self-complementary or bidegreed graphs was found (searched:
     self-complementary, biregular, bidegreed, "two distinct degrees").
3. Bite: it aims straight at the face, but not at all of the residual (n = 8: 2 of 31 are
   self-complementary).
4. Graph-specific? **No, and this is a warning.**
   - *Evidence*, my computation on the repo's construction: both Stockmeyer tournaments B_k
     and C_k (n = 5 and 9) are **self-converse**, the tournament analogue of
     self-complementary.
   - A search snippet attributes "the order 2^t + 1 tournaments are self-complementary" to
     Stockmeyer; that is UNVERIFIED in the primary text.
   - So the antimorphism symmetry alone is shared with known counterexamples.
5. Lean: medium for the statement, unknown for any proof.
6. First lemma: none recommended. If pursued, first ask the red team whether t4's Lemma G
   transported along τ adds any constraint beyond Lemma G applied to Ḡ. t4 §9.7 suggests it
   does not.

**O6–O13: options with no bite on the residual (one row each).** Columns: idea and
sources; why there is no bite; whether it is graph-specific; Lean cost and first lemma.

| Option | Idea and sources | Why no bite | Graph-specific? | Lean cost / first lemma |
|---|---|---|---|---|
| **O6. Almost every graph and reconstruction numbers** | Generic graphs have asymmetric, pairwise non-isomorphic (n − 2)-subgraphs. Bollobás 1990, Müller 1976, Korshunov 1971 (**secondary**, see `novelty` 5a). Asciak, Francalanza, Lauri, Myrvold, Ars Combin. 97 (2010) 443–456 (**abstract**). Asilis, Chen, Hansen, Teng, arXiv:2509.21516 (**abstract**): Bollobás's property survives adversarial flips with any constant probability. | The deterministic core is already checked (Lemma P, gluing). Pure covers all of G(n, ½) from n = 10 (t4 §7), so the residual is what is left once the generic graphs are removed. | No. A guess: random tournaments behave alike (UNVERIFIED). | The probability part is useless for `ClassReconstructible`. No first lemma. |
| **O7. Kocay covers and a vertex Nash-Williams lemma** | Counts of covers; the inclusion–exclusion identity for \|Iso(G, H)\| − \|Aut G\| (t4 §9.4). `algebraic_methods.md` A2, A7, A10. | The independence polynomial at −1 has no sign. | No (holds verbatim for hypergraphs and tournaments). | Medium to high. None. |
| **O8. ℓ-decks (2-reconstruction)** | The deck determines the (n − 2)-deck (Kostochka–West arXiv:2004.05527 Obs. 1.3, **read**). 3-regular graphs: arXiv:1908.01258 (**abstract**). Strongly regular graphs: arXiv:2210.11742 (**abstract**). Chinn 1971 (**secondary**). | The known 2-reconstructible classes are regular, hence already pure. The residual is exactly where the (n − 2)-deck is ambiguous on adjacency. | No (it uses less data than the deck). | Needs a k-deck definition in `Basic.lean` (human). None. |
| **O9. Switching classes** | Stanley, JCTB 1985, n ≢ 0 (mod 4) (`groups_and_harmonic.md` S11). Ellingham–Royle and Bondy–Mercier (**secondary**, arXiv:1308.0675). Cavaleri et al. arXiv:2611.13901 (**abstract**). t3 S6: a second reconstruction is a block switch. | The switching deck is a different object. The face lives at n ≡ 0 (mod 4), Stanley's exceptional residue; any link is a guess. | Generic in shape (hypercube harmonic analysis). | High. None. |
| **O10. Degree-sequence structure** | Threshold graphs and unigraphs; one card plus the degree sequence: Mulla 1978, Steane arXiv:1810.02602 (**read**); split unigraphs: Tyshkevich, Discrete Math. 220 (2000) (**secondary**). | Threshold graphs have an isolated or dominating vertex, so they are excluded (own observation). 1-decomposable graphs are p-disconnected (Skums): none at n = 8. | Yes (deg = e(G) − e(G − v)), but already used (T0, (★)). | Low, mostly done. None. |
| **O11. Graph limits and flag algebras** | The deck gives t(F, G) for all \|F\| ≤ n − 1 (own assessment; no source found). | Limits forget n, while Nýdl's ⌊qn⌋ examples show that n must enter exactly. Flag-algebra SDPs certify inequalities, not identities. | No (hypergraph flag algebras exist). | Mathlib has the regularity lemma but no graphons. None. |
| **O12. Products** | Dörfler: Cartesian products are reconstructible. Imrich–Žerovnik, Discrete Math. 150 (1996). Zmazek–Žerovnik, strong products, Discrete Math. 307 (2007). All **secondary**. | Lexicographic products have modules (see O1), and the face members are prime. | Unclear. | `boxProd` exists (`Mathlib/Combinatorics/SimpleGraph/Prod.lean:45`); no factorisation. None. |
| **O13. Other recent arXiv work** | Zinchenko arXiv:2611.13728 (UNVERIFIED); Groenland–Johnston–Scott–Tan, Israel J. Math. 2025; Kostochka–Qu–Ritter–West arXiv:2511.23309; Ramachandran arXiv:2305.14401; Pokorná et al. arXiv:2508.19189 (graphlets, not decks); Tsoukalas et al. arXiv:2605.22763 (**read**, appendix: Lean proof of a *weak bipartite incidence-deletion* variant, labelled, with distinct vertex types). | None of them touches the face. | — | — |

## 2. Methodology lesson: the 2026 Lean RH announcement
- **What was published (read).**
  - Lean blog, 2026-11-21: Alpöge released a 17M-line Lean library proving Mathlib's
    `RiemannHypothesis`. It was certified by a Mathlib-only statement-isolation file,
    `comparator`, `con-leche --compare` and several kernels run on an inert export.
  - **No methodology is described.** There is no blueprint and no decomposition or search
    account.
  - Sutherland's check page (math.mit.edu/~drew/grh/): RH plus GRH for Dirichlet
    L-functions, about 175k modules, the standard three axioms. One comparator run was once
    satisfied by a stub, and one build was non-deterministic.
- **Different results, also read.**
  - Anthropic, Aug 2026, on the proportion of zeta zeros on the critical line, *not* RH:
    about 650 failed ideas, then about 60 role-split subagents, numerical checks and a
    novelty check against 54 arXiv papers.
  - Tsoukalas et al.: agents hide the core difficulty in one `sorry` helper and cite
    hallucinated literature lemmas.
- **Lessons for us.**
  1. Our gate matches that trust model. A second-kernel re-check of an inert export is the
     missing piece.
  2. Breadth first, with validator agents.
  3. Never accept a child that rests on "the literature says".

## 3. Ranked shortlist
1. **O3, codegree-refined pair typing.**
   - It is the only option that touches the face in evidence (5 of 6 members, using G or Ḡ).
   - Its graph-specific ingredient is the bit law, and it is cheap in Lean on top of the
     checked Kelly files.
   - Step 1, GMP's pv/pav recognizability, is a known theorem. Step 2 (the triple count is a
     deck invariant) is a **guess**: red-team it first in single-card extension form.
2. **O2, a pseudosimilarity structure theory for impure pairs.**
   - It aims at the defining property of the residual, and Godsil–Kocay give a template
     (every pseudosimilar pair comes from one construction).
   - It is not graph-specific alone, so it must be fused with the bit law. Thinker work, not
     builder work, for now.
3. **O1, modular / P₄ carving as a cheap child.**
   - It removes the twin-type DE members, and its recognizability half is graph-specific:
     Stockmeyer's n = 5 pair has one prime and one decomposable member.
   - Low value against the face; take it only if a reduction needs a fourth child.

Not ranked: O4 (graph-specific but misses the face; very costly), O5 (shares self-converse
symmetry with the tournament counterexamples), and O6–O12 (generic or no bite).
