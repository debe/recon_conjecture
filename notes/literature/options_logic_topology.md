# Attack options from logic, categories, topology, groups and computation (two residuals)

Librarian sweep, 2026-11-25. Literature only. Nothing here is checked; nothing is claimed for the
residuals.

**Targets.** `conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure` and
`..__dominating_edge_impure`: G and Ḡ connected; a dominating edge, or both diameters ≤ 2; no pure
degree class; no unique-copy factorizing pair.

**Known members** (t4 §8): `GhEJ]o`, `GhdYLc`, `GhEKzW` (n = 8); ``K[N_ZpBVe`q{``,
`KbcrMZwA~c@r` (n = 12); ``OpyHvCM]IFJpsMdwu`pJp`` (n = 16). All have degrees d and d + 1, half
the vertices each.

**Covered elsewhere, not repeated:** hom counts, Prop R, Lovász, Dvořák, DGR, Roberson, game
comonads (`hom_counts_and_logic.md`); Nash-Williams, ACKR, Mnukhin, Pouzet–Thiéry, Oliveira–Thatte
(`groups_and_harmonic.md`); spectral chain, Mulla, Farhadian, Chinn (`novelty_open_core_lemmas.md`).

**Tags:** [text] = full text read this session; [abstract]; [secondary] = read in another paper;
UNVERIFIED = memory or search snippet. "Derived" = my own observation; "guess" = a guess.

**Per option:** (1) idea; (2) sources; (3) bite on the residual; (4) graph-specific?; (5) Lean
cost; (6) first step. Item (4) is the filter: if a method also works for tournaments (Stockmeyer)
or 3-uniform hypergraphs (Kocay), it cannot close a residual alone.

## A. Finite model theory and counting logics

**A1. Colour refinement (CR) along σ, plus amenability.**
1. CR (1-WL, C², tree hom counts) identifies the *amenable* graphs. If a hypomorphism σ kept the
   stable CR colours, every amenable graph would be reconstructible. CR round 1 is the degree tie
   and round 2 is Lemma B (neighbour degrees); both are checked. Round ≥ 3 along σ is open.
2. Arvind–Köbler–Rattan–Verbitsky, Comput. Complexity 26 (2017), doi:10.1007/s00037-016-0147-6,
   arXiv:1502.01255 [abstract] (amenable ⇒ compact; decidable in O((n + m) log n)).
   Arvind–Köbler–Verbitsky, arXiv:2406.09351 [abstract] (cards up to CR still determine
   connectedness). Cotta–Morris–Ribeiro, NeurIPS 2021, arXiv:2110.00577 [abstract].
   "Hypomorphic ⇒ CR-equivalent": no source found.
3. Partly. Members have |Aut| of 2, 6 or 8, so some may be amenable. Guess: the
   self-complementary ones are not.
4. No. CR and Lemma B work for digraphs, so Stockmeyer's pairs must be non-amenable. This carves
   out a subclass; it cannot close.
5. Hard. Mathlib has no WL, so the statement would need a hand definition.
6. Red-team screen: CR on the six members and on Stockmeyer's pairs. If no member is amenable,
   drop the option.

**A2. Restricted or minor-closed hom-indistinguishability; EF games.** Does not bite.
- At order n the deck is hom-indistinguishability over graphs on ≤ n − 1 vertices (Prop R).
- On all graphs it is a hom-indistinguishability relation iff RC holds: van Dobben de Bruyn et al.,
  arXiv:2610.07927, Ex. 3.8 [text, earlier sweep].
- The closedness theorems (Roberson, JCTB 2026; Seppelt 2024; Neuen 2024) use unbounded targets.
  The strong Roberson conjecture is reported refuted (Kristjánsson, arXiv:2610.03550, Ci₁₀₁(1,5)),
  UNVERIFIED via MathWorld.
- EF-game or quantifier-rank characterisations of recognizability: search negative.
- Generic, very hard in Lean. There is no new first step; `kelly_hom_image_count` stays the brick.

## B. Category theory

**B1. A "deck comonad"; species.** Does not bite.
- Abramsky–Jakl–Paine (arXiv:2205.06589, doi:10.1007/978-3-031-10736-8_2) [abstract] attach a
  density comonad (a Kan extension) with a hom-counting theorem to any standard graph class.
- Applied to graphs on ≤ n − 1 vertices, with Prop R, it gives a categorical deck at order n
  (derived; guess).
- In species terms, the deck is the pushforward along F′ → F (delete the point), which is E2 of
  `groups_and_harmonic.md` again.
- No deck comonad was found in the literature.
- Signature generic, a reformulation only, very hard in Lean. No first step.

## C. Algebraic and combinatorial topology

**C1. Clique and independence complexes, χ̃, homotopy type.**
1. Derived, elementary:
   - The f-vectors of Cl(G) and Ind(G) = Cl(Ḡ) are clique and independent-set counts, given by
     Kelly for sizes < n (size n means K_n or its complement). So χ̃(Cl G) and χ̃(Ind G) are
     recognizable.
   - Ind(G) = Ind(G − v) ∪ v∗Ind(G − N[v]) (standard; citation UNVERIFIED) needs N(v) inside the
     card, which is the unknown itself.
   - Recognizability of Betti numbers or homotopy type: search negative.
2. Rinaldo–Romeo, arXiv:1706.00863 [abstract], circulants only.
3. No lever.
4. No: the same complexes exist for hypergraphs and tournaments.
5. Easy via `cliqueFinset` (`Combinatorics/SimpleGraph/Clique.lean:845`). `AbstractSimplicialComplex`
   (`AlgebraicTopology/SimplicialComplex/Basic.lean`) has no homology.
6. `kelly_clique_count`: a corollary of the checked induced counts; library value only.

**C2. Matroid and topological-space decks (warning settings).** Does not bite.
- Brylawski, LNM 406 (1974) [abstract]: deletions give the subgeometry generating function.
- Brylawski, *On the nonreconstructibility of combinatorial geometries*, JCTB 19(1) (1975)
  72–76, doi:10.1016/0095-8956(75)90074-X (content UNVERIFIED).
- Pitz–Suabedissen, arXiv:1311.7625 [abstract]: ℝ and ℚ are reconstructible from X − x; the
  Cantor set is not.
- Mathlib has `Combinatorics/Matroid/` (including `Minor/`) but no deck.

## D. Group theory and structure

**D1. Two card types (Zinchenko 2026). On the residual's face.**
1. Let t(G) be the number of card isomorphism types. Zinchenko claims (Thm 1.1): t(G) = 2,
   n ≥ 3 ⇒ G is reconstructible.
   - Prop 2.3 forces degrees d and d + 1 with one card type per degree class.
   - Lemma 2.4: the number of high neighbours is constant on low vertices (b) and on high
     vertices (e).
   - §§3–10: extensions of a card and eigen-identities A_K f = (θ − s) f.
   - His Lemma 2.2 is Mulla's (★), which is known.
2. M. Zinchenko, arXiv:2611.13728v1 (10 Nov 2026), 28 pp. [text: §§1–2 and the end of §10 read,
   §§3–9 skimmed]. Unrefereed, so the theorem is UNVERIFIED.
3. **Yes, directly** (evidence only, networkx): t = 2 for `GhEJ]o` (|Aut| 8),
   ``K[N_ZpBVe`q{`` (|Aut| 6) and ``OpyHvCM]IFJpsMdwu`pJp`` (|Aut| 8); t = 5, 5, 6 for the rest.
4. Yes if correct: it uses symmetry of A_K. Audit: do Stockmeyer pairs with t = 2 exist? If so,
   the digraph version of the argument must break, and the break locates the graph-specific step.
5. Medium–hard, about 1500–3000 lines (guess): `Matrix.mulVec` over ℚ plus card-extension
   plumbing like the checked gluing lemma.
6. Lemma 2.4 first (elementary, on the checked degree tie). Target: reduce each residual to
   t(G) = 2 ∪ (t(G) ≥ 3 ∧ residual). Predicate sketch (not elaborated):
   `∃ a b : Fin n, ∀ x, Nonempty (Recon.card G x ≃g Recon.card G a) ∨ Nonempty (Recon.card G x ≃g Recon.card G b)`.

**D2. Modular decomposition (Ille; Brignall–Georgiou–Waters).**
1. Results: primeness (no module with 1 < |M| < n) is recognizable (Ille); the skeleton is
   reconstructible since Skel(G − v) ≤ Skel(G) (BGW Thm 3.2).
   - Thm 4.1: reconstructible if |K| ≤ n − 2 and some interval I_{k*} has I_{k*} − u ∉
     {I_j : j ∈ Orb_K(k*)}.
   - Cor 4.2: Aut(K) trivial; Cor 4.3: K vertex-transitive; Thm 4.4: |K| = n − 1 and K has no
     pseudosimilar vertices, plus an orbit condition.
2. Brignall–Georgiou–Waters, J. Comb. 3(1) (2012), doi:10.4310/JOC.2012.V3.N1.A6, arXiv:1112.1509
   [text]. Via BGW [secondary]: Ille, NATO ASI C 411 (1993) 189–198; Basso-Gerbelli–Ille,
   CRAS 316 (1993); Schmerl–Trotter, Discrete Math. 113 (1993).
3. Partly. It splits each residual into prime ∪ decomposable. The leftovers are BGW's
   "hereditary orbits" and |K| = n − 1 cases. Guess: the self-complementary members are prime.
4. Mostly no. Ille's result is for binary relations, so it covers tournaments. The regular
   skeleton step has a score-regular tournament analogue (derived). It shrinks; it does not close.
5. Medium–hard. Modules are easy to state; Ille needs Schmerl–Trotter. Mathlib has no modules.
6. Screen: is any residual member decomposable for n ≤ 10? If not, note "prime" in the residual
   description; if so, propose a child after BGW Thm 4.1.

**D3. Pseudosimilar pairs.**
- Impurity is a pseudosimilarity phenomenon: G − x − y ≅ G − x′ − y′ with different adjacency, so
  no automorphism maps one pair to the other.
- Godsil–Kocay: pseudosimilar *vertices* arise from an automorphism of a larger graph with part of
  an orbit deleted. JCTB 32 (1982) [secondary, pages UNVERIFIED]; Kocay, J. Austral. Math. Soc.
  (1984) [abstract]; Lauri's survey, Ars Combin. 46 (1997), UNVERIFIED.
- No pair version was found.
- Description language only; generic (digraphs have pseudosimilarity too); hard in Lean.
- First step: a sketch testing whether the n = 8 impure pairs lift to a Godsil–Kocay graph.

**D4. Vertex-transitive and Cayley graphs, orbit algebras.** Does not bite.
- These graphs are regular, hence pure (t4 bit law), so the residual excludes them.
- The members have 2–5 orbits and |Aut| ≤ 8, far below Nash-Williams-type bounds.
- Cameron, *Stories from the age of reconstruction*, Congr. Numer. 113 (1996): UNVERIFIED.

## E. Relational and order-theoretic reconstruction

**E1. Labelled hypomorphy (Lopez), difference classes; what separates the settings.**
1. R and R′ on one set are (≤ k)-hypomorphic if R↾K ≅ R′↾K for all |K| ≤ k.
   - Lopez: finite binary relations are (≤ 6)-reconstructible, via *difference classes*
     (components of the graph of pairs with R′(a,b) = R(b,a) ≠ R(a,b)).
   - For graphs the labelled notion is trivial (k = 2 gives G = H); its content is orientation.
     Labelled, tournaments are tame; unlabelled vertex decks are where they fail.
   - Pouzet: ternary relations have no threshold; hypomorphic, non-isomorphic pairs exist on 2m
     points for every m [secondary, arXiv:1604.05839].
2. [secondary, via Ben Brahim–Sayar, Filomat 39:21 (2025) 7451–7464, doi:10.2298/FIL2521451B,
   text]: Lopez, CRAS 274, 275 (1972), Z. Math. Logik 24 (1978) 303–317; Lopez–Rauzy (sizes
   2, 3, 4, n − 1); Boudabbous–Delhommé, EJC 37 (2014) 43–67. Pouzet, JCTB 26 (1979) 22–34
   (citation only). Dammak–Lopez–Pouzet–Si Kaddour, arXiv:math/0601118 [abstract]: up to
   complement, k-hypomorphy gives G′ ∈ {G, Ḡ} for 4 ≤ k ≤ n − 4.
3. Guess: a possible bite. t4's twist lemma (L5–L7) puts H = G_g on the *same* labels, differing
   only at pairs through u and v. A difference-class analysis of (G, G_g) might exclude twists.
4. Unclear: the twist pair is not labelled-hypomorphic, so Lopez's separation does not transfer
   automatically.
5. Medium: difference classes are `SimpleGraph.ConnectedComponent` of an explicit graph.
6. A sketch: the difference graphs of (G, G_g) for the n = 8 members.

**E2. Posets.** McKay checked posets up to 13 points [text]; Rampon's survey, Discrete Math. 291
(2005). No known failure, no lever. Skip.

## F. Computation and certificates

**F1. McKay's method and its coverage.**
1. Method (Thm 2.1(b)): canonical-construction-path generation (geng). Hypomorphic graphs are
   siblings under one maximal card. Siblings are compared by edge/triangle hash, then card degree
   sequences, then full isomorphism.
2. McKay, Australas. J. Combin. 83(3) (2022) 448–457, arXiv:2102.01942 [text].
3. Evidence on the face, not usable in Lean:
   - Thm 3.1(h) checks degree ranges (5,6; 14), (6,7; 14), (4,5; 15) and (3,4; 16). So
     two-degree members at n = 14 with degrees 5–7 are reconstructible.
   - The n = 16 member (degrees 7, 8) is outside every checked range.
   - Self-complementary graphs to n = 17: Gupta et al., arXiv:1012.5995 [abstract; "weak
     reconstruction" undefined, UNVERIFIED].
4–5. The search is generic (tournaments are checked to 13 too); Lean is infeasible
   (6 × 10¹³ graphs).
6. Aim red-team hunts above the (h) ranges: n = 16, degrees 7–8.

**F2. SAT/LRAT certificates under our gate.**
1. An external search emits certificates and the kernel replays them.
2. Subercaseaux et al. (with Carneiro, Heule), ITP 2024, doi:10.4230/LIPIcs.ITP.2024.35,
   arXiv:2403.17370 [abstract]: verified encoding plus an external LRAT checker. Mathlib
   `Tactic/Sat/FromLRAT.lean` (`lrat_proof`, line 621). SAT on reconstruction: search negative.
3. Fixed n only, so it cannot reach the statement itself. Useful as an anchor: a check that
   `GhEJ]o` satisfies the residual predicate shows non-vacuity at n = 8.
4. Not applicable.
5. Gate: `lrat_proof` takes string literals (forbidden); `bv_decide` reportedly uses
   `Lean.ofReduceBool` (UNVERIFIED for v4.36; the axiom check rejects it). Only `decide` /
   `decide +kernel` sized certificates pass.
6. The n = 8 anchor via explicit isomorphisms plus `decide`. Medium: ¬GLUE needs Aut of 6-vertex
   graphs enumerated.

**F3. The Lean RH announcement as a process model.**
- Lean FRO and Mathlib Initiative blog, 21 Nov 2026 [text]: Alpöge's library (17 M lines,
  Mathlib only) is reported to prove Mathlib's `RiemannHypothesis`; statement match by `comparator` and
  `con-leche --compare`; proof replayed by the kernel and independent checkers on an *inert
  export*. **The post does not mention AI**, so "AI + Lean" is UNVERIFIED. No mathematics for us.
- Process idea (a human-only change): replay `Checked/` with an independent checker in CI.

## Ranked shortlist (judgements of value, not results)

1. **D1, Zinchenko t(G) = 2.** The only option whose class demonstrably contains residual
   members (3 of 6, all with |Aut| ≥ 6), and it has a graph-specific ingredient (symmetric A).
   Next: red-team audit of §§3–10 and a Stockmeyer t = 2 check, then a reducer split on
   t(G) = 2. Risk: unrefereed preprint.
2. **D2, modular decomposition.** Published, elementary, moderate Lean cost. Generic, so it
   shrinks and cannot close. Screen first: are the members prime?
3. **A1, CR plus amenability.** The checked Lemma B is CR round 2, so a "round k along σ" lemma
   is the natural next counting brick. No source, and it may be as hard as RC. Screen amenability
   of the members and of Stockmeyer's pairs first.

Not recommended: A2, B1, C1, C2, D4, E2; F1/F2 only for anchors and hunts.
