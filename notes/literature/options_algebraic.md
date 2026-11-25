# Algebraic, spectral and representation-theoretic attack options on the two residuals

Librarian, 2026-11-25. Literature plus a little computation. **Nothing here is checked.**
"Derivation" = my own paper argument, unchecked. "Computed" = a decidable fact about named graphs,
found by script: evidence, never an argument for all n.

Targets: `conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure` and `__dominating_edge_impure`
(statements read in `lean/Recon/Statements/`): G, Ḡ connected; a dominating edge, or both diameters
≤ 2; no pure degree class (¬PURE); no unique-copy factorizing pair (¬GLUE).

Not repeated: `algebraic_methods.md` A2–A4, A11; `groups_and_harmonic.md` S1–S12;
`hom_counts_and_logic.md`; t3.md (S0–S6, D1–D5, R, R⁺); `novelty_open_core_lemmas.md` row 6.

Source tags: **[read]** full text or the relevant section; **[abs]** abstract or search excerpt;
**[sec]** quoted in another source; **UNVERIFIED** not seen at all.

## 0. Two computed facts that drive the ranking

Scripts were in the session scratchpad (not committed); each is a few lines on top of `t3_lib.py`
and `screen_lib.py`.

**F1. Most known residual members have walk rank 2, the minimum for a non-regular graph.**
W = [1, A1, …, A^{n−1}1]; rank W = number of main eigenvalues.
- t4's self-complementary members `GhEJ]o`, ``K[N_ZpBVe`q{``, ``OpyHvCM]IFJpsMdwu`pJp``: rank W = 2,
  and so is every one of their cards. `KbcrMZwA~c@r`: 6 of 12. `GhdYLc`, `GhEKzW`: 4 of 8.
- New residual members: **SRG minus one vertex** for Paley(13), the 4×4 rook graph, Shrikhande and
  Clebsch. Each lies in `diam2_impure` (n = 12, 15, 15, 15) by the clause transcriptions in
  `screen_lib.py`. Each has exactly two main eigenvalues (Rowlinson 2007 §3 [read]). Paley(9) − v
  is pure; Petersen − v lies in neither branch.

So the residual has a "two main eigenvalues" face. There, Godsil–McKay (rank W ≥ n − 1), the
corank-2 switch (S6) and walk-based DGS criteria are all void.

**F2. A Tutte-free one-card closed-walk test decides every known residual member.**
- Test: t3's feasibility D5 plus only the bilinear constraint 1_Sᵀ A_c^k 1_S = 1_Nᵀ A_c^k 1_N for
  k ≤ n − 3 (A_c = card matrix, N = N(v)). It drops t3's linear constraint and the top length
  k = n − 2. On the D2 branch, re-attaching v to S must keep both diameters ≤ 2. "Decided at v" =
  every surviving S is an image of N(v) under an automorphism of the card.
- Results: exhaustive n ≤ 8, every graph in either residual has a decided vertex (DE: 1, 7, 15, 26
  for n = 5..8; D2: 5 at n = 8). All 6 self-complementary members and all 4 SRG − v members are
  decided at every vertex.
- Ablation: triangles at v alone (k = 1) decide nothing on `GhEJ]o`. With k ≤ 2 (adding 4-cycles
  through v) everything is decided except `KbcrMZwA~c@r`, which needs longer walks.

Why it is Tutte-free (derivation): Jacobi's formula φ′(G) = Σ_v φ(G − v) gives φ(G) up to its
constant term δ. The resolvent entry ((tI − A)⁻¹)_vv = φ(G − v)/φ(G) changes only at order t^{−n−1}
when φ(G) becomes φ(G) + δ. So along σ, closed walks at v and σv of length ≤ n − 1 agree; the
first-return decomposition turns them into card walks between neighbours of v of length ≤ n − 3.
Tutte's determinant theorem is needed only for the top length.

## 1. Options

Each option: (1) idea; (2) sources; (3) bites on the residual?; (4) graph-specific ingredient (if
the method also works for tournaments or 3-uniform hypergraphs it cannot close the residual
alone); (5) Lean cost; (6) first lemma.

**O1. Walk matrix and controllability.**
(1) Along σ, walks from v agree (S4); rank W ≥ n − 1 ⇒ σ is an isomorphism (S5); at rank n − 2 a
second reconstruction is a balanced block switch (S6). (2) Godsil–McKay, JCTB 30 (1981) 285–289
[sec]; O'Rourke–Touri arXiv:1511.05080, almost all graphs controllable [abs]; Godsil, *Controllable
subsets in graphs*, Ann. Comb. 16 (2012) 733–744, doi:10.1007/s00026-012-0156-3, arXiv:1010.3231: a
controllable (X, S) has only the identity automorphism fixing S, and simple eigenvalues [abs];
Liu–Siemons arXiv:1911.00062 [abs]; Zhu–Yue arXiv:2609.36895 [read in the novelty note].
(3) **No, on the known face** (F1: rank W = 2). Rank W ≤ the number of cells of any equitable
partition (Rowlinson Thm 1.6), and impurity breeds symmetry; guess: the residual is mostly
low-rank. (4) Yes: symmetry of A (S4 fails for the n = 6 tournaments, t3 §7; no matrix for
hypergraphs). (5) S5core 150–300 lines now; S4 needs S2 (Tutte), 2000+ lines. (6) S5core (t3 §8):
cheap, but does not bite here.

**O2. Generalized spectrum (DGS).**
(1) (φ(G), φ(Ḡ)) is recognizable (Tutte for G and Ḡ), so **DGS ⇒ reconstructible** (one-line
derivation). (2) W. Wang, JCTB 122 (2017) 438–451, doi:10.1016/j.jctb.2016.07.004,
arXiv:1410.2164: 2^{−⌊n/2⌋} det W odd and square-free ⇒ DGS [abs]; Wang–Liu–Wang arXiv:2010.15888
(rank n − 1) [abs]; Qiu, LAA 2023, doi:10.1016/j.laa.2023.12.006 (a rank n − 2 family; statement
UNVERIFIED) [abs]; Z. Xiang arXiv:2610.11047 (Oct 2026), almost all graphs DGS [abs]. (3) No: the
criteria need det W ≠ 0 or corank ≤ 2; the known face has corank n − 2. (4) Yes, via Tutte.
(5) Very high: rational orthogonal matrices, Smith normal form (Mathlib has it for PIDs:
`LinearAlgebra/FreeModule/Int.lean`, `PID.lean`), Tutte. (6) The bridge `DGS → Reconstructible`,
about 50 lines once S2 exists. Low priority.

**O3. Main eigenvalues, main angles, walk generating function.**
(1) Rowlinson eq. (7) [read]: H_G(t) = t⁻¹[(−1)^n φ(Ḡ, −(t+1)/t)/φ(G, 1/t) − 1], so main
eigenvalues and main angles are recognizable given Tutte (derivation). G has ≤ 2 main eigenvalues
iff A²1 ∈ span{1, A1}, i.e. Σ_{w~v} deg w = a·deg v + b for all v; with exactly 2,
Var(deg) = (µ₁ − d̄)(d̄ − µ₂) (Prop 3.1). (2) Rowlinson, *The main eigenvalues of a graph: a
survey*, AADM 1 (2007) 445–471, doi:10.2298/AADM0702445R [read]; Cvetković 1970 (H_G formula) and
1978 (divisors) [sec]; Cvetković–Fowler 1999, #main eigenvalues ≤ #Aut-orbits [sec, Rowlinson
Prop 1.5]; Hagos, LAA 356 (2002) 103–111 [sec]. (3) **As a classifier, yes**: it splits off the
≤ 2-main face (all of F1's rank-2 members), where walk methods are void and all spectral
information sits in the non-main eigenspaces (angles, card-level data: O4). (4) The ≤ 2 test is
degree data, so universal; eq. (7) uses symmetry and Ḡ. (5) Cheap: 100–200 lines from the checked
neighbour-degree data. (6) `twoMainRecognizable` (elaborates): `open Classical in
Recon.Recognizable (fun n G => ∃ a b : ℤ, ∀ v : Fin n, (∑ w : Fin n, if G.Adj v w then
((G.neighborSet w).ncard : ℤ) else 0) = a * (G.neighborSet v).ncard + b)`. A splitting tool for a
reducer, not progress by itself.

**O4. One-card spectral / closed-walk test (Hong 1982; t3 S5′/U2s; Tutte-free truncation).**
1. F2: a one-card test (does some card admit only automorphic re-attachments?) using only
   φ(G − v) and φ′(G).
2. Hong, JCTB 32 (1982) 245–256 [sec, via Wang–Wen–Guo]. Wang–Wen–Guo arXiv:2408.02488 Thm 3
   [read in t3]. He arXiv:math/0607142 [read]. Godsil–Smith, *Strongly cospectral vertices*,
   arXiv:1709.07975, Australas. J. Combin. 88 (2024): φ(X∖v)/φ(X) = Σ_r (E_r)_vv/(t − θ_r) and the
   walk generating function at v [read, HTML extract]. The truncation is my derivation.
3. **Yes: the strongest evidence of any option** (F2: exhaustive n ≤ 8, both faces). But "every
   residual graph has a decided vertex" is open, t3's H**-type hypothesis. Neutral prior.
4. **No.** Jacobi's formula and the first-return decomposition hold for any square matrix, so a
   tournament analogue exists and it **cannot close the residual alone**. It gives a
   reconstructible *class* that a reducer splits off. Guess (untested): Stockmeyer's tournaments
   are undecided at every vertex in the analogue.
5. Jacobi derivative: 300–600 lines. Not in Mathlib; only `Matrix.derivative_det_one_add_X_smul`
   (trace at 0) exists. Resolvent expansion and first return: 300–500 lines
   (`RingTheory/PowerSeries/Inverse.lean`, `Matrix.adjugate`, `det_fromBlocks₁₁`). The class
   statement, D5-style: 300–450 lines.
6. `jacobiCharpoly` (elaborates; spot-checked numerically): `∀ (n : ℕ) (M : Matrix (Fin (n + 1))
   (Fin (n + 1)) ℤ), Polynomial.derivative M.charpoly = ∑ i : Fin (n + 1), (M.submatrix
   i.succAbove i.succAbove).charpoly`. Then `closedWalksTrunc`: t3's S3 with the hypothesis
   `k + 1 ≤ n` added (elaborates).

**O5. Tutte's determinant theorem itself (Tutte 1979; Kocay; He 2007).**
(1) det A is recognizable. He states and argues it for **all real symmetric matrices** with aligned
hypomorphic principal minors, via the lowest eigenvector of A + tJ and a comparison theorem for
volumes of solid angles. (2) H. He, *Reconstruction and higher dimensional geometry*,
arXiv:math/0511475, JCTB 97 (2007) (pages UNVERIFIED) [read §§1, 5], Thm 1:
det(B − λI + tJ) = det(A − λI + tJ); Tutte 1979 [sec]. (3) Only as infrastructure: the top length
in O4, and O1–O3, O9. (4) **Yes, symmetry is the whole ingredient** (fails for tournaments at n = 5,
`algebraic_methods.md` A11). Caveat: a symmetric-matrix-only argument also covers edge-weighted
graphs, where reconstruction is open, not refuted (`groups_and_harmonic.md` S12). (5) Very hard:
Kocay route S0–S2, 2000+ lines; He's route needs cone volumes (`MeasureTheory`, Rayleigh), guess:
worse. (6) t3's S0 (complementary induced pair count).

**O6. Two-deleted spectral identity, aimed at impurity.**
(1) Jacobi's 2×2 complementary minor: φ(G−a)φ(G−b) − φ(G)φ(G−a−b) = φ_ab(G)², with
φ_ab = adj(tI − A)_ab = Σ_{a–b paths P} φ(G − P), leading term [a ~ b]·t^{n−2}. An impure pair
(x, y), (x′, y′) has G−x−y ≅ G−x′−y′, deg x = deg x′, [xy] ≠ [x′y′]; so φ(G−x)φ(G−y) ≠
φ(G−x′)φ(G−y′) and the whole squared x–y walk series differs. Whether this rules out impurity is a
guess; at top order it only re-derives t4's bit law. (2) Godsil, *Algebraic Combinatorics* (1993),
Thm 4.1.2 (Jacobi), Cor. 2.2 (path sum) [sec, via Godsil–Smith]; the identity in this form is my
derivation, checked symbolically on random symmetric integer matrices. (3) Unknown; the only
algebraic tool found that speaks about the *(n − 2)-subgraph types* in which ¬PURE and ¬GLUE are
phrased. (4) Yes: needs adj_ab = adj_ba (for a digraph adj_ab·adj_ba is not a square).
(5) Desnanot–Jacobi is **not in Mathlib**: 200–400 lines from `Matrix.adjugate`,
`det_fromBlocks₁₁`. (6) `twoMinor` (elaborates): `∀ n (M : Matrix (Fin (n+2)) (Fin (n+2)) ℤ),
M.IsSymm → φ(M∖0)·φ(M∖1) − φ(M)·φ(M∖{0,1}) = (adjugate (charmatrix M) 0 1)^2`.

**O7. Pseudosimilar and cospectral vertices.**
(1) ¬PURE says every degree class has "2-pseudosimilar" pairs. Godsil–Kocay: every graph with a
pseudosimilar pair comes from the Herndon–Ellzey construction; Kocay explains pseudosimilarity by
subgroup cosets. A pair version might constrain the residual (guess). (2) Kimble–Schwenk–Stockmeyer,
JGT 5 (1981) 171–181 [sec]; Godsil–Kocay, *Constructing graphs with pairs of pseudo-similar
vertices*, JCTB (1982; vol. 32 pp. 146–155 UNVERIFIED) [sec]; Herndon–Ellzey 1975 (venue UNVERIFIED)
[sec]; Kocay, *Graphs, groups and pseudo-similar vertices*, J. Austral. Math. Soc. (1984) [abs];
Lauri, Ars Combin. 46 (1997) and Discrete Math. 267 (2003) 197–211 [citation]; Ivanov
arXiv:2609.00394 [abs]. (3) Possibly, structurally; Lauri 2003 (pseudosimilar *edges*) is nearest,
not read. (4) No: universal. (5) Definitions cheap; structure theorems hard. (6) None yet; read
Lauri 2003 first.

**O8–O12. Low-yield options (each: idea; sources; bite; graph-specific?; Lean).**
- **O8 Coherent configurations, WL, SRGs.** Regular graphs, including every SRG, are pure
  (e(G−x−y) = m − 2d + [xy]), so they are outside the residual; SRG − v is **inside** (F1). Idea
  (guess): an almost-regular G is a card of the regular G⁺ = G + a vertex joined to D_{r−1}, but
  G⁺ − w ≅ G does not give H ≅ G. Rowlinson §3 [read]. Universal (WL). Mathlib: `IsSRGWith`,
  `IsSRGWith.matrix_eq` (StronglyRegular.lean:206); no WL, no equitable partitions.
- **O9 Seidel switching.** charpoly(J − I − 2A) follows from φ(G) and H_G by a rank-one update, so
  it is recognizable given Tutte (derivation). Stanley 1985 [read, prior note]; Diaconis–Graham,
  Pacific J. Math. 118 (1985) [abs]. No route: switching does not preserve the deck, and the
  corank-2 obstruction is a rank-2 Δ, not a switch. Graph-specific.
  `det_add_replicateCol_mul_replicateRow` (SchurComplement.lean:426) exists.
- **O10 Polynomial reconstruction (PRP).** Is φ(G) determined by {φ(G − v)}? It is weaker than
  Tutte, since our cards are whole graphs. Sciriha–Stanić, Discrete Math. 346 (2023) 113349,
  doi:10.1016/j.disc.2023.113349 [abs]; Hagos, EJC 7 (2000) #R12 [sec]; Sciriha, LAA 356 (2002)
  [sec]; Spier arXiv:2503.17853 (φ mod 4) [abs]; Schwenk, *Selected Topics in Graph Theory* (1979)
  307–336 [sec]. Only use: det A mod 4, not enough for O4's top length. Off route.
- **O11 S_n representations, Radon transforms** (Nash-Williams, ACKR, Stanley, Diaconis):
  `groups_and_harmonic.md`. Universal, and the deck map has a large kernel: **cannot bite alone**.
- **O12 Chromatic symmetric function, Tutte polynomial, Hopf; Gröbner.** The Tutte polynomial is
  recognizable (Tutte 1979 [sec]). X_G = Σ_{S⊆E} (−1)^{|S|} p_{λ(S)} (Stanley 1995; formula from
  memory, UNVERIFIED) is recognizable by the same Kocay argument: disconnected spanning-subgraph
  counts from Kocay, connected ones by complement (my derivation; NOT FOUND in the literature).
  Hopf papers (arXiv:1511.05843, arXiv:1912.10645, Gonçalves thesis UFMG 2023 [abs]) reformulate
  Kelly. All universal: cannot bite. Gröbner/ideal approaches: none found.

## 2. Mathlib (pinned v4.36.0; paths under `lean/.lake/packages/mathlib/Mathlib/`)

**Present:** `SimpleGraph.adjMatrix`, `adjMatrix_pow_apply_eq_card_walk` (Combinatorics/SimpleGraph/
AdjMatrix.lean); `isHermitian_adjMatrix` (LapMatrix.lean:56); `Matrix.charpoly`, `charmatrix`,
`aeval_self_charpoly` (LinearAlgebra/Matrix/Charpoly/Basic.lean); `minpoly_dvd_charpoly`
(Charpoly/Minpoly.lean:43); `Matrix.IsHermitian.spectral_theorem`, `charpoly_eq`
(Analysis/Matrix/Spectrum.lean:143, 157); Rayleigh (Analysis/InnerProductSpace/Rayleigh.lean);
`Matrix.rank`, `rank_transpose_mul_self` (LinearAlgebra/Matrix/Rank.lean:553); `det_fromBlocks₁₁`
(SchurComplement.lean:368); `adjugate_fin_succ_eq_det_submatrix` (Adjugate.lean:366); power-series
inverse (RingTheory/PowerSeries/Inverse.lean).

**Gaps:** Jacobi derivative φ′ = Σ φ(M∖i); Desnanot–Jacobi; Sachs and Tutte; equitable partitions,
main eigenvalues, walk matrices; Seidel matrices; WL; chromatic and Tutte polynomials. The four
candidate bodies (`jacobiCharpoly`, `closedWalksTrunc`, `twoMainRecognizable`, `twoMinor`) elaborate
against `Recon.Basic` in a scratchpad file.

## 3. Ranked shortlist

1. **O4, Tutte-free one-card closed-walk class.** The only option with evidence on the residual
   (F2: exhaustive n ≤ 8, plus every known larger member). Moderate Lean cost, avoids Tutte, and the
   first lemma (`jacobiCharpoly`) is pure matrix algebra that can be upstreamed. It is not
   graph-specific: it can only split off a class (a reduction child). The remainder ("undecided
   at every vertex") is open; it is the analogue of t3's H** (guess: comparably hard).
2. **O3, two-main-eigenvalue split.** Cheap from the checked neighbour-degree data. It gives reducers
   and red teams a precise face (rank W = 2: the self-complementary members and SRG − v) where O1
   and O2 are void (Rowlinson). It also tells the strategist not to spend builder time on S4/S5 for
   this residual.
3. **O6, two-deleted spectral identity.** The one graph-specific (symmetry-using) algebraic
   statement in the language of ¬PURE and ¬GLUE (types of G − x − y). Speculative (a guess), but its
   first lemma fills a 200–400 line Mathlib gap. O5 (Tutte, 2000+ lines) remains the long-term
   graph-specific infrastructure behind everything.

Red-team targets: (i) a residual graph undecided at every vertex by O4; search near SRG − v
(n ≥ 15), Paley − v, and self-complementary graphs with n ≥ 20. (ii) Re-run F1 and F2 from this
description.
