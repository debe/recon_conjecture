# Mathlib map: algebraic and counting methods

This note maps Mathlib support for Kelly/Kocay counting, inclusion–exclusion and Möbius
inversion, adjacency matrices and characteristic polynomials, and edge reconstruction.
Companion literature note: `notes/literature/algebraic_methods.md`.

- Toolchain: Lean v4.36.0 and Mathlib v4.36.0, as pinned in `lean/`.
- Paths are relative to `lean/.lake/packages/mathlib/Mathlib/`.
- Every name below was found by grep in that tree on 2026-11-25. Line numbers are
  approximate anchors.
- The candidate Props C1–C11 elaborated without errors in a throwaway scratchpad file
  that imports `Mathlib` and `Recon.Basic`. That file is not a submission.

## 1. Counting and double counting

| Declaration | File:line | Use |
|---|---|---|
| `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` | `Combinatorics/Enumerative/DoubleCounting.lean:87` | Kelly double count (pairs (copy, missed vertex)) |
| `Finset.card_mul_eq_card_mul` | `Combinatorics/Enumerative/DoubleCounting.lean:184` | regular bipartite double count: each copy misses n − k vertices |
| `Finset.card_powersetCard` | `Data/Finset/Powerset.lean:211` | C(n, s) subsets of size s |
| `Finset.powerset_card_disjiUnion` | `Data/Finset/Powerset.lean:320` | split `∑ S : Finset` by `S.card` (C5 reduction) |
| `Finset.sum_powerset_neg_one_pow_card` (+ `_of_nonempty`) | `Data/Nat/Choose/Sum.lean:210,215` | Σ_S (−1)^{|S|} = [x = ∅] |
| `Finset.prod_add`, `Finset.prod_one_add` | `Algebra/BigOperators/Ring/Finset.lean:174,199` | expanding products into sums over subsets |
| `Fintype.card_fun` | `Data/Fintype/BigOperators.lean:202` | number of k-tuples of edges = m^k |
| `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` (Burnside) | `GroupTheory/GroupAction/Quotient.lean:267` | orbit counting over `Equiv.Perm (Fin n)` (Nash-Williams route) |

## 2. Inclusion–exclusion and Möbius inversion

| Declaration | File:line | Use |
|---|---|---|
| `Finset.inclusion_exclusion_sum_biUnion` | `Combinatorics/Enumerative/InclusionExclusion.lean:117` | general IE |
| `Finset.inclusion_exclusion_card_biUnion` | same, `:155` | card of a union |
| `Finset.inclusion_exclusion_sum_inf_compl` | same, `:166` | **the C4 form**: count of tuples avoiding none of the "uncovered" events |
| `Finset.inclusion_exclusion_card_inf_compl` | same, `:183` | card version of the above |
| `IncidenceAlgebra`, `IncidenceAlgebra.zeta`, `IncidenceAlgebra.mu` | `Combinatorics/Enumerative/IncidenceAlgebra.lean:333,372` | Möbius function of a locally finite order |
| `IncidenceAlgebra.moebius_inversion_top`, `moebius_inversion_bot` | same, `:540,576` | Möbius inversion (usable on `Finset α` ordered by ⊆) |
| `IncidenceAlgebra.mu_prod_mu` | same, `:650` | product posets (Boolean lattice = product of chains) |

Gap: there is no ready lemma for the Möbius function of the Boolean lattice
μ(A, B) = (−1)^{|B∖A|}. It follows from `mu_prod_mu` with chains, or it can be avoided by
using `inclusion_exclusion_*` directly. **Prefer the inclusion–exclusion lemmas.**

## 3. Subgraph counts

| Declaration | File:line | Use |
|---|---|---|
| `SimpleGraph.Copy` (`H.Copy G`, injective homs) | `Combinatorics/SimpleGraph/Copy.lean` (~:80) | not-necessarily-induced copies |
| `SimpleGraph.labelledCopyCount`, `copyCount` | `Copy.lean:506,527` | s(F, G), labelled and unlabelled; arguments are `G.labelledCopyCount H` = copies **of H in G** |
| `copyCount_le_labelledCopyCount`, `copyCount_eq_card_image_copyToSubgraph` | `Copy.lean:547,530` | relating the two counts |
| `SimpleGraph.IsIndContained` (`⊴`), `isIndContained_iff_exists_iso_induce` | `Copy.lean:408,465` | induced copies via `↪g` |
| `SimpleGraph.Embedding` (`↪g`) | `Combinatorics/SimpleGraph/Maps.lean` | induced copies: `Nat.card (F ↪g G)` |
| `SimpleGraph.Copy.induce` | `Copy.lean:159` | `G.induce s` as a copy inside G |
| `SimpleGraph.comap` DecidableRel instance | `Maps.lean:149` | `Recon.card G v = G.induce _` inherits `DecidableRel` (needed for `adjMatrix` of a card) |

## 4. Matchings, Hamiltonicity, trees

| Declaration | File:line | Note |
|---|---|---|
| `Subgraph.IsMatching`, `Subgraph.IsPerfectMatching` | `Combinatorics/SimpleGraph/Matching.lean:67,236` | C4/C5 use `Nat.card {M : G.Subgraph // M.IsPerfectMatching}` |
| `IsPerfectMatching.even_card` | `Matching.lean:265` | odd n ⇒ no perfect matching |
| `Walk.IsHamiltonian`, `Walk.IsHamiltonianCycle`, `SimpleGraph.IsHamiltonian` | `Combinatorics/SimpleGraph/Hamiltonian.lean:38,327` | the graph-level predicate exists; there is **no Hamiltonian-cycle count** |
| `SimpleGraph.IsTree`, `IsAcyclic` | `Combinatorics/SimpleGraph/Acyclic.lean:56,52` | there is **no spanning-tree count** and no matrix-tree theorem |
| `SimpleGraph.Tutte` file | `Combinatorics/SimpleGraph/Tutte.lean` | the Tutte 1-factor theorem, **not** the Tutte polynomial |

## 5. Adjacency matrix and characteristic polynomial

| Declaration | File:line | Use |
|---|---|---|
| `SimpleGraph.adjMatrix` | `Combinatorics/SimpleGraph/AdjMatrix.lean:236` | needs `[DecidableRel G.Adj]` |
| `SimpleGraph.Embedding.submatrix_adjMatrix` | `AdjMatrix.lean:288` | a card's adjacency matrix is a principal submatrix |
| `SimpleGraph.Iso.reindex_adjMatrix` | `AdjMatrix.lean:294` | iso ⇒ reindexed adjacency matrix (for C7) |
| `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` | `AdjMatrix.lean:401` | closed walks give trace powers, i.e. the spectral moments |
| `SimpleGraph.trace_adjMatrix` | `AdjMatrix.lean:379` | c₁ = 0 |
| `Matrix.charpoly`, `Matrix.charmatrix` | `LinearAlgebra/Matrix/Charpoly/Basic.lean:140,49` | |
| `Matrix.charpoly_reindex` | `Charpoly/Basic.lean:176` | iso invariance of the charpoly |
| `Matrix.derivative_det_one_add_X_smul` | `LinearAlgebra/Matrix/Charpoly/Coeff.lean:181` | derivative at 0 only (= trace); **not** the full Jacobi formula |
| `Matrix.charpolyRev` | `Charpoly/Coeff.lean:289` | reverse charpoly det(1 − X·M) |
| `Matrix.det_apply`, `det_apply'` | `LinearAlgebra/Matrix/Determinant/Basic.lean:65,69` | Leibniz expansion, the route to the Jacobi formula |
| `Matrix.det_updateRow_add`, `Matrix.det_succ_row` | `Determinant/Basic.lean:416,798` | multilinearity and Laplace expansion (alternative route) |
| `Polynomial.derivative_prod_finset` | `Algebra/Polynomial/Derivative.lean:639` | derivative of Π over i of (X·δ − a) |
| `SimpleGraph.lapMatrix`, `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` | `Combinatorics/SimpleGraph/LapMatrix.lean:79,282` | Laplacian and the number of components (no matrix-tree theorem) |
| `Matrix.rank`, `rank_le_card_width` | `LinearAlgebra/Matrix/Rank.lean:133,171` | for Oliveira–Thatte rank statements and Gottlieb |

**Jacobi gap (C6).** Mathlib has no lemma
`derivative (charpoly M) = ∑ i, charpoly (M.submatrix (·≠i) (·≠i))`. Suggested proof:
1. Write `charpoly M = det (charmatrix M)`.
2. Expand with `det_apply`. Each summand is Π over j of a linear-or-constant polynomial.
3. Apply `derivative_prod_finset` and swap the sums.
4. For a fixed i, the terms with σ i = i give `det` of the minor at i. The terms with
   σ i ≠ i vanish, because the entry (charmatrix M)_{σ i, i} is constant and its derivative
   is 0.
5. Reindex the minor along `{i}ᶜ ≃ Fin (n-1)`, or stay on the subtype, which is what
   `Recon.card` uses directly.
Expect 300–600 lines. This is an upstreamable lemma.

## 6. Edge deletion and group actions (edge program)

| Declaration | File:line | Use |
|---|---|---|
| `SimpleGraph.deleteEdges` | `Combinatorics/SimpleGraph/DeleteEdges.lean:43` | edge cards `G.deleteEdges {e}` |
| `SimpleGraph.edgeSet`, `edgeFinset`, `card_edgeFinset_le_card_choose_two` | `Combinatorics/SimpleGraph/Basic.lean`, `Finite.lean:144` | m ≤ C(n, 2) |
| `Equiv.Perm` acting on `Sym2` via `Sym2.map` | `Data/Sym/Sym2.lean` | Sₙ acting on the edge slots for Nash-Williams |

Gap: there is no edge-deck or edge-hypomorphism definition in `Recon.Basic`. Adding one
is a **human** change to `Basic.lean`. Until then, statements inline it as an `∃ σ :
G.edgeSet ≃ H.edgeSet, …` clause.

## 7. Hypergraphs and digraphs (for the failing-setting checks)

- `Combinatorics/Hypergraph/Basic.lean`: `Hypergraph α` (2026, Spotte-Smith–Mehta). Edges
  are `Set (Set α)` and there is no uniformity API yet.
- `Combinatorics/Digraph/Basic.lean`, `Digraph/Orientation.lean`: digraphs and
  orientations. There is no tournament-specific API.

None of these is needed for steps. They would only matter if someone wanted a
*formalized* failure witness (for example, the n = 5 tournament pair).

## 8. Gaps summary (nothing found by grep)

- chromatic polynomial (Mathlib has `chromaticNumber`, but no polynomial);
- Tutte (rank) polynomial;
- matching polynomial;
- the matrix-tree theorem / Kirchhoff;
- a spanning-tree count;
- a Hamiltonian-cycle count;
- Sachs' theorem (charpoly coefficients via elementary subgraphs);
- the Jacobi formula for the derivative of the charpoly;
- inclusion-matrix rank (Gottlieb–Kantor); Peck/Sperner quotient theory;
- an explicit Boolean-lattice Möbius function lemma;
- invariant rings of Sₙ on polynomial rings in the form Pouzet/Thiéry need.
