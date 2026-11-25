# Mathlib map: homomorphism counts, copy counts, and the deck

This map serves `notes/literature/hom_counts_and_logic.md` (candidates A to F). The toolchain
is Lean v4.36.0 with Mathlib as pinned in `lean/`. Paths are relative to
`lean/.lake/packages/mathlib/Mathlib/`, and every name below was grepped in that tree on
2026-11-25. The candidate Props elaborated in a throwaway file against `Recon.Basic`. That
probe is not a result.

## Homomorphisms and their finiteness (`Combinatorics/SimpleGraph/Maps.lean`)

| Declaration | Line | Note |
|---|---|---|
| `instance [Finite V] [Finite W] : Finite (G →g H)` | 439 | This is **only `Finite`; there is no `Fintype` instance**. Use `Nat.card (F →g G)` in statements, or build a local `Fintype.ofInjective (⇑) DFunLike.coe_injective` inside proofs. |
| `SimpleGraph.map (f : V → W) G`, with `Adj := Ne ⊓ Relation.Map G.Adj f f` | 57 | Use it for quotients F/P: map along `Quotient.mk`. Loops are dropped automatically, so the "no edge inside a block" condition must be tracked separately. |
| `map_adj'` | 66 | the iff form of `map`'s adjacency |
| `Iso.induce` | 869 | restricts an iso to the cards; already used by `found_iso_hypomorphic` |
| `Hom.comp`, `Iso.toHom`, `RelIso` coercions | — | post-composition with a card iso transports homs |

## Copies (`Combinatorics/SimpleGraph/Copy.lean`)

| Declaration | Line | Note |
|---|---|---|
| `structure Copy (H) (G)` | 83 | an injective hom; `Copy H G` is a copy of H in G |
| `Hom.toCopy`, `Embedding.toCopy`, `Iso.toCopy` | 89–95 | |
| `Copy.comp` | 135 | transport along card isos |
| `Copy.induce G s : Copy (G.induce s) G` | 159 | the card as a copy |
| `IsContained` (`⊑`), `IsIndContained` (`⊴`) | 238, 408 | |
| `isIndContained_iff_exists_iso_induce` | 465 | the induced-copy ↔ induce-iso bridge |
| `labelledCopyCount G H := Fintype.card (Copy H G)` (classical, noncomputable) | 506 | this is inj(H,G); note the argument order is host first |
| `labelledCopyCount_eq_zero`, `labelledCopyCount_pos` | 514, 517 | |
| `copyCount G H` (unlabelled subgraphs iso to H) | 527 | |
| `copyCount_le_labelledCopyCount` | 547 | |

**Gaps.**
- There is no induced-copy count, so the "ind(F,G)" of the literature note has to be defined
  inline, e.g. `#{s : Finset V | s.card = k ∧ Nonempty (F ≃g G.induce s)}`.
- There is no hom count (`homCount`), no Kelly lemma, and no relation between
  `labelledCopyCount` and `copyCount` via `|Aut|`.
- Mathlib's own TODO (line 58) is to make the counts computable.

## Disjoint union (`Combinatorics/SimpleGraph/Sum.lean`), for candidate D

| Declaration | Line |
|---|---|
| `SimpleGraph.sum G H : SimpleGraph (V ⊕ W)`, notation `⊕g` (infixl 60) | 34, 44 |
| `sum_adj_inl`, `sum_adj_inr`, `not_adj_sum_inl_inr` | 48, 51, 166 |
| `Iso.sumCongr`, `Iso.sumComm`, `Iso.sumAssoc` | 129, 65, 70 |
| `Embedding.sumInl`, `Embedding.sumInr` | 77, 85 |
| `not_connected_sum` | 181 |

The gap here is a lemma of the form "card of `G ⊕g ⊥` at `inr ()` ≅ G". It can be built from
`Iso.induce` together with `Equiv` on `{inr ()}ᶜ ≃ V`.

## Products

Only `boxProd` (`Combinatorics/SimpleGraph/Prod.lean:45`, the Cartesian product) exists.
There is **no categorical/tensor product** of simple graphs. Example 3.8(iii) of the
literature note (⊗K) would need a local definition, which is not allowed in proof files as a
`structure`; a plain `def` of a `SimpleGraph` is fine.

## Counting glue

| Declaration | File:line |
|---|---|
| `Fintype.card_sigma` (simp) | `Data/Fintype/BigOperators.lean:163` |
| `Finset.card_eq_sum_card_fiberwise` | `Algebra/BigOperators/Group/Finset/Basic.lean:1017` |
| `Finset.card_compl : #sᶜ = card α - #s` | `Data/Fintype/Card.lean:134` |
| `Fintype.card_congr` | `Data/Fintype/Card.lean:66` |
| `Nat.card_eq_fintype_card` | `SetTheory/Cardinal/Finite.lean:47` |
| `inclusion_exclusion_sum_biUnion`, `inclusion_exclusion_card_biUnion`, `..._inf_compl` | `Combinatorics/Enumerative/InclusionExclusion.lean:117, 155, 166, 183` |
| `IncidenceAlgebra.mu`, `mu_mul_zeta`, `moebius_inversion_top`, `moebius_inversion_bot` | `Combinatorics/Enumerative/IncidenceAlgebra.lean:372, 470, 540, 576` |
| `Finpartition`, its `Fintype` instance, and its `PartialOrder` | `Order/Partition/Finpartition.lean:85, 258/311, 272` |

**Gap.** There is no closed form for the partition-lattice Möbius function, and no
hom ↔ inj ↔ ind basis change. For candidate A we avoid both: the stratified double count
needs only `Fintype.card_sigma`, fibre counting, and `Finset.card_compl`.

## Edge count and degree (needed by candidates D and E)

These are as in `notes/mathlib/foundations-…md` §4:
- `card_edgeFinset_induce_compl_singleton` (`Combinatorics/SimpleGraph/DeleteEdges.lean:160`);
- `card_edgeFinset_deleteIncidenceSet` (`DeleteEdges.lean:181`);
- `Iso.card_edgeFinset_eq` and `Iso.degree_eq` (`Combinatorics/SimpleGraph/Finite.lean`);
- `sum_degrees_eq_twice_card_edges` (`Combinatorics/SimpleGraph/DegreeSum.lean:101`).

## Walks and spectra (candidate F)

- `adjMatrix_pow_apply_eq_card_walk` is in `Combinatorics/SimpleGraph/AdjMatrix.lean:401`.
- `finsetWalkLength` and `card_set_walk_length_eq` are in
  `Combinatorics/SimpleGraph/Walk/Counting.lean:89, 150`.
- `Matrix.charpoly` and `Matrix.trace` are in the general linear algebra files.

The gap is that nothing relates the characteristic polynomial of a card to principal minors.
The external repo mentioned in the literature note has this (unaudited, no licence: do not
copy).

## Absent entirely

These are absent: Weisfeiler–Leman / colour refinement, counting logics C^k, treewidth / tree
depth, game comonads, and homomorphism indistinguishability. Any step touching them is a
large infrastructure project. Prefer candidates A to E.
