# Mathlib map: foundations of hypomorphism

Scope: Hypomorphic is symmetric and transitive; order is recognizable; each card has n − 1
vertices; hypomorphism is invariant under isomorphism on either side; small reusable facts
for later Kelly-lemma proofs.

Toolchain: Lean v4.36.0 and Mathlib v4.36.0 as pinned in `lean/`. Paths are relative to
`lean/.lake/packages/mathlib/Mathlib/`. Every name below was grepped in that tree, and the
routes marked **[probe-compiled]** were elaborated against `Recon.Basic` in a throwaway
file (outside the repo, not a submission, and not a result). The axioms were
`propext`/`Quot.sound` (+ `Classical.choice` for the edge-count lemma).

## 0. Repo definitions (`lean/Recon/Basic.lean`, trusted)

- `Recon.card G x : SimpleGraph ({x}ᶜ : Set V) := G.induce {x}ᶜ` (an `abbrev`, so it
  unfolds to `SimpleGraph.induce`).
- `Recon.Hypomorphic G H := ∃ σ : V ≃ W, ∀ x, Nonempty (card G x ≃g card H (σ x))`. This
  is heterogeneous: `G` and `H` may live on different vertex types.
- `anchor_hypomorphic_refl` (reflexivity) is already proved.
- Checked: `Recon.Checked.L_found_iso_hypomorphic` (`lean/Recon/Checked/L_found_iso_hypomorphic.lean`).
  Its helper `Recon.Checked.L_found_iso_hypomorphic.cardIso` (`f : G ≃g H` on `Fin n`
  gives `card G x ≃g card H (f x)`) can be imported by later proofs. It is stated only for
  `Fin n`. The general version below is a one-liner via `Iso.induce`.

## 1. Isomorphisms (`Combinatorics/SimpleGraph/Maps.lean`)

| Declaration | Line | Use |
|---|---|---|
| `SimpleGraph.Iso` (`abbrev`, `RelIso G.Adj G'.Adj`, notation `≃g`) | 410 | the type of card isomorphisms |
| `Iso.refl`, `Iso.symm` (abbrevs) | 732, 744 | reflexivity and symmetry of card isos |
| `RelIso.trans` (used as `e.trans e'`), `Iso.comp` | 847 | transitivity |
| `Iso.map_adj_iff` | 747 | adjacency transport |
| `Iso.mapEdgeSet`, `Iso.mapNeighborSet` | 774, 790 | equivalences of edge and neighbour sets |
| `Iso.card_eq : Fintype.card V = Fintype.card W` | 799 | an iso preserves the order |
| **`Iso.induce (φ : G ≃g G') (φst : Set.BijOn φ s t) : G.induce s ≃g G'.induce t`** | 870 | **the key tool**: restricting an iso to the cards |
| `Iso.coe_induce`, `Iso.induce_refl`, `Iso.induce_comp_induce` | 878–888 | simp lemmas for it |
| `induce` (`abbrev`), `induce_adj` (`.rfl`), `comap_adj` (simp) | 312, 316, 136 | unfolding cards |
| `Iso.comap`, `Iso.map` (from `V ≃ W`) | 807, 821 | relabelling a graph along an equiv |
| `induceUnivIso`, `induceHom`, `induceHomOfLE` | 907, 686, 714 | other induce maps |
| `overFin`, `overFinIso` | 926, 930 | move any finite graph to `Fin n` |

## 2. Set/Equiv glue (BijOn for complements of singletons)

- `Equiv.bijOn (h : ∀ a, e a ∈ t ↔ a ∈ s) : BijOn e s t` is in `Data/Set/Function.lean:1342`.
  With `s = {x}ᶜ`, `t = {f x}ᶜ` the side condition is closed by `simp`, which uses
  injectivity. **[probe-compiled]**
- Alternatives: `Set.BijOn.compl` (`Data/Set/Function.lean:747`), `Set.bijOn_id` (:682),
  `Equiv.bijOn_image` (:1348), `Equiv.image_compl` (`Logic/Equiv/Set.lean:111`).
- `Equiv.subtypeEquiv` is the route used in the checked `cardIso`.
- `Equiv.apply_symm_apply`, `Equiv.symm_apply_apply` and `Equiv.trans` live in core Mathlib
  `Logic/Equiv/Defs.lean`.

## 3. Counting vertices of a card

- `Fintype.card_compl_set [Fintype α] (s) : Fintype.card ↥sᶜ = Fintype.card α - Fintype.card s`
  is in `Data/Fintype/Card.lean:155`.
- `Set.card_singleton (a) : Fintype.card ({a} : Set α) = 1` (simp, rfl) is in
  `Data/Set/Finite/Basic.lean:802`.
- `Set.card_ne_eq (a) : Fintype.card {x | x ≠ a} = Fintype.card α - 1` is at
  `Data/Set/Finite/Basic.lean:826`.
- `Fintype.card_subtype_compl` is at `Data/Fintype/Card.lean:400`.
- `Fintype.card_fin` and `Fintype.card_congr` (`Data/Fintype/Card.lean`, `Data/Fintype/EquivFin.lean`).
- Each card has n − 1 vertices: `rw [Fintype.card_compl_set, Set.card_singleton, Fintype.card_fin]`
  proves `Fintype.card ({x}ᶜ : Set (Fin n)) = n - 1`. **[probe-compiled]**
- Order is recognizable (`Hypomorphic G H → n = m` for `Fin n`, `Fin m`):
  `simpa using Fintype.card_congr σ`. **[probe-compiled]** It is trivial because σ is part of
  the definition. With the `Fin n`-only `Recognizable`, order is built into the type.

## 4. Edge counts and degrees (for the next layer, edge count / degree sequence)

| Declaration | File:line |
|---|---|
| `card_edgeFinset_induce_compl_singleton : #(G.induce {x}ᶜ).edgeFinset = #(G.deleteIncidenceSet x).edgeFinset` | `Combinatorics/SimpleGraph/DeleteEdges.lean:160` |
| `card_edgeFinset_deleteIncidenceSet : #(G.deleteIncidenceSet x).edgeFinset = #G.edgeFinset - G.degree x` | `DeleteEdges.lean:181` |
| `edgeFinset_deleteIncidenceSet_eq_sdiff` | `DeleteEdges.lean:173` |
| `Iso.card_edgeFinset_eq (f : G ≃g G') : #G.edgeFinset = #G'.edgeFinset` | `Combinatorics/SimpleGraph/Finite.lean:647` |
| `Iso.degree_eq (f) (x) : G'.degree (f x) = G.degree x` (simp) | `Finite.lean:652` |
| `Iso.minDegree_eq`, `Iso.maxDegree_eq` | `Finite.lean:659+` |
| `card_neighborFinset_eq_degree`, `card_neighborSet_eq_degree`, `card_incidenceFinset_eq_degree` | `Finite.lean:244, 246, 350` |
| `sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * #G.edgeFinset` | `Combinatorics/SimpleGraph/DegreeSum.lean:101` |
| `card_edgeFinset_le_card_choose_two` | `Finite.lean:144` |
| `degree_induce_of_neighborSet_subset`, `card_edgeFinset_induce_of_support_subset` | `Finite.lean:716, 696` |

- `#(card G x).edgeFinset = #G.edgeFinset - G.degree x` is the composition of the two
  `DeleteEdges` lemmas: `rw [card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]`.
  **[probe-compiled]**
- The edge-count identity Σₓ|E(G−x)| = (n−2)|E| then follows from `Finset.sum_tsub_distrib`
  (or by working with `+`, since `G.degree x ≤ #G.edgeFinset`), together with the handshake
  lemma.
- Recognizing the edge count needs `Iso.card_edgeFinset_eq` on each card, then
  `Equiv.sum_comp σ` (additive form of `Equiv.prod_comp`, `Algebra/BigOperators/Group/Finset/Defs.lean:743`) to reindex the sum.

## 5. Connectivity / acyclicity under iso (later programs)

- `Iso.reachable_iff` is at `Combinatorics/SimpleGraph/Connectivity/Connected.lean:139`.
- `Iso.preconnected_iff` is at :265.
- `Iso.connected_iff` is at :364.
- `Iso.isAcyclic_iff` and `Iso.isTree_iff` are at `Combinatorics/SimpleGraph/Acyclic.lean:82, 86`.
- `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial` is at
  `Acyclic.lean:555`. It says that a connected finite graph has a connected card, which
  makes it relevant to "connected iff ≥ 2 connected cards".

## 6. Subgraph counts (Kelly's lemma, `Combinatorics/SimpleGraph/Copy.lean`)

- `structure Copy H G` (:83).
- `Iso.toCopy` (:95).
- `Copy.comp` (:135).
- `Copy.induce` (:159).
- `IsContained` (`⊑`, :238).
- `isContained_congr` (:270).
- `IsIndContained` (`⊴`, :408).
- `isIndContained_iff_exists_iso_induce` (:465).
- `labelledCopyCount G H := Fintype.card (Copy H G)` (:506).
- `copyCount G H := #{G' : G.Subgraph | Nonempty (H ≃g G'.coe)}` (:527).
- `copyCount_eq_card_image_copyToSubgraph` (:530).
- Double counting: `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` and
  `Finset.card_mul_eq_card_mul` (`Combinatorics/Enumerative/DoubleCounting.lean:87, 184`).

## 7. Probe-compiled routes for the target statements

- **Symmetry.** Take `σ.symm`. For `y`, take `e := hσ (σ.symm y) : card G (σ.symm y) ≃g card H (σ (σ.symm y))`.
  Compose it with `cardCongr H (σ.apply_symm_apply y)`, where
  `cardCongr G (h : x = y) := Iso.refl.induce ((Equiv.refl V).bijOn (by simp [h]))`, and
  take `.symm`. The only friction is the dependent type `card H (σ (σ.symm y))` versus
  `card H y`. It is handled by `cardCongr` (or `subst`); no `cast` is needed.
- **Transitivity.** `⟨σ.trans τ, fun x => ⟨(hσ x).some.trans (hτ (σ x)).some⟩⟩` typechecks
  definitionally, because `(σ.trans τ) x ≡ τ (σ x)`.
- **Invariance under iso on either side.** Use the general
  `cardIso f x := f.induce (f.toEquiv.bijOn (fun a => by simp))`. The iso gives a
  hypomorphism; compose with symmetry and transitivity. For the right side, use `trans h`
  with the iso-hypomorphism.
- **Each card has n − 1 vertices** and **order**: see §3.
- **Card edge count**: see §4.

## 8. Gaps (nothing in Mathlib; must be built in the checked library)

1. **No reconstruction notions at all.** There is no `deck`, `hypomorphic` or vertex-deleted
   subgraph API (grep for `vertexDeleted`, `deck` and `hypomorph` finds nothing). Mathlib
   has only `induce {x}ᶜ` and `deleteIncidenceSet` (which keeps the vertex type).
2. **No `Iso` congruence along vertex equality.** There is no `induce`-level
   `Iso.ofEq`/`setCongr` for `s = t`; build it via `Iso.refl.induce`, as in §7, or
   `Equiv.setCongr`/`Equiv.Set.ofEq`.
3. **No iso-invariance of copy counts.** No `labelledCopyCount_congr` or `copyCount_congr`
   (grep finds none) states that `G ≃g G'` gives `G.copyCount H = G'.copyCount H`. Kelly's
   lemma needs this for cards; it is derivable from `Copy.comp` with `Iso.toCopy` as an
   `Equiv` of `Copy` types (easy, around 20 lines).
4. **No Kelly lemma.** Nothing relates copies in `G` to copies in `G.induce {x}ᶜ`.
   Double-counting pairs (copy, vertex outside its image) needs
   `DoubleCounting` + `Copy.induce`/`Copy.comp` plus a bijection between copies of `H` in
   `G` that avoid `x` and copies in `card G x`. This is the main new work for the `kelly`
   program (medium: about 150–300 lines).
5. **Fintype instances on `↥({x}ᶜ : Set (Fin n))`** resolve automatically (via decidable
   membership). Statements that mention `edgeFinset` of a card need
   `[DecidableRel (card G x).Adj]`. This is inferred from `[DecidableRel G.Adj]` via
   `induce`/`comap`, but statements over arbitrary `G : SimpleGraph (Fin n)` should use
   `classical` or `Finset.card (Set.toFinset ...)` / `Nat.card G.edgeSet` to avoid
   instance mismatch between the statement and the proof. Prefer `Nat.card (card G x).edgeSet`
   or `G.edgeSet.ncard` in frozen statements, because they need no instance arguments.

## 9. Formalization difficulty estimates

| Statement | Estimate |
|---|---|
| Hypomorphic symmetric | easy (about 10 lines, probe-compiled) |
| Hypomorphic transitive | trivial (one line, probe-compiled) |
| iso ⇒ hypomorphic (general types) | trivial via `Iso.induce` (checked already on `Fin n`) |
| hypomorphism invariant under iso, left/right | easy (compose the above) |
| each card has n − 1 vertices | trivial (probe-compiled) |
| order recognizable (n = m) | trivial (probe-compiled) |
| `\|E(G − x)\| = \|E\| − deg x` | trivial (two Mathlib lemmas, probe-compiled) |
| edge count recognizable (n ≥ 3) | easy–medium (sum reindex, handshake, divide by n − 2) |
| degree sequence recognizable | easy given edge count |
| Kelly's lemma | medium (gap 4) |
