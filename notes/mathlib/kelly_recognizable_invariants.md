# Mathlib map: Kelly's lemma and invariants recognizable from the deck

Program: `kelly`. Toolchain: Lean v4.36.0 and Mathlib v4.36.0 (pinned in `lean/`).
All paths are relative to `lean/.lake/packages/mathlib/Mathlib/`.

I compiled every name below with `#check` in the scratch files
`lean/Recon/Scratch/librarian_kelly/probe.lean` and `probe2.lean`. Both are gitignored drafts,
not results.

Reminder: `Recon.card G x` is `G.induce ({x}ᶜ : Set V)`, an `abbrev`. So every Mathlib lemma
about `G.induce {x}ᶜ` applies to it directly.

## 0. Elaboration facts (tested in probe.lean)

- `Fintype ({x}ᶜ : Set (Fin n))` is found by instance search. So `Finset.univ`, `∑ v`,
  `labelledCopyCount` and `copyCount` all work on cards with no extra instances.
- **Statement bodies are not allowed to say `open`.** `desk.py` rejects the words `open`,
  `instance` and `end`, and it rejects `#`. A `DecidableRel G.Adj` for an arbitrary
  `G : SimpleGraph (Fin n)` is therefore not available inside a statement. The `Finset`
  API (`G.edgeFinset`, `G.degree`) needs that instance.
  **Recommendation:** phrase statements with `Set.ncard`, which needs no instances:
  - `G.edgeSet.ncard`
  - `(G.neighborSet v).ncard`
  - `{v | P v}.ncard`

  Proofs then bridge to the Finset API with `classical`, plus:
  - `Set.ncard_eq_toFinset_card'` (`Data/Set/Card.lean:669`): `s.ncard = s.toFinset.card` given `[Fintype s]`.
    Note that `G.edgeFinset` *is* `G.edgeSet.toFinset`.
  - `Set.ncard_coe_finset` (`Data/Set/Card.lean:704`), and `SimpleGraph.coe_edgeFinset` (`Combinatorics/SimpleGraph/Finite.lean:62`).
  - `SimpleGraph.card_neighborSet_eq_degree` (`Combinatorics/SimpleGraph/Finite.lean:246`): `Fintype.card (G.neighborSet v) = G.degree v`.
  - `SimpleGraph.edgeFinset_card` / `card_edgeSet` (`Finite.lean:123,126`).
  - `Nat.card_eq_fintype_card` (`SetTheory/Cardinal/Finite.lean:47`) and `Set.ncard_univ` (`Data/Set/Card.lean:707`).
- These candidate Props elaborate as `def … : Prop` with only `import Mathlib` and
  `import Recon.Basic` (probe.lean, all green):
  - `∀ n (G : SimpleGraph (Fin n)), ∑ v : Fin n, (Recon.card G v).edgeSet.ncard = (n - 2) * G.edgeSet.ncard`
  - `∀ n (G : SimpleGraph (Fin n)) v, (Recon.card G v).edgeSet.ncard + (G.neighborSet v).ncard = G.edgeSet.ncard`
  - `∀ n, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H → G.edgeSet.ncard = H.edgeSet.ncard`
  - `∀ n, 3 ≤ n → ∀ G H (σ : Fin n ≃ Fin n), (∀ x, Nonempty (Recon.card G x ≃g Recon.card H (σ x))) → ∀ v, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard`
  - `Recon.Recognizable (fun _ G => G.Connected)`
  - `∀ n, 3 ≤ n → ∀ G : SimpleGraph (Fin n), G.Connected ↔ 2 ≤ {v : Fin n | (Recon.card G v).Connected}.ncard`
  - `∀ n k (G : SimpleGraph (Fin n)) (F : SimpleGraph (Fin k)), ∑ v : Fin n, (Recon.card G v).labelledCopyCount F = (n - k) * G.labelledCopyCount F`
  - the same with `copyCount` (unlabelled copies)
  - `∀ n k, k < n → ∀ G H (F : SimpleGraph (Fin k)), Recon.Hypomorphic G H → G.copyCount F = H.copyCount F`

  Truncated `ℕ` subtraction is harmless in the sum identities:
  - for n ≤ 2 both sides of the edge identity are 0;
  - for k ≥ n the card side of Kelly's identity is 0, because a card has n − 1 < k vertices.

## 1. Edge count and degree of a card (essentially present)

| Declaration | File:line | Statement |
|---|---|---|
| `SimpleGraph.card_edgeFinset_induce_compl_singleton` | `Combinatorics/SimpleGraph/DeleteEdges.lean:160` | `#(G.induce {x}ᶜ).edgeFinset = #(G.deleteIncidenceSet x).edgeFinset` (`[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`) |
| `SimpleGraph.card_edgeFinset_deleteIncidenceSet` | `DeleteEdges.lean:181` | `#(G.deleteIncidenceSet x).edgeFinset = #G.edgeFinset - G.degree x` |
| `SimpleGraph.edgeFinset_deleteIncidenceSet_eq_filter` | `DeleteEdges.lean:188` | the edges of `G - x` are `{e ∈ G.edgeFinset \| x ∉ e}` |
| `SimpleGraph.induce_deleteIncidenceSet_of_notMem` | `DeleteEdges.lean:146` | `(G.deleteIncidenceSet x).induce s = G.induce s` when `x ∉ s` |
| `SimpleGraph.degree_le_card_edgeFinset` | `Finite.lean:359` | `G.degree v ≤ #G.edgeFinset` (so the subtraction above is exact) |
| `SimpleGraph.sum_degrees_eq_twice_card_edges` | `DegreeSum.lean:101` | `∑ v, G.degree v = 2 * #G.edgeFinset` (handshake) |
| `SimpleGraph.card_filter_edgeFinset_toFinset_subset` | `Finite.lean:749` | `#{e ∈ G.edgeFinset \| e.toFinset ⊆ s} = #(G.induce ↑s).edgeFinset` |
| `SimpleGraph.map_edgeFinset_induce` | `Finite.lean:684` | the edges of `G.induce s`, mapped by `sym2Map`, equal `G.edgeFinset ∩ s.toFinset.sym2` |
| `SimpleGraph.edgeSet_induce` | `Combinatorics/SimpleGraph/Maps.lean:331` | `(G.induce s).edgeSet = Sym2.map (↑) ⁻¹' G.edgeSet` |
| `SimpleGraph.Iso.card_edgeFinset_eq` | `Finite.lean:647` | `G ≃g G' → #G.edgeFinset = #G'.edgeFinset` |
| `SimpleGraph.Iso.mapEdgeSet` | `Maps.lean:774` | `G ≃g G' → G.edgeSet ≃ G'.edgeSet` (use it with `Set.ncard_congr'` for the `ncard` form) |
| `SimpleGraph.Iso.degree_eq` (simp) | `Finite.lean:652` | `G'.degree (f x) = G.degree x` |
| `SimpleGraph.Iso.mapNeighborSet` | `Maps.lean:790` | `G.neighborSet v ≃ G'.neighborSet (f v)` |
| `SimpleGraph.degree_induce_of_neighborSet_subset` | `Finite.lean:716` | the degree in `G.induce s` equals `G.degree v` when `N(v) ⊆ s` |
| `SimpleGraph.Iso.minDegree_eq` / `maxDegree_eq` | `Finite.lean:660,665` | |

**Route for the edge count.**
1. Card edges plus degree: rewrite with `card_edgeFinset_induce_compl_singleton`, then
   `card_edgeFinset_deleteIncidenceSet` and `degree_le_card_edgeFinset`. probe.lean checks
   the first two rewrites as an `example`.
2. Sum over v: `Finset.sum_add_distrib`, `Finset.sum_const`, `Finset.card_univ` and
   `Fintype.card_fin`, then `sum_degrees_eq_twice_card_edges`. This gives
   `Σ|E(G−v)| + 2|E| = n|E|`, so `Σ|E(G−v)| = (n−2)|E|`.
3. Recognizability: σ pairs the cards, and `Iso.card_edgeFinset_eq` gives equal sums. Cancel
   by `n − 2 > 0`, using `Nat.eq_of_mul_eq_mul_left`.

Difficulty: **easy**, about 40–80 lines. The only friction is instances (`classical`, and
`Fintype` on `{x}ᶜ`).

**Route for the degree sequence.** Use `deg v = |E| − |E(G−v)|`:
- `|E(G)| = |E(H)|` from the edge count;
- `|E(G−v)| = |E(H−σv)|` from the card isomorphism.

So the hypomorphism σ itself matches the degrees, which is a stronger statement than "the
multisets agree". Difficulty: **easy** once the edge count is checked. Make it a child or a
second step that reuses the edge-count step.

## 2. Kelly's lemma (counting copies), partly present

Copies, in `Combinatorics/SimpleGraph/Copy.lean`:

| Declaration | Line | Notes |
|---|---|---|
| `SimpleGraph.Copy H G` (structure: injective hom) | 83 | `FunLike`; `Copy.injective` 104, `Copy.toEmbedding` 127 |
| `Copy.comp` | 135 | composition |
| `Copy.induce G s : Copy (G.induce s) G` | 159 | the inclusion of a card into G |
| `Iso.toCopy`, `Embedding.toCopy`, `Hom.toCopy` | 89–95 | |
| `Copy.toSubgraph`, `Copy.isoToSubgraph`, `Copy.range_toSubgraph` | 174, 177, 180 | |
| `instance Fintype (G.Copy H)` | 196 | needs `Fintype {f : G →g H // Injective f}`; it resolves for `Fin` types |
| `IsContained` (`⊑`), `isContained_congr` | 238, 270 | Prop-level isomorphism invariance |
| `IsIndContained` (`⊴`), `isIndContained_iff_exists_iso_induce` | 408, 465 | induced containment, Prop only |
| `labelledCopyCount G H := Fintype.card (Copy H G)` (classical, noncomputable) | 506 | `_of_isEmpty` = 1, `_eq_zero ↔ H.Free G`, `_pos` |
| `copyCount G H := #{G' : G.Subgraph \| Nonempty (H ≃g G'.coe)}` | 527 | unlabelled copies, i.e. Kelly's s(H, G). Has `copyCount_eq_card_image_copyToSubgraph` 530, `copyCount_le_labelledCopyCount` 547, `copyCount_bot` 550, `copyCount_of_isEmpty` 566 |

Double counting (`Algebra/BigOperators/...` and `Combinatorics/DoubleCounting.lean`):
- `Finset.sum_comm`;
- `Finset.card_eq_sum_ones`;
- `Finset.sum_boole`;
- `Finset.sum_const`;
- `Finset.card_compl`;
- `Fintype.card_subtype_compl`;
- `Fintype.card_range` (the range of an embedding-like map has card `Fintype.card α`);
- `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`;
- `Fintype.card_congr`;
- `Equiv.subtypeEquiv`;
- `Set.ncard_congr'` (`Data/Set/Card.lean:947`);
- `Set.ncard_compl` (`Data/Set/Card.lean:1207`).

**Gaps** (nothing in Mathlib; grep found no `copyCount_congr`, no `Copy` equivalences and no
induced-copy count):
1. **Isomorphism invariance of the counts:**
   - `G ≃g G' → labelledCopyCount G F = labelledCopyCount G' F`, via `Copy F G ≃ Copy F G'`
     with `e.toCopy.comp`;
   - the same for `copyCount`, via `Subgraph.map` along the isomorphism;
   - invariance in F as well.

   Easy: about 30 lines each.
2. **Copies avoiding v, labelled:** `Copy F (G.induce {v}ᶜ) ≃ {f : Copy F G // v ∉ Set.range f}`.
   - Forward direction: `(Copy.induce G _).comp`.
   - Backward direction: restrict the codomain. Mathlib has no `Hom.codRestrict` into
     `induce`. Write it by hand as `⟨fun w => ⟨f w, _⟩, _⟩` with `induce_adj` (`Maps.lean:316`).

   Medium-easy: about 40 lines.
3. **Copies avoiding v, unlabelled:** a bijection between `(G.induce {v}ᶜ).Subgraph` and the
   subgraphs of `G` whose `verts` avoid `v`, preserving `≃g` of `.coe`. Tools: `Subgraph.map` and
   `Subgraph.comap` along `Embedding.induce` (`Combinatorics/SimpleGraph/Subgraph.lean`), and
   `Embedding.isoInduceRange` (`Maps.lean:602`). **Medium**: about 80–150 lines, mostly
   Subgraph ext lemmas.
4. **Double count:** `Σ_v #{f | v ∉ range f} = Σ_f #(range f)ᶜ = (n − k)·#Copy`. Use
   `Finset.sum_comm` and `Fintype.card_range`. Easy.

**Recommendation.** Prove the **labelled** Kelly lemma first: it needs gaps 1, 2 and 4, and
avoids Subgraph bookkeeping. The unlabelled form follows if `labelledCopyCount = |Aut F| ·
copyCount`, but that identity is **also missing** (orbit counting; medium). Either the
labelled or the unlabelled count is enough for recognizability of `⊑`-counts. Kelly's lemma
for *induced* copies has no Mathlib counting function at all: you would define it inline as
`Fintype.card (F ↪g G)`, using `Embedding`, which has a Fintype instance via
`RelEmbedding`. UNVERIFIED: I did not test that instance.

## 3. Connectivity

| Declaration | File:line | Statement |
|---|---|---|
| `SimpleGraph.Iso.connected_iff` | `Combinatorics/SimpleGraph/Connectivity/Connected.lean:364` | `G ≃g H → (G.Connected ↔ H.Connected)` |
| `SimpleGraph.Iso.preconnected_iff` | `Connected.lean:265` | |
| `SimpleGraph.Reachable.map`, `Preconnected.map`, `Connected.map` | `Connected.lean:122, 236, 334` | push along homs (surjective for (pre)connected) |
| `SimpleGraph.Connected.mono` | `Connected.lean:340` | `G ≤ G' → G.Connected → G'.Connected` |
| `SimpleGraph.comap_monotone` | `Maps.lean:160` | `induce` is `comap` of `Embedding.subtype`, so it is monotone in G |
| `SimpleGraph.induce_union_connected` | `Connectivity/Subgraph.lean:564` | `(G.induce s).Preconnected → (G.induce t).Preconnected → (s ∩ t).Nonempty → (G.induce (s ∪ t)).Connected` |
| `SimpleGraph.connected_induce_union` | `Connectivity/Subgraph.lean:587` | the variant joined by an edge |
| `SimpleGraph.induceUnivIso` | `Maps.lean:907` | `G.induce Set.univ ≃g G` |
| `SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial` | `Acyclic.lean:555` | a connected finite nontrivial G has **one** v with G − v connected |
| `SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one` | `Connected.lean:1040` | deleting a leaf keeps G connected |
| `SimpleGraph.Preconnected.induce_of_degree_eq_one` | `Connected.lean:1029` | |
| `SimpleGraph.Connected.exists_isTree_le` | `Acyclic.lean:463` | spanning tree |
| `SimpleGraph.IsTree.exists_ne_and_degree_eq_one` | `Acyclic.lean:536` | a nontrivial finite tree has **two** distinct leaves |
| `SimpleGraph.connected_induce_iff`, `preconnected_induce_iff` | `Connectivity/Subgraph.lean:555,560` | bridge to `Subgraph` |
| `SimpleGraph.ConnectedComponent`, `sum_connectedComponent_ncard_edgeSet` | `Connected.lean`, 761 | for the `discon` program |

**Route for "G connected ⟺ at least two cards connected" (n ≥ 3).**
- (⇐) Take u ≠ v with both cards connected, and a third vertex w (this is where n ≥ 3 is
  used). Apply `induce_union_connected` to `{u}ᶜ` and `{v}ᶜ` (they meet in w), whose union is
  `univ`, then use `induceUnivIso`. **I compiled this direction in full** in probe.lean (about
  10 lines).
- (⇒) Take a spanning tree T (`exists_isTree_le`) and two leaves u ≠ v
  (`exists_ne_and_degree_eq_one`). Then `T − u` is connected
  (`induce_compl_singleton_of_degree_eq_one`), so `G − u` is connected (`Connected.mono` with
  `comap_monotone`); the same holds for v. Needs `Nontrivial (Fin n)`, from n ≥ 3.
- Recognizable: σ is a bijection that matches connected cards with connected cards
  (`Iso.connected_iff`). So `{v | (card G v).Connected}.ncard` equals the same count for H, by
  `Set.ncard_congr'` restricted from σ, or by `Set.ncard_image_of_injective` (`Data/Set/Card.lean:855`).

Difficulty: **easy-medium**, about 60–120 lines. Everything needed exists.

## 4. Trees and acyclicity (for the `trees` and `discon` programs)

All in `Combinatorics/SimpleGraph/Acyclic.lean`:
- `IsAcyclic` (52) and `IsTree`;
- `Iso.isAcyclic_iff` (82) and `Iso.isTree_iff` (86);
- `IsAcyclic.induce` (97), `IsAcyclic.embedding` (78) and `IsAcyclic.anti` (105);
- `IsTree.card_edgeFinset` (292): `#E + 1 = card V`;
- `isTree_iff_connected_and_card` (479): `IsTree ↔ Connected ∧ Nat.card E + 1 = Nat.card V`;
- `isTree_iff_isAcyclic_and_ncard_edgeSet_add_one_eq_card` (511);
- `IsTree.minDegree_eq_one_of_nontrivial` (517);
- `IsTree.exists_vert_degree_one_of_nontrivial` (531).

Consequence: **"G is a tree" is recognizable** directly from `isTree_iff_connected_and_card`
plus the edge count and connectivity results above. Order is `n`. Easy once sections 1 and 3
are checked.

## 5. Gaps summary (things to build in proof files, not in Mathlib)

1. Restricting the codomain of a `Copy`/`Hom` to `G.induce s` when the range lies in `s`.
2. Isomorphism invariance of `labelledCopyCount` and `copyCount`, in both arguments.
3. `labelledCopyCount = Fintype.card (F ≃g F) * copyCount` (the orbit count), needed only to
   pass between the labelled and unlabelled forms.
4. A counting function for induced copies.
5. Any notion of the deck as a multiset. Recon deliberately avoids one, and Mathlib has none.
6. Characteristic, Tutte and chromatic polynomials of a graph: absent or very thin for
   `SimpleGraph`. This is UNVERIFIED in detail: I did not grep beyond `Coloring/`. Do not plan
   steps on them.
7. Ready-made `Set.ncard` forms of `card_edgeFinset_*`: absent. Bridge with
   `Set.ncard_eq_toFinset_card'`.

## 6. Suggested step order (proposal candidates; not proposed here)

1. `kelly_card_edges_add_degree`: `|E(G−v)| + deg v = |E|`.
2. `kelly_edge_sum`: `Σ|E(G−v)| = (n−2)|E|`.
3. `kelly_edge_count`: hypomorphic graphs with n ≥ 3 have equal edge counts.
4. `kelly_degree_sequence`: the strong form; σ preserves degrees.
5. `kelly_connected_iff_two_cards`, then `kelly_connected_recognizable`.
6. `kelly_lemma_labelled`, then `kelly_copycount_recognizable` (k < n).
