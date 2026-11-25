# Fidelity review: kelly_edge_count (lens: testing, reviewer fid-testing)

Verdict: **pass**

## Statement under review
- English: For every n at least 3 and all graphs G, H on Fin n: if G and H are hypomorphic
  (have the same deck), then G and H have the same number of edges.
- Lean: `∀ n : ℕ, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H → G.edgeSet.ncard = H.edgeSet.ncard`
- `Recon.Hypomorphic G H := ∃ σ : V ≃ W, ∀ x, Nonempty (card G x ≃g card H (σ x))`, with
  `card G x = G.induce {x}ᶜ` (from the trusted Basic definitions file).

## Predicates encoded
Script: `notes/sketches/kelly_edge_count/fidelity_fid-testing_script.py` (uses
`tools/search/small_graphs.py` as a library).
- Lean reading: `hyp_lean` searches for the bijection σ directly, as a perfect matching in the
  bipartite graph "card G-x is isomorphic to card H-y" (networkx `is_isomorphic` on induced
  subgraphs). It does not use `small_graphs.canon`, so it is independent of the English side.
  `lean_pred(n,G,H) = not(3<=n) or not hyp_lean or |E(G)| = |E(H)|`.
- English reading: `hyp_en` is equality of the multiset of card isomorphism classes
  (`deck_key`). `en_pred(n,G,H) = not(n>=3) or not hyp_en or |E(G)| = |E(H)|`.
- H was randomly relabelled for each pair, so labelled graphs are exercised, not only atlas
  representatives.

## Results (all ordered pairs of graphs, n = 0..6)
| n | graphs | pairs | hypomorphic pairs | non-iso hypomorphic | hyp mismatch | pred differ |
|---|---|---|---|---|---|---|
| 0 | 1 | 1 | 1 | 0 | 0 | 0 |
| 1 | 1 | 1 | 1 | 0 | 0 | 0 |
| 2 | 2 | 4 | 4 | 2 | 0 | 0 |
| 3 | 4 | 16 | 4 | 0 | 0 | 0 |
| 4 | 11 | 121 | 11 | 0 | 0 | 0 |
| 5 | 34 | 1156 | 34 | 0 | 0 | 0 |
| 6 | 156 | 24336 | 156 | 0 | 0 | 0 |

There are no pairs where the two readings of hypomorphism differ, and no pairs where the two
predicates differ. Neither predicate is ever false.

## Failure-mode checks
- **Vacuity:** the hypothesis holds. `Hypomorphic G G` always holds (anchor
  `anchor_hypomorphic_refl`), and it held for 205 pairs with n in 3..6.
- **The `3 ≤ n` guard is load-bearing:** at n = 2, K2 and 2K1 satisfy `hyp_lean` (as in the
  anchor `anchor_two_vertices_hypomorphic`) but have 1 and 0 edges. Without the guard the
  statement would be false, and the English says "n at least 3". It is not an extra
  hypothesis.
- **Off-by-one:** `3 ≤ n` matches "at least 3".
- **Edge count:** `G.edgeSet.ncard` is a subset of `Sym2 (Fin n)`, which is finite, so `ncard`
  is the true edge count. The infinite-set-gives-0 pitfall does not apply. It agrees with
  networkx `number_of_edges`.
- **Types and quantifiers:** both graphs are on the same `Fin n`, and n is universally
  quantified outside. This matches the English. `Nonempty (≃g)` is the right notion
  (existence of an isomorphism), and the deck is the standard Bondy–Hemminger bijection form.
- **Trivially true?** No. It does not follow from the definitions without the counting
  argument |E| = Σ|E(G−v)|/(n−2), so it is a genuine (Kelly-style) statement.

## Limitation of the test
For 3 ≤ n ≤ 6, every hypomorphic pair is isomorphic (reconstruction holds there; McKay). So
the edge-count conclusion cannot be distinguished from other isomorphism-invariant
conclusions on this range. The test does confirm that the hypothesis readings coincide
exactly, that the guard matches, and that the statement is not vacuous. The back-translation
lens covers the rest.
