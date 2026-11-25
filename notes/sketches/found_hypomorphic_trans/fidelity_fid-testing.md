# Fidelity review: found_hypomorphic_trans (lens: testing, reviewer fid-testing)

Verdict: **pass**

## Statement under review

Lean (`S_found_hypomorphic_trans`, sha256 d6f23421...):
`∀ (n : ℕ) (G H K : SimpleGraph (Fin n)), Recon.Hypomorphic G H → Recon.Hypomorphic H K → Recon.Hypomorphic G K`

English: for every n and all graphs G, H, K on Fin n, if G and H are hypomorphic and H and K
are hypomorphic, then G and K are hypomorphic.

`Recon.Hypomorphic G H := ∃ σ : V ≃ W, ∀ x, Nonempty (card G x ≃g card H (σ x))`, where
`card G x = G.induce {x}ᶜ`.

## Predicates encoded

- **Lean reading** (`lean_hyp_perm`): literal search over every bijection σ, requiring each
  induced subgraph `G[V∖{x}]` (original labels kept, as for the subtype) to be isomorphic
  (networkx VF2) to `H[V∖{σx}]`. A matching-based variant (`lean_hyp_match`, a perfect
  matching in the card-isomorphism bipartite relation, which is equivalent to ∃σ) is used
  for the unlabelled sweep up to n = 6.
- **English reading** (`en_hyp`): equal decks, meaning equal multisets of canonical forms
  of the cards (`small_graphs.hypomorphic` / `deck_key`). This is independent of the Lean
  encoding: it uses canon, not VF2.
- Statement-level: for each relation, check every chain G~H, H~K for G~K.

Script: `notes/sketches/found_hypomorphic_trans/fidelity_fid-testing_script.py` (run time
about 3 minutes).

## Results

| sweep | n | pair disagreements (Lean vs English) | hypothesis chains | transitivity failures |
|---|---|---|---|---|
| unlabelled (atlas) | 0..6 | 0 | 1,1,8,4,11,34,156 | 0 (both readings) |
| all labelled graphs on Fin n | 0..4 | 0 | 1,1,8,56,5800 | 0 (both readings) |

The two predicates agree on every pair of graphs tested, and so do the two statement readings
on every triple.

## Vacuity and triviality

- The hypothesis is not vacuous. `Hypomorphic G G` always holds (anchor
  `anchor_hypomorphic_refl`), so chains exist for every n. At n = 2 there are non-isomorphic
  hypomorphic chains (K2 and 2K1, as in `anchor_two_vertices_hypomorphic`). For labelled graphs
  on Fin 4 there are 556 hypomorphic ordered pairs, which gives 5800 chains.
- The conclusion is not trivially true: `Hypomorphic` is false for many pairs (for example
  `anchor_three_vertices_not_hypomorphic`), so a counterexample was possible in principle.
- The statement itself is easy (compose σ's and the card isomorphisms). That matches the
  English, which is a basic foundation fact, so it is not a fidelity defect.

## Failure-mode checklist

- Quantifier order and scope: n, G, H, K are all universal, and the hypotheses are a curried
  implication. This matches the English.
- Missing or extra hypothesis: there is no `3 ≤ n`, and none is needed or stated in the English
  ("for every n"). Transitivity holds for n = 0, 1, 2 as well, and the tests confirm it.
- `Fin n` against arbitrary types: the English says "on Fin n", so they match. All three graphs
  share the vertex type, which is the intended reading.
- Notion of deck: the ∃-bijection definition agrees with multiset-of-cards deck equality on
  every tested pair.
- Nonempty against structure, and coercions: `Nonempty (≃g)` per card is the intended
  "isomorphic". No coercions are involved.

There is no mismatch.
