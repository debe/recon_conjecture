# Fidelity review: found_hypomorphic_symm (lens: testing, reviewer fid-testing)

Verdict: **pass**

## Statement under review
- Lean: `∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Recon.Hypomorphic G H → Recon.Hypomorphic H G`
- English: "For every n and all graphs G, H on Fin n: if G and H are hypomorphic (have the
  same deck), then H and G are hypomorphic."
- `Recon.Hypomorphic G H := ∃ σ : V ≃ W, ∀ x, Nonempty (card G x ≃g card H (σ x))`, with
  `card G x = G.induce {x}ᶜ` (Basic.lean).

## Predicates encoded (script: `notes/sketches/found_hypomorphic_symm/fid_testing_check.py`)
- `lean_hyp(G, H)`: a direct encoding of the Lean definition. It checks for a bijection
  V → W that matches every card G − x with an isomorphic card H − σx. I compute it two ways:
  as a perfect matching in the bipartite "card-isomorphic" relation (using `nx.is_isomorphic`
  on induced subgraphs), and by brute force over all permutations. Neither way uses the
  canonical forms in `small_graphs.py`, so the check does not depend on that library. The
  bijection between equal-size vertex sets is a real `Equiv`. When n = 0 the predicate holds
  vacuously.
- `en_hyp(G, H)`: the English reading "same deck". It holds when the multisets of cards up
  to isomorphism are equal (`small_graphs.deck_key`) and the orders are equal.
- I compare the Lean statement `lean_hyp(G,H) → lean_hyp(H,G)` with the English statement
  `en_hyp(G,H) → en_hyp(H,G)`.

## Results
- **Unlabeled run:** all ordered pairs of isomorphism classes with n = 0..6 (25,635 pairs,
  networkx atlas). The two statements never differ, and the Lean statement never fails.
  `lean_hyp` and `en_hyp` agree on every pair, so the Bondy–Hemminger bijection form and the
  multiset form of the deck match.
- **Labeled run:** every labeled graph on Fin n with n = 0..4 (4,166 ordered pairs), using
  brute-force permutation search. There are 0 differences and 0 failures of symmetry.
  Labels matter here because `Hypomorphic` is stated on labeled `SimpleGraph (Fin n)`.
- **Vacuity:** the hypothesis does hold. Across the unlabeled pairs it is true for 211 of
  them: the 209 diagonal pairs (reflexivity, matching `anchor_hypomorphic_refl`) and both
  orders of the non-isomorphic pair K2 / 2K1 at n = 2, which matches
  `anchor_two_vertices_hypomorphic`. In the labeled run it holds for 582 pairs. The library's
  `hypomorphic` agrees on the n = 2 anchor.

## Checklist of failure modes
- **Quantifier order and scope:** n, G and H are all universally quantified, and the
  implication sits inside, as the English says.
- **Missing or extra hypothesis:** there is no `3 ≤ n`, and that is correct. Symmetry holds
  for every n, including n = 2, where the hypothesis is genuinely satisfied by non-isomorphic
  graphs. The English says "for every n", which matches.
- **`Fin n` against arbitrary types:** both readings use Fin n, and G and H share the same
  n. The general `Hypomorphic` is heterogeneous, but here it is only instantiated on one
  type. That is a restriction the English states, not a mismatch.
- **≤ against < or off-by-one:** not applicable.
- **Vacuity or triviality:** the statement is not vacuous (see above). It is easy, because
  it needs σ.symm and the inverse card isomorphisms, but it is a real lemma, not
  definitionally `True`.
- **Notion of isomorphism, card and deck:** `≃g` on induced subgraphs on `{x}ᶜ` is the
  vertex-deleted card, and the bijection form equals the multiset deck. I checked that
  empirically above.
- **Nonempty against an explicit structure:** `Nonempty (… ≃g …)` is the right
  propositional form for "isomorphic".
- **Coercions:** none that change meaning. The subtype `{x}ᶜ` card is standard.

## Conclusion
The Lean statement means what the English says. I found no distinguishing graph.
