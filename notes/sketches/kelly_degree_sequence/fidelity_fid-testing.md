# Fidelity review: kelly_degree_sequence (lens: testing), reviewer fid-testing

Verdict: **pass**

## Readings encoded

- **Lean predicate** (taken literally): for a given n, G, H on Fin n:
  `3 ≤ n → Hypomorphic G H → ∃ σ : Fin n ≃ Fin n, ∀ v, |N_G(v)| = |N_H(σ v)|`, with
  `Hypomorphic` implemented exactly as in `Basic.lean`: brute force over all permutations σ,
  checking that card `G - x` ≅ card `H - σ x` for every x (canonical forms of the cards).
  The conclusion is also brute force over all permutations σ, comparing degrees pointwise.
- **English predicate:** n ≥ 3 and same deck (equal multisets of card isomorphism classes,
  `deck_key`) ⇒ equal sorted degree sequences.

## Search (tools/search/small_graphs.py as a library)

- All ordered pairs of isomorphism-class representatives for n = 0..6 (`all_graphs`), with
  the Lean and English predicates compared on every pair: **0 differences**.
- The literal `Hypomorphic` (∃ bijection matching the cards) agreed with deck-multiset
  equality on every pair for n ≤ 5, with no prefilter. For n = 6 it agreed on every same-deck
  pair.
- Labeled graphs (every SimpleGraph on Fin n) for n = 3 (8 graphs) and n = 4 (64 graphs):
  20 and 556 hypomorphic ordered pairs respectively, including 12 and 492 pairs of
  *distinct* labeled graphs. The Lean conclusion and the English conclusion held in every
  case.

## Vacuity and triviality

- The hypothesis is satisfiable: `Hypomorphic G G` holds (anchor), and there are many
  hypomorphic pairs of distinct labeled graphs (above). Hypomorphic pairs at n = 3..6:
  4, 11, 34 and 156 (one per isomorphism class, as McKay predicts).
- `3 ≤ n` is necessary and present. At n = 2, K₂ and 2K₁ are hypomorphic, but their degree
  multisets {1,1} and {0,0} differ, so dropping the bound would make the statement false.
- The statement is not trivially true. The conclusion is a real constraint (σ must match
  degrees), and the hypothesis quantifies over the cards. It is not about labeled equality.

## Other failure modes checked

- Quantifiers: ∀ n, ∀ G H, hypothesis → ∃ σ, ∀ v. The order and scope match the English.
- The σ in the conclusion is fresh, not the hypomorphism σ. This matches the English ("some
  bijection") and is the weaker, correct notion of "same degree sequence" (multiset
  equality). It is not "the hypomorphism preserves degrees". That also holds (Kelly), but it
  is not what the English says.
- `Fin n` on both sides, the same n: fine. `ncard` of `neighborSet` on the finite type
  Fin n is the degree, so no infinite-set or ncard = 0 coercion issue arises.
- ≤ against <: `3 ≤ n` matches "at least 3".

Script: the predicates and search are reproduced in the run summary. Runtime is about 2.5 min.
