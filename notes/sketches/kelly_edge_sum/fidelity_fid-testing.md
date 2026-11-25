# Fidelity review: kelly_edge_sum (lens: testing, reviewer fid-testing)

Verdict: **pass**

## Statement
Lean: `∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∑ v : Fin n, (Recon.card G v).edgeSet.ncard = (n - 2) * G.edgeSet.ncard`

English: for every n and every graph G on Fin n, the sum over all vertices v of the number of
edges of the card G - v equals (n - 2) times the number of edges of G (natural subtraction;
both sides are 0 when n < 2).

## Lean reading (checked by elaboration)
`#print` of the statement shows that every quantity is in ℕ, and no coercion is involved. The sum
runs over `Finset.univ : Finset (Fin n)`. `Recon.card G v = G.induce {v}ᶜ`, so its `edgeSet` is
the set of unordered pairs of distinct vertices other than v that are adjacent in G. The vertex
type is finite, so `Set.ncard` gives the true count and the "infinite set gives 0" convention
never applies. `n - 2` is truncated subtraction.

## Test
The script is `notes/sketches/kelly_edge_sum/fidelity_fid-testing_check.py`. It uses
`tools/search/small_graphs.py` as a library.
- `lean_reading(n, G)`: the LHS is computed from the raw adjacency relation as the number of
  adjacent pairs {a,b} with a,b ≠ v, summed over v. The RHS is `max(n-2,0) * |E|`.
- `english_reading(n, G)`: the LHS is `sum(card(G,v).number_of_edges())` using `small_graphs.card`.
  The RHS uses integer `(n-2)*|E|`, and a second variant uses natural subtraction.

I ran both over every isomorphism class for n = 0..7 (1253 graphs) and over every labelled graph
for n = 0..6 (33,868 graphs, with all 2^15 graphs at n = 6).

Result: the readings never differ, and the Lean predicate holds on every graph. The edge cases
behave as stated:
- n = 0: empty sum = 0 = 0·0;
- n = 1: 0 = 0;
- n = 2: every card has 1 vertex and so 0 edges, and the RHS is 0·|E| = 0. Because |E| = 0 for
  n < 2, natural and integer subtraction agree everywhere.

## Failure-mode checklist
- Quantifiers: there is a plain universal over n and G and no hidden order issue.
- Hypotheses: there are none, so there is no vacuity. The English explicitly claims every n,
  including n < 3, and the identity is true there. A missing `3 ≤ n` is therefore not a
  defect: the identity does not need it.
- `Fin n` matches the English "graph G on Fin n".
- Off-by-one: the factor is n − 2, which is correct because each edge survives in exactly the
  n − 2 cards that delete neither endpoint.
- Not trivially true: it is the content of the double-counting argument for n ≥ 3.
- Card notion: this is the trusted `Recon.card` (induced subgraph on {v}ᶜ), which matches the
  vertex-deleted subgraph. The deck and isomorphism are not involved.
- Coercions: none. Everything is in ℕ.

Evidence only. This is a sketch-level search, not a result.
