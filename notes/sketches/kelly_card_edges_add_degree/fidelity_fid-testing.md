# Fidelity review: kelly_card_edges_add_degree (lens: testing, reviewer fid-testing)

Verdict: **pass**

## Statement under review
Lean: `∀ (n : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n), (Recon.card G v).edgeSet.ncard + (G.neighborSet v).ncard = G.edgeSet.ncard`

English: for every n, every graph G on Fin n and every vertex v, |E(G − v)| + deg_G(v) = |E(G)|.

## Lean reading
- `Recon.card G v = G.induce {v}ᶜ` (Basic.lean): a graph on the subtype `{v}ᶜ` with G's adjacency.
  Its `edgeSet` is a `Set (Sym2 ↥{v}ᶜ)`: the edges of G with neither endpoint v. `ncard` is the
  ordinary count, because the type is finite, so the "infinite set has ncard 0" convention never applies.
- `G.neighborSet v` = {w | G.Adj v w}. Its `ncard` is deg_G(v). It agrees with `G.degree v`, and
  no `DecidableRel` instance is needed.
- `G.edgeSet.ncard` = |E(G)|.
- Every quantity is ℕ, and the identity is written additively, so truncated subtraction is not an
  issue. (The title says "|E| minus deg v" but the body is additive. That is equivalent in ℕ and safer.)
- The statement has no hypotheses, so it cannot be vacuous through an unsatisfiable hypothesis. The
  only empty slice is n = 0, where there is no v. For every n ≥ 1 there are instances. The English
  also says "every n", so n ≥ 3 is not required here. The identity holds for every n ≥ 1, so leaving
  that hypothesis out is correct.
- The statement uses `Fin n` vertex types, as the English says. No isomorphism notion or deck appears.

## Testing
Script: `notes/sketches/kelly_card_edges_add_degree/fidelity_fid-testing_check.py` (it imports
`tools/search/small_graphs.py` as a library).
- `lean_pred(G, v)`: a literal encoding. The card's edges are the unordered pairs {a, b} with a, b ≠ v,
  a ≠ b and G-adjacent, with no relabelling (the subtype). The neighbour set is {w | adj v w}.
- `en_pred(G, v)`: `small_graphs.card(G, v).number_of_edges() + G.degree(v) == G.number_of_edges()`.

Results:
- Over all graphs up to isomorphism for n = 0..6 (atlas: 1, 1, 2, 4, 11, 34, 156 classes), every
  vertex v was checked. That is 1 + 4 + 12 + 44 + 170 + 936 = 1167 pairs (G, v), and both predicates
  were true on all of them, with 0 disagreements.
- Over all labelled graphs on Fin n for n ≤ 5, every v was checked: 5405 pairs (G, v), with 0
  disagreements and 0 failures. This also covers the labelled quantifier directly, not only
  representatives up to isomorphism.

## Other checks
- The statement file elaborates: `lake env lean` on the generated statement module succeeded.
- It is not trivially true by definition. It needs the real fact that the edges of G split into those
  incident to v (there are deg v of them, through the bijection w ↦ s(v, w)) and those of G − v
  (through `Sym2.map Subtype.val`).
- It is true on every tested case, so the negated twin should not be provable. This is consistent
  with the standard fact (CLAUDE.md §3: deg v = |E| − |E(G − v)|).

No mismatch found.
