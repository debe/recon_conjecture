# Fidelity review: kelly_edge_sum (lens: back-translation, reviewer fid-backtranslate)

## Lean statement
`∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∑ v : Fin n, (Recon.card G v).edgeSet.ncard = (n - 2) * G.edgeSet.ncard`

## Independent back-translation (written before reading statement_en)
`Recon.card G v` is the abbrev `G.induce ({v}ᶜ : Set (Fin n))`, the subgraph of G induced on
every vertex except v, with vertex type the subtype `{v}ᶜ`. Reading: "For every natural
number n and every simple graph G on vertex set Fin n, the sum over all vertices v of the
number of edges of the induced subgraph G − v equals (n − 2) times the number of edges of G,
where n − 2 is truncated natural subtraction."

## Clause-by-clause comparison with statement_en
- "For every n and every graph G on Fin n": matches `∀ n, ∀ G : SimpleGraph (Fin n)`. No
  hypothesis on n, and none is needed (see below). Fin n, as in the English.
- "sum over all vertices v": `∑ v : Fin n` over the full Fintype. Matches.
- "number of edges of the card G − v": `(Recon.card G v).edgeSet.ncard`. The card is the
  induced subgraph on `{v}ᶜ`, which is the repository's definition of a card. `Set.ncard`
  returns 0 on infinite sets, but every edge set here is finite (finite vertex type), so
  ncard is the true edge count. The count is taken in the subtype graph, not after mapping
  back into Fin n. The edge count is the same either way.
- "equals (n − 2) times the number of edges of G": `(n - 2) * G.edgeSet.ncard` in ℕ. Matches.
- "natural-number subtraction; both sides are 0 when n < 2": correct. For n ∈ {0, 1}, G has
  no edges and every card has no edges, so both sides are 0. The English states the
  truncation explicitly, so the coercion convention is not hidden.

## Failure-mode checklist
- Quantifier order and scope: fine.
- Missing or extra hypothesis: none. The identity holds for all n, including n < 3, because
  each edge {a, b} survives in exactly the n − 2 cards G − v with v ∉ {a, b}, and in ℕ,
  n·m − 2·m = (n − 2)·m.
- ≤ against <, off-by-one: the factor is n − 2, which is the right one.
- Vacuous or trivial: no. It is the genuine double-counting identity behind the recognizability
  of edge count (Kelly's lemma for H = K₂). The edge-count recognizability step builds on it.
- Notion of card: Recon.card. Notion of count: edgeSet.ncard, the right one for simple graphs.
- Coercions: only ℕ arithmetic. No ℤ or ℚ division is hidden.

## Sanity search
A brute-force enumeration of all labelled graphs on n = 0..6 vertices (Python, Lean reading
with truncated subtraction) found 0 mismatches between the LHS and the RHS. The statement is
not evidently false.

## Verdict
PASS. The Lean statement says exactly what the English says.
