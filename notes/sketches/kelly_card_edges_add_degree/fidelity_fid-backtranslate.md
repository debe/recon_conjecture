# Fidelity review: kelly_card_edges_add_degree (lens: back-translation, reviewer fid-backtranslate)

## Lean statement
∀ (n : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n),
  (Recon.card G v).edgeSet.ncard + (G.neighborSet v).ncard = G.edgeSet.ncard

## Expansion of Recon definitions
- `Recon.card G v` is an abbrev for `G.induce ({v}ᶜ : Set (Fin n))`: the simple graph on the
  subtype of vertices other than v, where two such vertices are adjacent iff they are adjacent in G.

## My own English reading (written before reading statement_en)
For every natural number n, every simple graph G on vertex set Fin n and every vertex v of G:
the number of edges of the induced subgraph G - v (on all vertices except v), plus the number
of neighbours of v in G, equals the number of edges of G. All counts are `Set.ncard`, an
equation in ℕ (no subtraction involved).

## Comparison with statement_en
"For every n, every graph G on Fin n and every vertex v: the number of edges of the card G - v
plus the degree of v in G equals the number of edges of G."
- Quantifiers: ∀ n, ∀ G, ∀ v; same order and scope. Match.
- Vertex type Fin n: match.
- "card G - v": Recon.card = induced subgraph on {v}ᶜ, the standard vertex-deleted subgraph. Match.
- "degree of v": `(G.neighborSet v).ncard`; the neighbour set of a vertex in a simple graph
  (loopless) is exactly what degree counts, equal to `G.degree v` on a finite type. Match.
- "number of edges": `edgeSet.ncard`. Edge sets live in `Sym2 (Fin n)` resp.
  `Sym2 {v}ᶜ`; all sets are finite (Fin n is a Fintype), so `ncard` never collapses to the
  infinite-set default 0. The card's edges in `Sym2` of the subtype map injectively to edges
  of G avoiding v, so ncard counts them correctly. Match.
- Hypotheses: no n ≥ 3 is needed; the identity holds for all n (n = 0 is vacuous since Fin 0
  is empty; n = 1 gives 0 + 0 = 0). The English also has no such hypothesis. Match.
- Title "A card has |E| minus deg v edges" is the same fact phrased with subtraction; the Lean
  uses the addition form, which avoids ℕ truncated subtraction. Equivalent since deg v ≤ |E|.

## Non-vacuity / non-triviality
Hypotheses are satisfiable (any n ≥ 1). The conclusion is a genuine counting identity
(partition of E(G) into edges through v and edges of G - v), not true by definition.
Brute-force sanity check of the intended combinatorial identity over all labelled graphs on
n ≤ 5 vertices and all v: 0 mismatches. It is the standard first step toward
"degree sequence is recognizable" (deg v = |E| − |E(G − v)|, CLAUDE.md §3).

## Coercions
None that change meaning: all quantities are ℕ, no casts.

## Verdict: PASS
