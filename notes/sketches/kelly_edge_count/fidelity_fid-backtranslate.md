# Fidelity review: kelly_edge_count (lens: back-translation)

Reviewer: fid-backtranslate. Verdict: **pass**.

## 1. My reading of the Lean, written before I read statement_en

Lean body:
`∀ n : ℕ, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H → G.edgeSet.ncard = H.edgeSet.ncard`

Expanding `Recon.Hypomorphic` and `Recon.card` from `lean/Recon/Basic.lean`:

> For every natural number n with n ≥ 3, and for all simple graphs G and H on the vertex
> set {0, …, n−1}: suppose there is a bijection σ of the vertex set such that, for every
> vertex x, the subgraph of G induced on V ∖ {x} is isomorphic (as a graph) to the subgraph
> of H induced on V ∖ {σ x}. Then the number of edges of G equals the number of edges of H,
> where "number of edges" is the cardinality (`Set.ncard`) of the set of unordered pairs
> `Sym2 (Fin n)` that are adjacent.

## 2. Clause-by-clause comparison with statement_en

statement_en: "For every n at least 3 and all graphs G, H on Fin n: if G and H are
hypomorphic (have the same deck), then G and H have the same number of edges."

| English clause | Lean | Match |
|---|---|---|
| for every n at least 3 | `∀ n : ℕ, 3 ≤ n →` | yes; `≤`, not `<`, so n = 3 is included |
| all graphs G, H on Fin n | `∀ G H : SimpleGraph (Fin n)` | yes; simple undirected loopless graphs on the same vertex type |
| G and H are hypomorphic (same deck) | `Recon.Hypomorphic G H` | yes; a bijection matching each card G − x to an isomorphic card H − σx is exactly equality of the decks as multisets of isomorphism classes (Bondy–Hemminger) |
| same number of edges | `G.edgeSet.ncard = H.edgeSet.ncard` | yes, see the coercion check below |

Quantifier order: n comes first, then G and H; the hypothesis is the only premise. There are
no extra or missing hypotheses.

## 3. Failure-mode checklist

- **Quantifier order or scope:** correct.
- **Hypothesis n ≥ 3:** present. It is needed: at n = 2, K₂ and 2K₁ are hypomorphic
  (`anchor_two_vertices_hypomorphic`) but have 1 and 0 edges. Without the bound the
  statement would be false. The bound matches the edge-count formula
  |E| = Σ|E(G − v)| / (n − 2).
- **Fin n against arbitrary types:** both graphs are on `Fin n`. This matches the English
  and the repo convention.
- **ncard and coercion:** `G.edgeSet : Set (Sym2 (Fin n))` is finite because `Fin n` is
  finite, so `Set.ncard` is the true edge count. The infinite-set-has-ncard-0 trap does not
  apply. It agrees with `G.edgeFinset.card`. Both sides are ℕ; no coercion changes meaning.
- **Vacuity or triviality:** not vacuous, because Hypomorphic is reflexive (anchor), so
  the premise can hold. It is also not trivial, because non-isomorphic graphs can have
  hypomorphic-looking pairs only when the deck carries the information; at n = 2 the
  conclusion fails. The statement is a genuine (and known true, Kelly) recognizability
  fact.
- **Notion of isomorphism, card or deck:** `card` is the induced subgraph on `{x}ᶜ`, which
  is the standard vertex-deleted subgraph. `≃g` is graph isomorphism. `Nonempty` is the
  right wrapper for "is isomorphic to".
- **Nonempty against explicit structure:** the conclusion is a Prop equality; there is no
  issue.

## 4. Elaboration

`lake env lean Recon/Statements/S_kelly_edge_count.lean` elaborates without errors.

## 5. Remark (not a fidelity issue)

The statement is equivalent to `Recon.Recognizable (fun n G => G.edgeSet.ncard = k)` for
all k, phrased directly. It is a faithful formalization of "the size is recognizable from
the deck for n ≥ 3".
