# Fidelity review: discon_isolated_vertex (lens: back-translation)

Reviewer: fid-backtranslate. Verdict: **pass**.

## Lean statement

    Recon.ClassReconstructible (fun n G => ∃ v : Fin n, ∀ w : Fin n, ¬ G.Adj v w)

The statement file elaborates (`lake env lean Recon/Statements/S_discon_isolated_vertex.lean` OK).

## Independent back-translation (written before reading statement_en)

Expanding `ClassReconstructible`, `Reconstructible` and `Hypomorphic` from `Basic.lean`:

For every natural number n with 3 ≤ n, and every simple graph G on vertex set Fin n,
if there is a vertex v of G such that no vertex w is adjacent to v, then for every
simple graph H on Fin n: if there is a bijection σ : Fin n ≃ Fin n such that for each
vertex x the card G − x (induced subgraph on {x}ᶜ) is isomorphic to the card H − σ x,
then G is isomorphic to H.

In words: every graph on n ≥ 3 vertices with an isolated vertex is reconstructible
(every graph with the same deck is isomorphic to it).

## Clause-by-clause comparison with statement_en

| English clause | Lean | Match |
|---|---|---|
| "Every graph" | `∀ G : SimpleGraph (Fin n)` inside `ClassReconstructible` | yes; Fin n is the repo's standard headline encoding, and any finite graph is isomorphic to one on Fin n |
| "on at least 3 vertices" | `3 ≤ n` in `ClassReconstructible` | yes; ≤ not <, correct bound (n = 2 fails by the anchor, and K₂ vs 2K₁ is exactly an isolated-vertex case, so the bound matters and is present) |
| "has an isolated vertex (adjacent to no vertex)" | `∃ v : Fin n, ∀ w : Fin n, ¬ G.Adj v w` | yes; quantifier order ∃v ∀w is correct (∀w ∃v would be a different, wrong condition). Including w = v is harmless since SimpleGraph is loopless |
| "is reconstructible" | `Reconstructible G`: ∀ H on Fin n, Hypomorphic G H → Nonempty (G ≃g H) | yes; H ranges over all graphs, not only those with an isolated vertex, which is the correct (stronger) notion |

## Failure-mode checklist

- Quantifier order/scope: ∃ v ∀ w, correct. n is bound before G; G and H share Fin n (hypomorphic graphs have equally many cards, so no loss).
- Missing/extra hypothesis: n ≥ 3 present, nothing extra.
- Fin n vs arbitrary types: standard convention; no loss.
- ≤ vs <, off-by-one: `3 ≤ n`, correct.
- Vacuity: not vacuous; e.g. the empty graph on Fin 3 satisfies the class predicate.
- Triviality: not trivial; it requires a genuine argument (the deck recognises |E|, a card
  with |E| edges comes from an isolated vertex, add back K₁). It is a special case of
  Kelly 1957, so there is no reason to expect a refutation.
- Isomorphism/card/deck notion: uses the trusted `Hypomorphic` (bijection-matched cards,
  Bondy–Hemminger) and `≃g`; correct.
- Nonempty vs structure: `Nonempty (G ≃g H)`, correct for a Prop.
- Coercions: none in the class predicate.

No mismatch found.
