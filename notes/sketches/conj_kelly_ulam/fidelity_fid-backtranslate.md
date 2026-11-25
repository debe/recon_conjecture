# Fidelity review: conj_kelly_ulam (lens: back-translation, reviewer fid-backtranslate)

Verdict: PASS

## Lean statement

`S_conj_kelly_ulam := Recon.ReconstructionConjecture`. Basic.lean expands it as follows:

```
∀ n : ℕ, 3 ≤ n → ∀ G : SimpleGraph (Fin n),
  ∀ H : SimpleGraph (Fin n),
    (∃ σ : Fin n ≃ Fin n, ∀ x, Nonempty (G.induce {x}ᶜ ≃g H.induce {σ x}ᶜ)) →
    Nonempty (G ≃g H)
```

## My English reading (written before I read statement_en)

"For every n ≥ 3 and every pair of simple graphs G, H on the vertex set {0, …, n−1}, the
following holds. Suppose some bijection σ of the vertices makes every vertex-deleted
induced subgraph G − x isomorphic to H − σ(x). Then G and H are isomorphic."

## Comparison with statement_en ("Every graph on at least 3 vertices is reconstructible")

- **Quantifiers.** The order is ∀ n, ∀ G, ∀ H, as in "every G is reconstructible" (every H
  with the same deck is ≅ G). Their scope is correct.
- **Hypothesis n ≥ 3.** It is present as `3 ≤ n` (not `<`, no off-by-one). It is exactly
  the Kelly–Ulam bound: n = 2 fails, and the anchors `anchor_two_vertices_hypomorphic` and
  `anchor_two_vertices_not_iso` pin this.
- **Deck / hypomorphism.** A bijection that matches cards to isomorphic cards exists iff the
  two multisets of card isomorphism classes are equal. This is the standard notion
  (Bondy–Hemminger) and a multiset notion, not the set notion of set reconstruction.
- **Card.** `G.induce {x}ᶜ` is the vertex-deleted induced subgraph, the standard card.
- **Isomorphism.** Mathlib `≃g` (`RelIso` on adjacency) is the standard graph isomorphism.
  The conclusion is `Nonempty`, which is correct for a Prop.
- **Fin n against arbitrary types.** This loses nothing. A finite graph on n vertices is
  isomorphic to one on Fin n, and both hypomorphism and isomorphism are invariant under
  relabelling. A graph hypomorphic to G must have exactly n vertices, because σ is a
  bijection, so letting H range only over Fin n is no restriction. Infinite graphs are
  excluded, which is correct: the conjecture fails for infinite graphs (Fisher 1969).
- **Vacuity / triviality.** The hypothesis can hold: take H = G, by
  `anchor_hypomorphic_refl`. The statement is not trivially true: the same statement with
  `2 ≤ n` is false by the anchors, and `anchor_three_vertices_not_hypomorphic` shows that
  Hypomorphic really looks at the cards.
- **Coercions.** `{x}ᶜ : Set (Fin n)` is coerced to a subtype. The two cards live on
  different subtypes, `{x}ᶜ` and `{σ x}ᶜ`, and `≃g` between them is a genuine isomorphism.
  No numeric coercions occur.

## Conclusion

The Lean statement is the Kelly–Ulam vertex reconstruction conjecture for finite simple
graphs on n ≥ 3 vertices, and statement_en says the same. I found no mismatch.
