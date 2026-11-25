# Fidelity review: found_hypomorphic_iso_invariant (lens: back-translation)

Reviewer: fid-backtranslate. Verdict: **pass**.

## My reading of the Lean, written before I read statement_en

Expanding `Recon.Hypomorphic` and `Recon.card` from `lean/Recon/Basic.lean`:

For every natural number n and all simple graphs G, G', H, H' on the vertex type `Fin n`
(all four on the same `Fin n`), suppose that:
1. there exists a graph isomorphism G ≅ G' (a bijection of `Fin n` that preserves and
   reflects adjacency);
2. there exists a graph isomorphism H ≅ H';
3. there exists a bijection σ : Fin n ≃ Fin n such that for every vertex x, the induced
   subgraph of G on {x}ᶜ is isomorphic to the induced subgraph of H on {σ x}ᶜ.

Then there exists a bijection τ : Fin n ≃ Fin n such that for every vertex y, the induced
subgraph of G' on {y}ᶜ is isomorphic to the induced subgraph of H' on {τ y}ᶜ.

In short: if G ≅ G', H ≅ H' and G, H have the same deck, then G', H' have the same deck.

## Clause-by-clause comparison with statement_en

| statement_en | Lean | Match |
|---|---|---|
| "For every n" | `∀ (n : ℕ)` | yes. There is no n ≥ 3 hypothesis, and none is needed: the claim holds for every n, including 0, 1 and 2. |
| "all graphs G, G', H, H' on Fin n" | `(G G' H H' : SimpleGraph (Fin n))` | yes. All four share the vertex type `Fin n`, as the English says. |
| "G is isomorphic to G'" | `Nonempty (G ≃g G')` | yes. `≃g` is Mathlib's `SimpleGraph.Iso`, the right notion. Nonempty is correct for a Prop. |
| "H is isomorphic to H'" | `Nonempty (H ≃g H')` | yes |
| "G and H are hypomorphic" | `Recon.Hypomorphic G H` | yes. This is the trusted Bondy–Hemminger definition. |
| "then G' and H' are hypomorphic" | `Recon.Hypomorphic G' H'` | yes |

## Failure-mode checklist

- Quantifier order and scope: all universals come first, followed by a chain of
  implications. There is no hidden existential. Correct.
- Missing or extra hypothesis: none. n ≥ 3 is correctly absent.
- Fin n against arbitrary types: the statement uses Fin n, matching the English. It is
  narrower than a heterogeneous-type version, but it says exactly what the English says.
- ≤ against <, off-by-one: not applicable.
- Vacuity: the hypotheses can hold, for example with G = G' = H = H' (the iso is `Iso.refl`
  and the hypomorphism is `anchor_hypomorphic_refl`). The hypotheses are not contradictory.
- Trivially true: no. The proof has to restrict the isomorphisms φ : G ≅ G' and
  ψ : H ≅ H' to the cards, giving G − φ⁻¹y ≅ G' − y, and so on. A witness is
  τ = ψ ∘ σ ∘ φ⁻¹. The claim is a true, small foundational lemma, which is what a `found`
  step should be.
- Notion of isomorphism, card and deck: `≃g` for isomorphism, `card` = the induced subgraph
  on {x}ᶜ, and the deck only through `Hypomorphic`. All three match the trusted conventions.
- Coercions: none affect meaning. The `Set (Fin n)` subtype for card vertices comes from
  Basic.lean.

## Conclusion

The Lean says exactly what statement_en says. Pass.
