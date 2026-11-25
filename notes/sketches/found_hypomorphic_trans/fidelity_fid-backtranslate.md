# Fidelity review: found_hypomorphic_trans (lens: back-translation)

Reviewer: fid-backtranslate. Statement sha256 d6f23421...cbe.

## 1. Independent reading of the Lean (written before reading statement_en)

Expanding `Recon.Hypomorphic` and `Recon.card` from `lean/Recon/Basic.lean`:

For every natural number n and all simple graphs G, H, K on the vertex type `Fin n`:
if there is a bijection σ : Fin n ≃ Fin n such that for every vertex x the induced subgraph
of G on {x}ᶜ is isomorphic (`Nonempty (_ ≃g _)`) to the induced subgraph of H on {σ x}ᶜ,
and there is a bijection τ : Fin n ≃ Fin n such that for every vertex y the induced subgraph
of H on {y}ᶜ is isomorphic to the induced subgraph of K on {τ y}ᶜ,
then there is a bijection ρ : Fin n ≃ Fin n such that for every vertex x the induced subgraph
of G on {x}ᶜ is isomorphic to the induced subgraph of K on {ρ x}ᶜ.

In words: having the same deck (as a card-matching bijection) is a transitive relation on
graphs on Fin n.

## 2. Clause-by-clause comparison with statement_en

| English clause | Lean | Match |
|---|---|---|
| "For every n" | `∀ (n : ℕ)` | yes |
| "all graphs G, H, K on Fin n" | `∀ (G H K : SimpleGraph (Fin n))` | yes; one common vertex type, as stated |
| "G and H are hypomorphic" | `Recon.Hypomorphic G H` (first hypothesis) | yes |
| "H and K are hypomorphic" | `Recon.Hypomorphic H K` (second hypothesis) | yes, direction H to K as stated |
| "then G and K are hypomorphic" | `Recon.Hypomorphic G K` | yes, direction G to K |

## 3. Failure-mode checklist

- Quantifier order/scope: all universal, outermost; σ and τ are existential inside each
  hypothesis, the witness ρ in the conclusion is free to be chosen (σ followed by τ). Fine.
- Missing/extra hypothesis: no `3 ≤ n`, and none is needed. Transitivity holds for every n
  (including n = 0, 1, 2); the English also says "for every n". Adding n ≥ 3 would weaken it.
- Fin n vs arbitrary types: Lean restricts to Fin n, exactly as the English says. This is
  a specialisation of the general heterogeneous `Hypomorphic`, not a mismatch.
- ≤ vs <, off-by-one: none present.
- Vacuity: hypotheses are satisfiable (e.g. G = H = K, by `anchor_hypomorphic_refl`), and
  the conclusion is non-trivial (it is not true for arbitrary G, K, by
  `anchor_three_vertices_not_hypomorphic`). Not trivially true or vacuous.
- Notion of isomorphism/card/deck: uses the trusted `card` (induced subgraph on {x}ᶜ) and
  `≃g` (Mathlib graph isomorphism); deck equality is the standard Bondy–Hemminger
  bijection form. Correct notion.
- Nonempty vs structure: `Hypomorphic` is a Prop (∃ σ, ∀ x, Nonempty ...), and the
  statement is a Prop; no data-vs-Prop confusion.
- Coercions: the card vertex types `({x}ᶜ : Set (Fin n))` are subtypes; no numeric
  coercions occur.

## 4. Expected truth

True: take ρ = σ.trans τ; for each x compose the isomorphisms
card G x ≃g card H (σ x) ≃g card K (τ (σ x)). This is a sanity note, not a result.

## Verdict

PASS. The Lean statement says exactly what the English says.
