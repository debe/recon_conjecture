# Fidelity review: found_hypomorphic_symm (lens: back-translation)

Reviewer: fid-backtranslate

## Lean statement

    ∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Recon.Hypomorphic G H → Recon.Hypomorphic H G

## My back-translation (written before I compared it with statement_en)

I expanded `Recon.Hypomorphic` and `Recon.card` from `lean/Recon/Basic.lean`:
- `card G x := G.induce ({x}ᶜ)`, the subgraph of G induced on every vertex except x;
- `Hypomorphic G H := ∃ σ : V ≃ W, ∀ x, Nonempty (card G x ≃g card H (σ x))`.

Reading: "For every natural number n and all simple graphs G and H on vertex set
Fin n: suppose there is a bijection σ : Fin n → Fin n such that for every vertex x the card
G − x is isomorphic, as a graph, to the card H − σ(x). Then there is a bijection
τ : Fin n → Fin n such that for every vertex y the card H − y is isomorphic to the card
G − τ(y)."

## Clause-by-clause comparison with statement_en

statement_en: "For every n and all graphs G, H on Fin n: if G and H are hypomorphic (have the
same deck), then H and G are hypomorphic."

| Clause | Lean | Match |
|---|---|---|
| "for every n" | `∀ (n : ℕ)`; there is no lower bound on n | yes. Symmetry holds for every n, including 0, 1 and 2, so an n ≥ 3 hypothesis is neither needed nor claimed |
| "all graphs G, H on Fin n" | `G H : SimpleGraph (Fin n)`, both on the same Fin n | yes. Simple graphs are the project convention |
| "G and H hypomorphic (same deck)" | `Recon.Hypomorphic G H` | yes. It is the Bondy–Hemminger bijection form of "same deck" from the trusted Basic.lean, and the card notion is the induced subgraph on {x}ᶜ |
| "then H and G hypomorphic" | `Recon.Hypomorphic H G`, with the arguments swapped | yes. The arguments sit in the right order |

## Failure-mode checklist

- Quantifier order and scope: all universal and outermost, and the implication is at the right place. OK.
- Missing or extra hypothesis: none. The English has no n ≥ 3, and the Lean has none either. OK.
- Fin n against arbitrary types: the English says Fin n and the Lean uses Fin n. The result is a
  specialization of the general-type fact, which is fine for this statement. OK.
- ≤ against <, off-by-one: not applicable.
- Vacuity: the hypothesis is satisfiable. `anchor_hypomorphic_refl` gives Hypomorphic G G for every G.
- Trivially true: the conclusion is not true for free. `anchor_three_vertices_not_hypomorphic` shows
  Hypomorphic can fail, so the statement needs real content (σ⁻¹ and the inverse card isos, with
  transport along σ (σ.symm y) = y). It is easy but not vacuous, which is right for a
  foundational lemma.
- Notion of iso, card or deck: `≃g` is graph isomorphism between the induced cards, and it matches
  the "same deck" (multiset of iso classes) characterization. OK.
- Nonempty against an explicit structure: `Nonempty (… ≃g …)` is the existence of an isomorphism,
  which is the intended meaning. OK.
- Coercions: the card vertex types are subtypes `{x}ᶜ : Set (Fin n)`. No numeric coercions are
  involved. OK.

## Verdict: PASS

The Lean statement says exactly what the English says.
