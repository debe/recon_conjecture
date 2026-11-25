# Fidelity review: found_hypomorphic_compl (lens: back-translation, reviewer fid-backtranslate)

## Independent English reading of the Lean (written before reading statement_en)

Lean: `∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H → Recon.Hypomorphic Gᶜ Hᶜ`

Expanding `Recon.Hypomorphic` and `Recon.card` from the trusted Basic.lean:

For every natural number n (n = 0, 1, 2 included; there is no lower bound) and every pair of
simple graphs G, H on vertex set Fin n: if there exists a bijection σ : Fin n ≃ Fin n such
that for every vertex x the induced subgraph G[V ∖ {x}] is isomorphic to H[V ∖ {σ x}], then
there exists a bijection τ : Fin n ≃ Fin n such that for every vertex x the induced
subgraph Gᶜ[V ∖ {x}] is isomorphic to Hᶜ[V ∖ {τ x}]. Here Gᶜ is the Mathlib complement
graph: `Gᶜ.Adj a b ↔ a ≠ b ∧ ¬ G.Adj a b` (the ordinary loopless complement).

In words: if G and H have the same deck, then so do their complements.

Mechanical confirmation: in a scratch file I typechecked, by `Iff.rfl`, that
`S_found_hypomorphic_compl` is definitionally the fully unfolded statement above
(`∃ σ, ∀ x, Nonempty (G.induce {x}ᶜ ≃g H.induce {σ x}ᶜ)` → the same with `Gᶜ` and `Hᶜ`).
I also typechecked `SimpleGraph.compl_adj` to confirm that `ᶜ` resolves to the SimpleGraph
complement.

## Clause-by-clause comparison with statement_en

| statement_en | Lean | Match |
|---|---|---|
| "For every n" | `∀ n : ℕ` with no hypothesis on n | yes. English sets no bound, and the claim is true for all n, so no n ≥ 3 is needed. |
| "all graphs G, H on Fin n" | `∀ G H : SimpleGraph (Fin n)` | yes. Both share one vertex type, `Fin n`, as the English says. |
| "if G and H are hypomorphic" | `Recon.Hypomorphic G H →` | yes. This is the repo's Bondy–Hemminger same-deck definition (a vertex bijection with card-wise isomorphisms), which is equivalent to equality of the multisets of card isomorphism classes. |
| "then their complements are hypomorphic" | `Recon.Hypomorphic Gᶜ Hᶜ` | yes. `ᶜ` is the graph complement. |
| parenthetical: card of complement = complement of card | none (proof hint) | n/a. It is commentary, not part of the claim. |

## Failure-mode checklist

- Quantifier order and scope: n, G and H are universal, and the hypothesis scopes only the
  conclusion. The σ inside the hypothesis and the τ inside the conclusion are independent
  existentials, which is correct. (The proof can take τ = σ, because
  `(Gᶜ).induce s = (G.induce s)ᶜ` and an isomorphism of graphs is also an isomorphism of
  their complements.)
- Missing or extra hypothesis: none. The fact holds for every n, so leaving out `3 ≤ n` is
  correct and makes the statement stronger, not weaker.
- Fin n against arbitrary types: the English explicitly says Fin n, so the restriction matches.
- ≤ against <, off-by-one: not applicable.
- Vacuity: the hypothesis is satisfiable (`anchor_hypomorphic_refl` gives `Hypomorphic G G`).
- Triviality: the conclusion is not trivially true. `anchor_three_vertices_not_hypomorphic`
  shows that Hypomorphic is a real restriction at n = 3.
- Notion of iso, card and deck: these are the trusted repo definitions. The card is an
  induced subgraph on `{x}ᶜ`, and `≃g` is a graph isomorphism.
- Nonempty against an explicit structure: Prop-level `Nonempty`, the same as in the definition.
- Coercions: `{x}ᶜ` is a set complement coerced to a subtype, the same in the hypothesis and
  the conclusion. `Gᶜ` and `Hᶜ` are graph complements. These two `ᶜ` are distinct notions,
  and each is used correctly.

## Verdict: PASS

The Lean says exactly what the English says: for graphs on Fin n, with no bound on n, the
hypomorphism of G and H implies the hypomorphism of Gᶜ and Hᶜ. This is a standard fact
(Kelly; Bondy 1991).
