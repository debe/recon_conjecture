# Fidelity review: found_reconstructible_compl (lens: back-translation, reviewer fid-backtranslate)

## Lean statement
`∀ n : ℕ, ∀ G : SimpleGraph (Fin n), Recon.Reconstructible G ↔ Recon.Reconstructible Gᶜ`

## Independent English reading (written before reading statement_en)
For every natural number n (including 0, 1, 2) and every simple graph G with vertex set Fin n,
the following are equivalent:
(a) for every simple graph H on Fin n, if there is a permutation σ of Fin n such that for every
    vertex x the induced subgraph of G on Fin n \ {x} is isomorphic to the induced subgraph of H
    on Fin n \ {σ x}, then G and H are isomorphic;
(b) the same property for the complement graph Gᶜ (adjacency: x ≠ y and not G.Adj x y) in place of G.
In short: G is reconstructible iff its complement is reconstructible, with no lower bound on n.

## Comparison with statement_en
statement_en: "For every n and every graph G on Fin n: G is reconstructible if and only if its
complement is reconstructible."
- Quantifiers: ∀ n, ∀ G. Both are universal, there is no ordering issue, and they match "for every n and every graph G".
- Domain: Fin n on both sides. `Reconstructible` quantifies H over Fin n, which matches the English convention.
- No n ≥ 3 hypothesis: the English also says "every n". The claim holds for every n because
  (Gᶜ).induce s = (G.induce s)ᶜ and isomorphisms preserve complements. So Hypomorphic G H ↔
  Hypomorphic Gᶜ Hᶜ and G ≃g H ↔ Gᶜ ≃g Hᶜ, and H ↦ Hᶜ is an involution. Leaving out the hypothesis is
  therefore not an error. At n = 2 both sides are false for G = ⊤ (Gᶜ = ⊥), by the anchors in Basic.lean.
- Notion of complement: checked by elaboration (pp.explicit, `#print`). The right-hand side is
  `@Recon.Reconstructible n (@compl (SimpleGraph (Fin n)) (@SimpleGraph.instCompl (Fin n)) G)`.
  This is the graph complement. It is not the Prop complement `(Reconstructible G)ᶜ`, a misparse
  that would make the statement equivalent to `R ↔ ¬R` and so false.
- Deck/isomorphism notions: these are the standard Basic.lean `Hypomorphic` (bijection σ with every card
  matched up to isomorphism) and `Nonempty (G ≃g H)`, the same notions as everywhere else.
- Vacuity/triviality: the statement is not vacuous because it has no hypotheses. It is not trivially true by
  definition either: it needs the complement-commutes-with-induce argument. Both sides are false at n = 2 and both are true for
  small n ≥ 3 (McKay), so the iff carries real content. It is a standard easy fact (Bondy 1991).
- Coercions: none affect meaning. The only implicit argument is n, which is the same on both sides.

## Verdict
PASS. The Lean statement says exactly what statement_en says.
