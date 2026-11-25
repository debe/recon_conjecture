# Fidelity review: found_hypomorphic_iso_invariant (lens: testing, reviewer fid-testing)

Verdict: **pass**

## Statement under review
Lean: `∀ (n : ℕ) (G G' H H' : SimpleGraph (Fin n)), Nonempty (G ≃g G') → Nonempty (H ≃g H') →
Recon.Hypomorphic G H → Recon.Hypomorphic G' H'`

English: for every n and all graphs G, G', H, H' on Fin n, if G ≅ G', H ≅ H' and G, H are
hypomorphic, then G', H' are hypomorphic.

## Predicates encoded (script: `fid_testing_script.py` in this directory)
- Lean reading: `lean_hyp(G,H)` = there is a bijection σ with `G - x ≅ H - σx` for all x,
  with cards as induced subgraphs keeping their original labels (as `G.induce {x}ᶜ`).
  The ∃σ is decided exactly, as a perfect matching in the bipartite "cards isomorphic" graph.
  Isomorphism (`Nonempty (G ≃g G')`) is `nx.is_isomorphic`.
- English reading: `en_hyp` = equal decks, that is equal multisets of card isomorphism classes
  (`small_graphs.hypomorphic`, which uses canonical forms).
- Each statement instance is `iso ∧ iso ∧ hyp(G,H) → hyp(G',H')` under the matching notion.

## Search
- n = 0..3: every labelled quadruple (G, G', H, H') on Fin n (4096 at n = 3).
- n = 0..6: every pair of atlas graphs (G, H), comparing `lean_hyp` with `en_hyp` directly.
  For each hypomorphic pair, 4 random relabellings (G', H') were tried, plus cases where the
  isomorphism hypothesis fails.
- Result: **0 disagreements** between the predicates, and no instance where either
  statement is false.

## Vacuity / triviality
- The hypothesis holds often. The labelled count at n = 3 is 164 = 1⁴ + 3⁴ + 3⁴ + 1⁴, as
  expected. It also holds non-trivially, with G ≇ H: at n = 2, G = K₂ and H = 2K₁ (2 such
  labelled quadruples). So the statement is not vacuous, and it covers the genuine
  hypomorphic-but-not-isomorphic case.
- The conclusion is not trivially true: there are many non-hypomorphic pairs at every n ≥ 3.
- n = 0, 1, 2 are included, which matches "for every n". No `3 ≤ n` is needed or claimed.

## Failure-mode checklist
- Quantifier order and scope: all universal, and the implications are in the right order. OK.
- Hypotheses: none missing or extra. The absence of n ≥ 3 is correct for this lemma.
- `Fin n`: all four graphs share `Fin n`, as the English says. This is narrower than
  arbitrary types, but that is faithful.
- Isomorphism notion: `Nonempty (G ≃g G')`, the Mathlib graph isomorphism, is correct.
  Hypomorphism is the Basic.lean bijection-of-cards definition, which on finite graphs is
  equivalent to equality of decks (confirmed empirically for n ≤ 6).
- No coercions are involved.
