# Fidelity review: found_hypomorphic_compl (lens: testing, reviewer fid-testing)

Verdict: **pass**

## Statement under review

Lean: `∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H → Recon.Hypomorphic Gᶜ Hᶜ`

English: for every n and all graphs G, H on Fin n, if G and H are hypomorphic then their
complements are hypomorphic.

`Recon.Hypomorphic G H := ∃ σ : V ≃ W, ∀ x, Nonempty (card G x ≃g card H (σ x))`, with
`card G x := G.induce {x}ᶜ`. `Gᶜ` is Mathlib's complement: `Gᶜ.Adj x y ↔ x ≠ y ∧ ¬ G.Adj x y`.

## Predicates encoded

- **Lean reading** (`lean_pred`): literal. `lean_hyp` searches every permutation σ of
  `range(n)` and checks, for each x, that the card of G at x (induced subgraph on the other
  vertices, labels kept) is isomorphic to the card of H at σ x. The complement is built
  literally as the Mathlib complement (`x ≠ y ∧ ¬ G.Adj x y`). Cards of the complement are
  computed as induced subgraphs *of the complement*, so the card-complement identity is not
  assumed. `lean_pred(G,H) = ¬lean_hyp(G,H) ∨ lean_hyp(Gᶜ,Hᶜ)`.
- **English reading** (`en_pred`): deck as a multiset of canonical card forms
  (`small_graphs.hypomorphic`, i.e. `deck_key` equality), and complements from
  `networkx.complement`. `en_pred(G,H) = ¬same_deck(G,H) ∨ same_deck(Gᶜ,Hᶜ)`.

Scripts (scratch, not part of the repo):
`/tmp/claude-1000/-home-db-repositories-recon-conjecture/e6d4dcbf-445f-4ae9-8905-c3fde960a39c/scratchpad/fid_compl.py`
and `fid_labeled.py` in the same directory.

## Results

Exhaustive over all ordered pairs of isomorphism classes (networkx atlas), n = 0..6:

| n | graphs | pairs | hyp pairs | non-iso hyp pairs | conclusion-false pairs | Lean vs English diffs | lean_hyp vs deck diffs | Lean pred false |
|---|---|---|---|---|---|---|---|---|
| 0 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| 1 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| 2 | 2 | 4 | 4 | 2 | 0 | 0 | 0 | 0 |
| 3 | 4 | 16 | 4 | 0 | 12 | 0 | 0 | 0 |
| 4 | 11 | 121 | 11 | 0 | 110 | 0 | 0 | 0 |
| 5 | 34 | 1156 | 34 | 0 | 1122 | 0 | 0 | 0 |
| 6 | 156 | 24336 | 156 | 0 | 24180 | 0 | 0 | 0 |

Because the Lean statement quantifies over *labeled* graphs on `Fin n`, I also ran all labeled
graphs for n = 0..4 (1, 1, 2, 8, 64 graphs; all ordered pairs): 0 Lean/English differences, 0
pairs where the Lean predicate is false, and `card Gᶜ x` equals `(card G x)ᶜ` edge for edge in
every case.

## Failure-mode checklist

- **Vacuity:** the hypothesis holds. G = H always satisfies it (reflexivity anchor), and n = 2
  gives a non-isomorphic hypomorphic pair (K₂, 2K₁). Their complements (2K₁, K₂) are again
  hypomorphic, so the n = 2 edge case is consistent with the statement.
- **Trivially true conclusion?** No: `Hypomorphic Gᶜ Hᶜ` is false for most pairs (for example
  24180 of 24336 pairs at n = 6). The implication carries content through the hypothesis.
- **Missing n ≥ 3:** the English says "for every n", and the Lean has no bound either. This is
  correct: the claim holds for every n, including n = 0, 1, 2, so no bound is needed. Leaving it
  out makes the statement stronger, not weaker, and it is still true on every graph tested.
- **Fin n vs arbitrary types:** both readings use `Fin n` with the same n for G and H. That
  matches the English.
- **Notion of deck:** Lean uses the bijection-of-cards definition from `Basic.lean`. The
  `lean_hyp vs deck` column shows it agrees with multiset deck equality on every pair tested.
- **Complement:** Mathlib's `ᶜ` on `SimpleGraph` is the loopless complement, which matches the
  graph-theoretic complement. The test builds it literally.
- **Quantifiers and coercions:** there is no quantifier alternation beyond ∀ ∀ ∀ → . There are
  no coercions, and both Hypomorphic instances live at the same type `Fin n`.

No mismatch found.
