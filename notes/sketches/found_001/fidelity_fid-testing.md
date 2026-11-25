# Fidelity review: found_001 (lens: testing), reviewer fid-testing

Statement (Lean): `∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Nonempty (G ≃g H) → Recon.Hypomorphic G H`
English: "For every n and all graphs G, H on Fin n: if G and H are isomorphic, then G and H
have the same deck (are hypomorphic)."

## Predicates (script: `notes/sketches/found_001/fidelity_fid-testing.py`)

- **Lean reading.** `lean_stmt(G,H) = ¬iso(G,H) ∨ lean_hypomorphic(G,H)`. Here
  `lean_hypomorphic` is a literal encoding of `Recon.Hypomorphic`. It uses backtracking to
  search for a bijection σ : V → W with `card G x ≅ card H (σ x)` for every x. A card is the
  induced subgraph on `{x}ᶜ` and keeps its original labels, as the Lean subtype does.
  Isomorphism is `nx.is_isomorphic`.
- **English reading.** `english_stmt(G,H) = ¬iso(G,H) ∨ same_deck(G,H)`. Here `same_deck`
  compares the multisets of isomorphism classes of cards, using greedy class matching with
  `nx.is_isomorphic`. It does not use `canon`. The script also cross-checks the tool's
  `small_graphs.hypomorphic` (deck_key).

## Runs (all n = 0..6, atlas via `small_graphs.all_graphs`)

1. **Statement comparison on labeled pairs.** For each G, H ranges over relabelings of G
   (every permutation for n ≤ 5, the identity plus 40 random permutations for n = 6).
   Total: 10770 labeled pairs, and the hypothesis holds on every one of them.
   Disagreements between lean_stmt and english_stmt: **0**. Pairs where either is false: **0**.
2. **Definition comparison.** `Recon.Hypomorphic` was compared with "same multiset deck"
   on every ordered pair of unlabeled graphs, with H randomly relabeled: 25635 pairs.
   Disagreements: **0**. deck_key also agrees everywhere. There are 211 hypomorphic pairs.
   Only 2 of them are non-isomorphic, both at n = 2 (K₂ against 2K₁, in both orders). This
   matches the Basic.lean anchor and McKay's verification for 3 ≤ n ≤ 6. So the Lean
   definition is neither trivially true nor just isomorphism.
3. **Non-isomorphic pairs.** Both statement predicates are vacuously true there, so the
   two readings cannot differ on them.

## Vacuity and triviality

- The hypothesis `Nonempty (G ≃g H)` is satisfiable, for example with G = H. It held on all
  10770 test pairs, so the statement is not vacuous.
- The conclusion is not trivially true: `Hypomorphic` fails on 25635 − 211 = 25424 of the
  definition-test pairs.
- The statement is an easy result, but it is the intended one. It is the first `found`
  target in CLAUDE.md §10.

## Failure-mode checklist

- **Quantifiers.** n, G and H are all universal, and the implication sits inside them.
  This matches the English.
- **No n ≥ 3 hypothesis.** This is correct. Isomorphic ⇒ hypomorphic holds for every n,
  including 0, 1 and 2, as the tests confirm. The English says "for every n".
- **Vertex type.** Both G and H live on `Fin n`, as the English says.
- **Isomorphism.** `≃g` is Mathlib's graph isomorphism (`RelIso` on `Adj`). Wrapping it in
  `Nonempty` correctly expresses "are isomorphic".
- **Deck.** `Hypomorphic` (∃ bijection matching cards up to isomorphism) agrees with
  multiset deck equality on all 25635 tested pairs. These are equivalent in general,
  because a bijection between card lists that respects an equivalence relation exists iff
  the class multisets coincide.
- **Coercions.** The only coercion is the `{x}ᶜ` subtype in `card`, and it is harmless.

## Verdict: PASS

No mismatch was found between the Lean statement and its English.

Side observation, not a fidelity issue: `desk.py status` already shows `human_approved:
true` with `approved_by: debe` while the step is `proposed` with no fidelity records yet.
The human may want to confirm that this ordering is intended.
