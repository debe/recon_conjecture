# Fidelity review: found_reconstructible_compl (lens: testing, reviewer fid-testing)

Statement (sha256 1c4ea879...):
`∀ n : ℕ, ∀ G : SimpleGraph (Fin n), Recon.Reconstructible G ↔ Recon.Reconstructible Gᶜ`

English: "For every n and every graph G on Fin n: G is reconstructible if and only if its
complement is reconstructible."

## Predicates encoded

- **Lean reading (literal, from Basic.lean):**
  - `Hypomorphic G H`: some bijection σ : Fin n → Fin n has `card G x ≅ card H (σ x)` for
    every x. I brute-forced all n! permutations over a card-isomorphism matrix built with
    `nx.is_isomorphic`, independently of `canon`/`deck_key`.
  - `Reconstructible G`: every H on Fin n that is Hypomorphic to G is isomorphic to G.
    H ranges over all labeled graphs for n ≤ 4 (2^C(n,2) of them) and over the isomorphism
    representatives for n = 5 and 6. Both Hypomorphic and ≃g are invariant under
    relabeling H, so the representatives are enough.
  - `Gᶜ` is `nx.complement` on the same vertex set, i.e. the loopless Mathlib complement.
- **English reading:** the deck is the multiset of card isomorphism classes (`deck_key`).
  G is reconstructible when every graph with the same deck is isomorphic to G (`canon`).
  The claim is then recon(G) == recon(complement G).

## Results (all graphs, n = 0..6; script in the session scratchpad)

| n | graphs | H range | reconstructible | not |
|---|---|---|---|---|
| 0 | 1 | 1 labeled | 1 | 0 |
| 1 | 1 | 1 labeled | 1 | 0 |
| 2 | 2 | 2 labeled | 0 | 2 (K2, 2K1) |
| 3 | 4 | 8 labeled | 4 | 0 |
| 4 | 11 | 64 labeled | 11 | 0 |
| 5 | 34 | 34 reps | 34 | 0 |
| 6 | 156 | 156 reps | 156 | 0 |

- The Lean and English predicates for `Reconstructible` never differ on a single graph.
- The Lean and English truth values of the statement instance never differ on a single graph.
- The Lean statement instance never fails. Mismatches: none.

## Vacuity / triviality

- There is no hypothesis, so it cannot be vacuous. Neither side is constant:
  `Reconstructible` is false at n = 2 (K2 and 2K1 are complements of each other, so this
  checks false ↔ false) and true for every n ∈ {0, 1, 3..6}.
- The statement is not trivially true by its form. `Gᶜ` is the genuine complement, not G.
  Proving it needs card(Gᶜ, x) = (card G x)ᶜ, that complement preserves ≃g, and an
  application to Hᶜ.
- Having no n ≥ 3 hypothesis matches the English "for every n". The claim is true for
  n < 3 as well, and the table confirms this for n = 0, 1, 2.

## Failure-mode checklist

- **Quantifier order:** ∀ n ∀ G, then a biconditional. This matches the English.
- **Hypotheses:** nothing is missing or extra; an n ≥ 3 hypothesis is not needed.
- **Fin n:** matches the English, which says "graph G on Fin n". `Reconstructible` quantifies
  H over Fin n, which is the standard meaning.
- **Off-by-one:** there are no bounds.
- **Notion of deck / iso:** the bijection-of-cards definition agrees with multiset-of-classes
  on every tested pair.
- **Coercions:** none. `Gᶜ : SimpleGraph (Fin n)` uses Mathlib's `HasCompl`, which is irreflexive.

## Caveat on test power

The conjecture holds for n ≤ 13, so for n ≥ 3 both sides are always true and the
biconditional is only exercised as true ↔ true. At n = 2 it is exercised as false ↔ false.
The test therefore mainly confirms that the definitions agree; the statement's meaning is
also clear from direct reading.

Verdict: **pass**.
