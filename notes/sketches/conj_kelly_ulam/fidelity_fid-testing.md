# Fidelity review: conj_kelly_ulam (lens: testing), reviewer fid-testing

Verdict: **pass**

## Statement under review
- Lean: `S_conj_kelly_ulam := Recon.ReconstructionConjecture`, which unfolds to
  `∀ n : ℕ, 3 ≤ n → ∀ G : SimpleGraph (Fin n), ∀ H : SimpleGraph (Fin n),
   (∃ σ : Fin n ≃ Fin n, ∀ x, Nonempty (G.induce {x}ᶜ ≃g H.induce {σ x}ᶜ)) → Nonempty (G ≃g H)`.
- English: "Every graph on at least 3 vertices is reconstructible", i.e. Kelly–Ulam:
  if two finite simple graphs on n ≥ 3 vertices have the same deck (the same multiset of
  vertex-deleted subgraphs up to isomorphism), then they are isomorphic.

## Predicates encoded
Script: `notes/sketches/conj_kelly_ulam/fid_testing_script.py`.
- Lean reading, written independently of the tool's canonical forms: the card is the induced
  subgraph on V \ {x} (labels kept); `Hypomorphic` = brute force over all n! bijections σ,
  checking `nx.is_isomorphic(card G x, card H σx)` for every x; conclusion = `nx.is_isomorphic(G, H)`;
  statement at n holds iff `3 ≤ n` is false or every G is reconstructible.
- English reading: deck = sorted multiset of canonical cards (`small_graphs.hypomorphic`,
  using `small_graphs.canon`); reconstructible = every graph with the same deck is isomorphic;
  statement at n holds iff n < 3 or every graph is reconstructible.

## Results (all graphs up to isomorphism, n = 0..6, all ordered pairs (G, H))
| n | graphs | hypomorphic pairs | hypomorphic non-iso pairs | all reconstructible |
|---|---|---|---|---|
| 0 | 1 | 1 | 0 | yes |
| 1 | 1 | 1 | 0 | yes |
| 2 | 2 | 4 | 2 | **no** (K2 vs 2K1) |
| 3 | 4 | 4 | 0 | yes |
| 4 | 11 | 11 | 0 | yes |
| 5 | 34 | 34 | 0 | yes |
| 6 | 156 | 156 | 0 | yes |

- Pairwise mismatches between Lean `Hypomorphic` and English deck equality: **0**.
- Per-graph mismatches in reconstructibility: **0**. Statement-level mismatches per n: **0**.
- Lean quantifies over all *labelled* H on `Fin n`, not iso classes. Checked directly on all
  labelled graphs for n ≤ 4 (64 graphs at n = 4, 4096 ordered pairs): 0 mismatches and no
  hypomorphic non-isomorphic labelled pair for n ≥ 3.

## Failure modes checked
- **Vacuity / triviality.** The hypothesis `Hypomorphic G H` is satisfiable (H = G always; at
  n = 4 there are 556 hypomorphic labelled pairs, many with H ≠ G). It is not trivially true:
  at n = 6 only 156 of 24336 iso-class pairs are hypomorphic. The conclusion is not trivially
  true either: at n = 2 the predicate genuinely fails (K2, 2K1), which also shows the test
  would detect a `2 ≤ n` mutant.
- **n ≥ 3 / off-by-one.** `3 ≤ n` matches "at least 3 vertices"; n = 2 is excluded exactly
  where it must be, and n = 0, 1 are included harmlessly (both readings agree, true there).
- **Quantifier order.** ∀ n, ∀ G, ∀ H, (hyp → iso); no existential leaks; σ is existential
  inside the hypothesis, as the deck definition requires.
- **Deck notion.** Bijection-matching of cards ⇔ equality of card multisets up to iso
  (confirmed empirically above; also immediate mathematically). It is the multiset deck,
  not the set deck (set reconstruction would be a different conjecture).
- **Fin n vs arbitrary types.** Every finite simple graph is isomorphic to one on `Fin n`, and
  both `Hypomorphic` and `≃g` are invariant under relabelling, so restricting to `Fin n`
  loses nothing. Infinite graphs are excluded, as they must be (Fisher 1969 counterexamples).
- **Nonempty vs structure.** `Nonempty (G ≃g H)` is the right Prop-level "isomorphic".
- **Isomorphism notion.** `≃g` is Mathlib graph isomorphism (adjacency-preserving bijection),
  the same notion `nx.is_isomorphic` checks.

## Minor remark (not a mismatch)
The English text is partly self-referential ("exactly Recon.ReconstructionConjecture as defined
in Basic.lean"). Its first clause is the standard statement and matches the Lean, so this does
not affect fidelity.

Known fact used only for context: the conjecture holds for n ≤ 13 (McKay), consistent with
"all reconstructible" for n = 3..6 above; the test does not rely on it.
