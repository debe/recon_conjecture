# Fidelity review: discon_isolated_vertex (lens: testing, reviewer fid-testing)

Verdict: **pass**

## Statement under review

English: every graph on at least 3 vertices that has an isolated vertex is reconstructible.

Lean: `Recon.ClassReconstructible (fun n G => ∃ v : Fin n, ∀ w : Fin n, ¬ G.Adj v w)`.

When `ClassReconstructible`, `Reconstructible` and `Hypomorphic` from `Basic.lean` are unfolded, this reads:
for all n ≥ 3 and every G : SimpleGraph (Fin n) that has a vertex v with no neighbour, every
H : SimpleGraph (Fin n) with a vertex bijection σ such that each card G − x ≅ H − σx is isomorphic to G.

## Encoded predicates

The check script is `notes/sketches/discon_isolated_vertex/fidelity_fid-testing_check.py`. It uses
`tools/search/small_graphs.py` as a library.

- `lean_C(n, G)`: `any(all(not G.has_edge(v, w) for w in range(n)) for v in range(n))`, read literally from the Lean.
- `en_C(n, G)`: `any(G.degree(v) == 0 ...)`, read from the English "a vertex adjacent to no vertex".
- Scope: Lean `3 ≤ n` (from `ClassReconstructible`) against English "at least 3 vertices".

## Results

1. **Class predicate, all labelled graphs n = 0..6:** 0 differences across 33,868 labelled graphs.
   The counts where the predicate holds are n=3: 4/8, n=4: 23/64, n=5: 256/1024 and n=6: 5319/32768.
   Labelled graphs are used because the Lean quantifies over labelled graphs on `Fin n`. The
   `w = v` case is harmless because `SimpleGraph` is loopless.
2. **Scope:** the two readings agree for n = 0..9. The guard is `3 ≤ n`, with no off-by-one.
3. **Whole statement, unlabelled classes n = 0..6:** the Lean reading and the English reading
   give the same truth value at every n, and both hold.
   - The members per n are 1, 2, 4, 11 and 34 for n = 2..6. These equal the number of graphs
     on n − 1 vertices, as expected.
   - Each member's deck class is a singleton.
4. **The guard is load-bearing:** at n = 2, 2K₁ has an isolated vertex and is hypomorphic to K₂,
   but the two are not isomorphic. The statement would be false without `3 ≤ n`, and that
   hypothesis is present.

## Vacuity and triviality

- **Not vacuous:** the hypothesis holds for many graphs at every n ≥ 3 (see the counts above).
- **Not trivially true:** members are not limited to the edgeless graph. There are 1, 3, 10
  and 33 members with edges for n = 3..6.
- The conclusion quantifies over **all** H on `Fin n`, not only H in the class. This is the
  correct, strong notion of reconstructibility.

## Failure-mode checklist

- Quantifier order: correct (∃ v ∀ w).
- `Fin n`: this follows the project convention. A deck determines n, so restricting H to
  `Fin n` loses nothing.
- Isomorphism and deck: these use the trusted `Hypomorphic` (a bijection matching cards up to
  isomorphism), which is equivalent to equality of decks as multisets. The conclusion uses
  `Nonempty (G ≃g H)`, which is the correct notion.
- Coercions: none.

No mismatch found.
