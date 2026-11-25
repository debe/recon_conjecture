# Fidelity review: kelly_degree_sequence (lens: back-translation, reviewer fid-backtranslate)

Verdict: PASS

## 1. Independent back-translation (written before reading statement_en)

Lean:
`∀ n : ℕ, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H →
 ∃ σ : Fin n ≃ Fin n, ∀ v : Fin n, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard`

Expanding `Recon.Hypomorphic` and `Recon.card` (Basic.lean):
`Hypomorphic G H := ∃ τ : Fin n ≃ Fin n, ∀ x, Nonempty (G.induce {x}ᶜ ≃g H.induce {τ x}ᶜ)`.

My reading: For every natural number n with n ≥ 3, and all simple graphs G, H on the vertex
set {0, …, n−1}: if there is a bijection τ of the vertices such that for every vertex x the
vertex-deleted induced subgraph G − x is isomorphic to H − τ(x), then there is a bijection σ
of the vertices (possibly different from τ) such that for every vertex v, the number of
neighbours of v in G equals the number of neighbours of σ(v) in H. Equivalently: hypomorphic
graphs on n ≥ 3 vertices have the same multiset of vertex degrees (same degree sequence).

## 2. Clause-by-clause comparison with statement_en

| English clause | Lean | Match |
|---|---|---|
| for every n at least 3 | `∀ n : ℕ, 3 ≤ n →` | yes (≤, not <; n = 3 included) |
| all graphs G, H on Fin n | `∀ G H : SimpleGraph (Fin n)` | yes; both on the same Fin n |
| G and H hypomorphic | `Recon.Hypomorphic G H` | yes; trusted definition, standard (Bondy–Hemminger) |
| some bijection σ of the vertices | `∃ σ : Fin n ≃ Fin n` | yes; existential, chosen after G, H |
| deg_G(v) = deg_H(σ v) for every v | `∀ v, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard` | yes |
| degrees counted as number of neighbours | `neighborSet … .ncard` | yes |

## 3. Failure-mode checklist

- Quantifier order/scope: σ is existential under ∀ n G H and the hypothesis; ∀ v is inside ∃ σ.
  This is exactly "same degree multiset". Correct.
- n ≥ 3 present. It is load-bearing: at n = 2, K₂ and 2K₁ are hypomorphic
  (`anchor_two_vertices_hypomorphic`) but degree sequences (1,1) vs (0,0) differ, so
  without it the statement would be false.
- Fin n vs arbitrary types: same as English ("graphs on Fin n"); consistent with the
  repository convention for headline statements.
- ncard coercion: `neighborSet v` is a subset of the finite type `Fin n`, so it is finite and
  `Set.ncard` equals the true neighbour count (the infinite-set junk value 0 never arises).
  It equals Mathlib's `G.degree v` for any Fintype instance; using ncard avoids
  DecidableRel instance dependence. No meaning change.
- Vacuity: hypothesis satisfiable (e.g. H = G, `anchor_hypomorphic_refl`). Not trivially
  true: the conclusion fails for non-hypomorphic pairs (e.g. K₃ vs empty on Fin 3), so
  the hypomorphism hypothesis does real work.
- Notion of deck/iso: inherited from trusted `Hypomorphic` (induced vertex-deleted cards,
  graph isos `≃g`, Nonempty — correct, an iso only needs to exist).
- Weaker-than-ideal? The statement does not require σ = τ (the hypomorphism bijection).
  The English also only says "some bijection", so this matches. (Note for builders: the
  standard proof deg v = |E| − |E(G − v)| actually gives σ = τ, so the statement is
  provable along the cited route.)
- Truth: standard result (Kelly 1957; cited Bondy–Murty GTM 244 Cor. 2.22 — citation not
  re-verified by this reviewer, UNVERIFIED). The mathematical content is the textbook
  argument above; no reason to suspect falsity.

## 4. Conclusion

The Lean statement says exactly what statement_en says: hypomorphic graphs on n ≥ 3
vertices have equal degree sequences, expressed as a degree-preserving vertex bijection.
No mismatch found.
