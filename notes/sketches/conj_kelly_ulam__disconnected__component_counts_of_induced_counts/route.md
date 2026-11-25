# Route: induced counts ⇒ component counts (disconnected G, H)

Sketch, not a result. Kelly (1957); the standard triangular solve (Bondy 1991, disconnected graphs).

Notation: ind(F, A) = #{S | A[S] ≃g F}; comp(F, A) = #{c : A.ConnectedComponent | A[c.supp] ≃g F}.

**Reuse the checked siblings (import them):**
- `Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count`: `ind`, `ind_iso`
  (isomorphic graphs have equal ind), `isoInduce`.
- `Recon.Checked.L_conj_kelly_ulam__disconnected__iso_of_component_counts`: `match_fibres`
  (equal fibre sizes of an equivalence relation ⇒ bijection α ≃ β respecting s), and the
  transport of a component to `Fin k` (`Iso.map` + `Fintype.equivFin`, connected by
  `ConnectedComponent.connected_toSimpleGraph`/`Iso.connected_iff`). Copy what is private.

1. **Decomposition.** For connected F: ind(F, G) = Σ_c ind(F, G[c.supp]). An S with G[S] ≃g F
   connected is nonempty and its vertices are pairwise reachable, so S ⊆ one c.supp; and an
   induced copy inside G[c.supp] is an induced copy in G (induce of induce).
2. **Split by size.** Components with |c.supp| < k contribute 0; |c.supp| = k contribute
   [G[c.supp] ≃g F] (an S of size k in a k-set is the whole set); so
   ind(F, G) = comp(F, G) + Σ_{c, |c.supp| > k} ind(F, G[c.supp]).
3. **Large sizes.** P(m) := ∀ F connected on Fin m, comp(F,G) = comp(F,H).
   For m ≥ n, P(m) holds since both counts are 0: a component with |supp| ≥ n has supp = univ,
   so G (or H) would be connected, contradicting the hypothesis.
4. **Downward strong induction on k** (e.g. on n − k). Given P(m) for all m > k, `match_fibres`
   gives a bijection between components of size > k in G and in H with G[c] ≃g H[φ c];
   `ind_iso` makes the two tail sums in (2) equal termwise. The hypothesis gives
   ind(F,G) = ind(F,H) for k < n, so comp(F,G) = comp(F,H): P(k).
Convert the `Set.ncard` in the statement with `Set.ncard_coe_finset` / `Set.ncard_eq_toFinset_card'`.
