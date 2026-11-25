# Route: Kelly's lemma, induced form

Sketch, not a result. Kelly (1957); Bondy (1991), Lemma "Kelly's lemma".

Let ind(F, G) = #{S : Finset V | G[S] ≃g F}, F on Fin k (forces |S| = k).
1. **Double count.** Σ_x #{S | x ∉ S, G[S] ≃g F} = (n − k) · ind(F, G), since each S with
   |S| = k misses exactly n − k vertices. With k < n, n − k > 0, so ind(F,G) is
   determined by the n per-vertex counts.
2. **Per-vertex count is a card invariant.** #{S | x ∉ S, G[S] ≃g F} = ind(F, card G x),
   via S ↦ S.subtype (or the image under `Subtype.val`), and `G.induce S ≃g
   (card G x).induce S'` (induce of induce; `SimpleGraph.induce`/`Embedding.induce`).
3. **Invariance under isomorphism.** e : A ≃g B ⇒ ind(F, A) = ind(F, B) (map S ↦ S.map e).
4. Hypomorphic σ: Σ_x ind(F, card G x) = Σ_x ind(F, card H (σ x)) = Σ_y ind(F, card H y)
   (`Equiv.sum_comp`). Divide by n − k.
Work with general `[Fintype V]` helpers; the cards live on `({x}ᶜ : Set V)`.
`Set.ncard` ↔ `Finset.card` via `Set.ncard_eq_toFinset_card'` / `Set.ncard_coe_finset`.
