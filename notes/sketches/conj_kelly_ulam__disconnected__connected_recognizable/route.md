# Route: connectedness is recognizable (n ≥ 3)

Sketch, not a result. Kelly (1957); see Bondy, *A graph reconstructor's manual* (1991), §on recognizable properties.

1. **Lemma A (connected ⇒ two connected cards).** G connected, n ≥ 2 ⇒ ∃ u ≠ v with
   `(G.induce {u}ᶜ).Connected` and `(G.induce {v}ᶜ).Connected`.
   Spanning tree `hconn.exists_isTree_le`, two distinct leaves (Mathlib
   `Acyclic.lean:537`, `IsTree` … `∃ u v, u ≠ v ∧ degree u = 1 ∧ degree v = 1`),
   `Connected.induce_compl_singleton_of_degree_eq_one` on the tree, then `.mono` up to G,
   exactly as in `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`
   (`Acyclic.lean:555`).
2. **Lemma B (two connected cards ⇒ connected), n ≥ 3.** a ≠ b, H − a and H − b connected.
   Pick c ∉ {a, b}. Every x ≠ a reaches c inside H − a; lift the walk with
   `(Embedding.induce _).toHom` / `Walk.map`. x = a: a ≠ b, so a reaches c inside H − b.
   Hence H preconnected, nonempty ⇒ connected.
3. **Transfer.** Hypomorphic G H gives σ with `card G x ≃g card H (σ x)`;
   `Iso.connected_iff` moves connectivity of a card. G connected ⇒ (A) u ≠ v ⇒ σ u ≠ σ v
   both with connected cards ⇒ (B) H connected. Converse by symmetry
   (`Recon.Checked.L_found_hypomorphic_symm` may be imported, or invert σ directly).
