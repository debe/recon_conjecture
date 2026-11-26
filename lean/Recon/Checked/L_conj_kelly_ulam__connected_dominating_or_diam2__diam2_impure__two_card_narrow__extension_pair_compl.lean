import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_pair_compl

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_pair_compl

theorem card_compl_iso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (x : V) (y : W)
    (e : Recon.card G x ≃g Recon.card H y) : Nonempty (Recon.card Gᶜ x ≃g Recon.card Hᶜ y) := by
  refine ⟨{ toEquiv := e.toEquiv, map_rel_iff' := ?_ }⟩
  intro a b
  have h1 : (Recon.card H y).Adj (e a) (e b) ↔ (Recon.card G x).Adj a b := e.map_rel_iff
  have h2 : e a = e b ↔ a = b := e.injective.eq_iff
  show (Hᶜ).Adj (e a).1 (e b).1 ↔ (Gᶜ).Adj a.1 b.1
  change H.Adj (e a).1 (e b).1 ↔ G.Adj a.1 b.1 at h1
  rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj, h1, Ne, Ne, ← Subtype.ext_iff,
    ← Subtype.ext_iff, h2]

theorem hyp_compl {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Recon.Hypomorphic G H) : Recon.Hypomorphic Gᶜ Hᶜ := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun x => ?_⟩
  obtain ⟨e⟩ := hσ x
  exact card_compl_iso G H x (σ x) e

theorem ncard_compl {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) :
    (Gᶜ.neighborSet x).ncard + (G.neighborSet x).ncard + 1 = n := by
  rw [SimpleGraph.neighborSet_compl]
  have hx : x ∈ (G.neighborSet x)ᶜ := by simp
  have h1 := Set.ncard_sdiff_singleton_add_one hx
  have h2 := Set.ncard_add_ncard_compl (G.neighborSet x)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  omega

theorem iso_of_compl {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : Gᶜ ≃g Hᶜ) : Nonempty (G ≃g H) := by
  refine ⟨{ toEquiv := e.toEquiv, map_rel_iff' := ?_ }⟩
  intro a b
  have h1 : Hᶜ.Adj (e a) (e b) ↔ Gᶜ.Adj a b := e.map_rel_iff
  have h2 : e a = e b ↔ a = b := e.injective.eq_iff
  rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj] at h1
  show H.Adj (e a) (e b) ↔ G.Adj a b
  by_cases hab : a = b
  · subst hab; simp
  · have hne : e a ≠ e b := fun h => hab (h2.1 h)
    tauto

theorem agree_compl {n : ℕ} {G K : SimpleGraph (Fin n)} {u : Fin n}
    (h : ∀ x y : Fin n, x ≠ u → y ≠ u → (G.Adj x y ↔ K.Adj x y)) :
    ∀ x y : Fin n, x ≠ u → y ≠ u → (Gᶜ.Adj x y ↔ Kᶜ.Adj x y) := by
  intro x y hx hy
  rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj, h x y hx hy]

theorem main : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_pair_compl := by
  intro hyp n hn d G H hNF hcard hhyp hni u K₁ K₂ K₃ k1 k2 k3 a1 a2 a3
  rcases hNF u with hu | hu
  · exact hyp n hn d G H hNF hcard hhyp hni u hu K₁ K₂ K₃ k1 k2 k3 a1 a2 a3
  · have hcu := ncard_compl G u
    have key := hyp n hn (n - 2 - d) Gᶜ Hᶜ ?_ ?_ (hyp_compl hhyp) ?_ u ?_ K₁ᶜ K₂ᶜ K₃ᶜ
      (hyp_compl k1) (hyp_compl k2) (hyp_compl k3) (agree_compl a1) (agree_compl a2)
      (agree_compl a3)
    · rcases key with h | h | h
      · exact Or.inl (compl_injective h)
      · exact Or.inr (Or.inl (compl_injective h))
      · exact Or.inr (Or.inr (compl_injective h))
    · intro x
      have hcx := ncard_compl G x
      rcases hNF x with hx | hx
      · right; omega
      · left; omega
    · intro x y hxy
      have hcx := ncard_compl G x
      have hcy := ncard_compl G y
      obtain ⟨e⟩ := hcard x y (by omega)
      exact card_compl_iso G G x y e
    · rintro ⟨e⟩
      exact hni (iso_of_compl e)
    · omega

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_pair_compl

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_pair_compl : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_pair_compl :=
  Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_pair_compl.main
