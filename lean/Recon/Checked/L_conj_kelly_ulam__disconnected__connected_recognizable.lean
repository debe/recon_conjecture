import Mathlib
import Recon.Statements.S_conj_kelly_ulam__disconnected__connected_recognizable

namespace Recon.Checked.L_conj_kelly_ulam__disconnected__connected_recognizable

open SimpleGraph

lemma reach_of_card {V : Type*} (G : SimpleGraph V) (a x c : V) (hx : x ≠ a) (hc : c ≠ a)
    (h : (G.induce ({a}ᶜ : Set V)).Connected) : G.Reachable x c := by
  have hr := h.preconnected ⟨x, hx⟩ ⟨c, hc⟩
  exact hr.map (Embedding.induce ({a}ᶜ : Set V)).toHom

lemma connected_of_two {V : Type*} (G : SimpleGraph V) (a b c : V) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b)
    (ha : (G.induce ({a}ᶜ : Set V)).Connected) (hb : (G.induce ({b}ᶜ : Set V)).Connected) :
    G.Connected := by
  have key : ∀ x, G.Reachable x c := by
    intro x
    by_cases hx : x = a
    · subst hx
      exact reach_of_card G b x c hab hcb hb
    · exact reach_of_card G a x c hx hca ha
  have : Nonempty V := ⟨c⟩
  exact ⟨fun x y => (key x).trans (key y).symm⟩

lemma two_cards {V : Type*} [Finite V] [Nontrivial V] (G : SimpleGraph V) (hconn : G.Connected) :
    ∃ u v : V, u ≠ v ∧ (G.induce ({u}ᶜ : Set V)).Connected ∧
      (G.induce ({v}ᶜ : Set V)).Connected := by
  obtain ⟨T, hTle, T_isTree⟩ := hconn.exists_isTree_le
  have := Fintype.ofFinite V
  classical
  obtain ⟨u, v, huv, hu, hv⟩ := T_isTree.exists_ne_and_degree_eq_one
  exact ⟨u, v, huv,
    (T_isTree.connected.induce_compl_singleton_of_degree_eq_one hu).mono (by tauto),
    (T_isTree.connected.induce_compl_singleton_of_degree_eq_one hv).mono (by tauto)⟩

lemma third (n : ℕ) (hn : 3 ≤ n) (a b : Fin n) : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b} := by
    intro c _
    by_cases hca : c = a
    · simp [hca]
    · simp [h c hca]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  have := Finset.card_le_two (a := a) (b := b)
  omega

lemma transfer (n : ℕ) (hn : 3 ≤ n) (G H : SimpleGraph (Fin n)) (σ : Fin n ≃ Fin n)
    (hσ : ∀ u : Fin n, G.induce ({u}ᶜ : Set (Fin n)) |>.Connected →
      (H.induce ({σ u}ᶜ : Set (Fin n))).Connected)
    (hG : G.Connected) : H.Connected := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨u, v, huv, hu, hv⟩ := two_cards G hG
  have hne : σ u ≠ σ v := fun h => huv (σ.injective h)
  obtain ⟨c, hca, hcb⟩ := third n hn (σ u) (σ v)
  exact connected_of_two H (σ u) (σ v) c hne hca hcb (hσ u hu) (hσ v hv)

end Recon.Checked.L_conj_kelly_ulam__disconnected__connected_recognizable

theorem Recon.Checked.L_conj_kelly_ulam__disconnected__connected_recognizable : Recon.Statements.S_conj_kelly_ulam__disconnected__connected_recognizable := by
  intro n hn G H ⟨σ, hσ⟩
  constructor
  · intro hG
    refine Recon.Checked.L_conj_kelly_ulam__disconnected__connected_recognizable.transfer n hn G H σ (fun u hu => ?_) hG
    obtain ⟨e⟩ := hσ u
    exact e.connected_iff.mp hu
  · intro hH
    refine Recon.Checked.L_conj_kelly_ulam__disconnected__connected_recognizable.transfer n hn H G σ.symm (fun u hu => ?_) hH
    obtain ⟨e⟩ := hσ (σ.symm u)
    rw [Equiv.apply_symm_apply] at e
    exact e.connected_iff.mpr hu
