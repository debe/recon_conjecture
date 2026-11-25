import Mathlib
import Recon.Statements.S_kelly_edge_count

namespace Recon.Checked.L_kelly_edge_count

open SimpleGraph

lemma ncard_eq_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.edgeSet.ncard = H.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr e.mapEdgeSet

lemma card_edges_add_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n) :
    (Recon.card G x).edgeSet.ncard + G.degree x = G.edgeSet.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card' (Recon.card G x).edgeSet, Set.ncard_eq_toFinset_card' G.edgeSet]
  have h1 := card_edgeFinset_induce_compl_singleton G x
  have h2 := card_edgeFinset_deleteIncidenceSet G x
  have h3 : G.degree x ≤ G.edgeFinset.card := by
    rw [← card_incidenceFinset_eq_degree]
    exact Finset.card_le_card (G.incidenceFinset_subset x)
  simp only [edgeFinset] at h1 h2 h3
  have h4 : (Recon.card G x).edgeSet.toFinset.card = (G.induce {x}ᶜ).edgeSet.toFinset.card := rfl
  convert (show (G.induce {x}ᶜ).edgeSet.toFinset.card + G.degree x = G.edgeSet.toFinset.card by omega)

lemma sum_cards {n : ℕ} (G : SimpleGraph (Fin n)) :
    (∑ x, (Recon.card G x).edgeSet.ncard) + 2 * G.edgeSet.ncard = n * G.edgeSet.ncard := by
  classical
  have hs := G.sum_degrees_eq_twice_card_edges
  have hE : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']; rfl
  rw [← hE] at hs
  rw [← hs, ← Finset.sum_add_distrib]
  simp only [card_edges_add_degree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

end Recon.Checked.L_kelly_edge_count

theorem Recon.Checked.L_kelly_edge_count : Recon.Statements.S_kelly_edge_count := by
  intro n hn G H ⟨σ, hσ⟩
  have hG := Recon.Checked.L_kelly_edge_count.sum_cards G
  have hH := Recon.Checked.L_kelly_edge_count.sum_cards H
  have hsum : (∑ x, (Recon.card G x).edgeSet.ncard) = ∑ y, (Recon.card H y).edgeSet.ncard := by
    rw [← Equiv.sum_comp σ (fun y => (Recon.card H y).edgeSet.ncard)]
    exact Finset.sum_congr rfl (fun x _ =>
      Recon.Checked.L_kelly_edge_count.ncard_eq_of_iso (hσ x).some)
  rw [hsum] at hG
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have : (k + 1) * G.edgeSet.ncard = (k + 1) * H.edgeSet.ncard := by nlinarith
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) this
