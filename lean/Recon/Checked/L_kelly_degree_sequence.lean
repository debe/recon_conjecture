import Mathlib
import Recon.Statements.S_kelly_degree_sequence
import Recon.Checked.L_kelly_card_edges_add_degree
import Recon.Checked.L_kelly_edge_count

namespace Recon.Checked.L_kelly_degree_sequence

lemma ncard_eq_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.edgeSet.ncard = H.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr e.mapEdgeSet

end Recon.Checked.L_kelly_degree_sequence

theorem Recon.Checked.L_kelly_degree_sequence : Recon.Statements.S_kelly_degree_sequence := by
  intro n hn G H hGH
  have hE := Recon.Checked.L_kelly_edge_count n hn G H hGH
  obtain ⟨τ, hτ⟩ := hGH
  refine ⟨τ, fun v => ?_⟩
  have h1 := Recon.Checked.L_kelly_card_edges_add_degree n G v
  have h2 := Recon.Checked.L_kelly_card_edges_add_degree n H (τ v)
  have h3 := Recon.Checked.L_kelly_degree_sequence.ncard_eq_of_iso (hτ v).some
  omega
