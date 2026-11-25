import Mathlib
import Recon.Statements.S_discon_isolated_vertex
import Recon.Checked.L_kelly_edge_count
import Recon.Checked.L_kelly_card_edges_add_degree

namespace Recon.Checked.L_discon_isolated_vertex

open SimpleGraph

lemma iso_of_card_iso_of_isolated {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v : V} {w : W} (hv : ∀ x, ¬ G.Adj v x) (hw : ∀ y, ¬ H.Adj w y)
    (e : Recon.card G v ≃g Recon.card H w) : Nonempty (G ≃g H) := by
  classical
  let f : V → W := fun x => if h : x = v then w else (e ⟨x, h⟩ : W)
  let g : W → V := fun y => if h : y = w then v else (e.symm ⟨y, h⟩ : V)
  have hf : ∀ x (h : ¬ x = v), f x = (e ⟨x, h⟩ : W) := fun x h => dite_eq_right h
  have hg : ∀ y (h : ¬ y = w), g y = (e.symm ⟨y, h⟩ : V) := fun y h => dite_eq_right h
  have hfv : f v = w := dite_eq_left rfl
  have hgw : g w = v := dite_eq_left rfl
  have hgf : ∀ x, g (f x) = x := by
    intro x
    by_cases h : x = v
    · subst h; rw [hfv, hgw]
    · have h2 : ¬ f x = w := by rw [hf x h]; exact (e ⟨x, h⟩).2
      rw [hg _ h2]
      have : (⟨f x, h2⟩ : ({w}ᶜ : Set W)) = e ⟨x, h⟩ := Subtype.ext (hf x h)
      rw [this, RelIso.symm_apply_apply]
  have hfg : ∀ y, f (g y) = y := by
    intro y
    by_cases h : y = w
    · subst h; rw [hgw, hfv]
    · have h2 : ¬ g y = v := by rw [hg y h]; exact (e.symm ⟨y, h⟩).2
      rw [hf _ h2]
      have : (⟨g y, h2⟩ : ({v}ᶜ : Set V)) = e.symm ⟨y, h⟩ := Subtype.ext (hg y h)
      rw [this, RelIso.apply_symm_apply]
  refine ⟨{ toEquiv := ⟨f, g, hgf, hfg⟩, map_rel_iff' := ?_ }⟩
  intro a b
  change H.Adj (f a) (f b) ↔ G.Adj a b
  by_cases ha : a = v
  · subst ha
    rw [hfv]
    exact ⟨fun h => (hw _ h).elim, fun h => (hv _ h).elim⟩
  · by_cases hb : b = v
    · subst hb
      rw [hfv]
      exact ⟨fun h => (hw _ h.symm).elim, fun h => (hv _ h.symm).elim⟩
    · rw [hf a ha, hf b hb]
      exact e.map_rel_iff (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)

end Recon.Checked.L_discon_isolated_vertex

theorem Recon.Checked.L_discon_isolated_vertex : Recon.Statements.S_discon_isolated_vertex := by
  intro n hn G ⟨v, hv⟩ H ⟨σ, hσ⟩
  obtain ⟨e⟩ := hσ v
  have hE := Recon.Checked.L_kelly_edge_count n hn G H ⟨σ, hσ⟩
  have hG := Recon.Checked.L_kelly_card_edges_add_degree n G v
  have hH := Recon.Checked.L_kelly_card_edges_add_degree n H (σ v)
  have hc := Recon.Checked.L_kelly_edge_count.ncard_eq_of_iso e
  have hGv : (G.neighborSet v).ncard = 0 := by
    have h0 : G.neighborSet v = ∅ := Set.eq_empty_of_forall_notMem (fun x hx => hv x hx)
    rw [h0, Set.ncard_empty]
  have hHv : (H.neighborSet (σ v)).ncard = 0 := by omega
  have hw : ∀ y, ¬ H.Adj (σ v) y := by
    intro y hy
    rw [Set.ncard_eq_zero (Set.toFinite _)] at hHv
    have hy' : y ∈ H.neighborSet (σ v) := hy
    rw [hHv] at hy'
    exact hy'
  exact Recon.Checked.L_discon_isolated_vertex.iso_of_card_iso_of_isolated hv hw e
