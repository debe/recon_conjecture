import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__slice_determined
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__unique_switch

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__slice_determined

open SimpleGraph
open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric

lemma census_F {n : ℕ} {G H M : SimpleGraph (Fin n)} (σ : Fin n ≃ Fin n)
    (hσ : ∀ x, Nonempty (Recon.card G x ≃g Recon.card H (σ x))) (u v : Fin n) :
    {p : Fin n × Fin n | p.1 ≠ p.2 ∧ Nonempty (H.induce ({p.1, p.2}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n)))}.ncard =
    {p : Fin n × Fin n | p.1 ≠ p.2 ∧ Nonempty (G.induce ({p.1, p.2}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n)))}.ncard := by
  classical
  let Φ := pairEquiv σ (fun x => extE (hσ x).some)
  rw [← Set.ncard_preimage_of_injective_subset_range Φ.injective (by simp)]
  congr 1
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Φ, pairEquiv, Equiv.coe_fn_mk]
  by_cases hxy : x = y
  · subst hxy
    simp [extE_a]
  · rw [ne_iff]
    obtain ⟨R⟩ := restrict (hσ x).some y _ (Ne.symm hxy) rfl
    have : Nonempty (H.induce ({σ x, extE (hσ x).some y}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n))) ↔
        Nonempty (G.induce ({x, y}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n))) :=
      ⟨fun ⟨w⟩ => ⟨R.trans w⟩, fun ⟨w⟩ => ⟨R.symm.trans w⟩⟩
    rw [this]

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__slice_determined

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__slice_determined : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__slice_determined := by
  intro n hn G hG H hGH
  obtain ⟨u, v, _, hK⟩ := hG
  obtain ⟨σ, hσ⟩ := hGH
  have hGH : Recon.Hypomorphic G H := ⟨σ, hσ⟩
  have hdeg : ∀ x, (G.neighborSet x).ncard = (H.neighborSet (σ x)).ncard :=
    fun x => (Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.deg_T0 hn hGH (hσ x).some.symm).symm
  refine hK H ⟨σ, fun x => ⟨hdeg x, ?_⟩⟩ ?_ ?_
  · have h := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__unique_switch.w2_tied G H σ (fun x => (hσ x).some) (fun x => by
      unfold Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__unique_switch.dg
      exact_mod_cast hdeg x) x
    exact h.symm
  · intro r s _ _
    exact Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.census_A σ hσ r s
  · exact Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__slice_determined.census_F σ hσ u v
