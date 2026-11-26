import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_asymmetric
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric
import Recon.Checked.L_kelly_edge_count
import Recon.Checked.L_kelly_card_edges_add_degree

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_asymmetric

open SimpleGraph
open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric

lemma census_R {n : ℕ} {G H M : SimpleGraph (Fin n)} (σ : Fin n ≃ Fin n)
    (hσ : ∀ x, Nonempty (Recon.card G x ≃g Recon.card H (σ x))) (u v r s : Fin n) :
    {p : Fin n × Fin n | p.1 ≠ p.2 ∧ Nonempty (H.induce ({p.1, p.2}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n))) ∧ ¬ (p.1 ≠ p.2 ∧ ∃ e : H.induce ({p.1}ᶜ : Set (Fin n)) ≃g M.induce ({r}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = s) ∧ ¬ (p.1 ≠ p.2 ∧ ∃ x' y' : Fin n, (x' ≠ y' ∧ ∃ e : M.induce ({x'}ᶜ : Set (Fin n)) ≃g M.induce ({r}ᶜ : Set (Fin n)), ∀ z : ({x'}ᶜ : Set (Fin n)), z.1 = y' → (e z).1 = s) ∧ ∃ e : H.induce ({p.1}ᶜ : Set (Fin n)) ≃g M.induce ({y'}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = x')}.ncard =
    {p : Fin n × Fin n | p.1 ≠ p.2 ∧ Nonempty (G.induce ({p.1, p.2}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n))) ∧ ¬ (p.1 ≠ p.2 ∧ ∃ e : G.induce ({p.1}ᶜ : Set (Fin n)) ≃g M.induce ({r}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = s) ∧ ¬ (p.1 ≠ p.2 ∧ ∃ x' y' : Fin n, (x' ≠ y' ∧ ∃ e : M.induce ({x'}ᶜ : Set (Fin n)) ≃g M.induce ({r}ᶜ : Set (Fin n)), ∀ z : ({x'}ᶜ : Set (Fin n)), z.1 = y' → (e z).1 = s) ∧ ∃ e : G.induce ({p.1}ᶜ : Set (Fin n)) ≃g M.induce ({y'}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = x')}.ncard := by
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
    simp only [ptd_iff (hσ x).some y (Ne.symm hxy)]
    obtain ⟨R⟩ := restrict (hσ x).some y _ (Ne.symm hxy) rfl
    have : Nonempty (H.induce ({σ x, extE (hσ x).some y}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n))) ↔
        Nonempty (G.induce ({x, y}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n))) :=
      ⟨fun ⟨w⟩ => ⟨R.trans w⟩, fun ⟨w⟩ => ⟨R.symm.trans w⟩⟩
    rw [this]

open Classical in
lemma deg_rev {n : ℕ} (hn : 3 ≤ n) {G H : SimpleGraph (Fin n)} (hGH : Recon.Hypomorphic G H)
    {u v a b : Fin n} (hab : a ≠ b)
    (e1 : Recon.card H a ≃g Recon.card G u) (he1 : ∀ z : ({a}ᶜ : Set (Fin n)), z.1 = b → (e1 z).1 = v)
    (e2 : Recon.card H b ≃g Recon.card G u) :
    ((G.neighborSet v).ncard : ℤ) + (if H.Adj a b then 1 else 0) =
      ((G.neighborSet u).ncard : ℤ) + (if G.Adj u v then 1 else 0) := by
  have hba : b ≠ a := Ne.symm hab
  have h := deg_extE e1 b hba
  have hv : extE e1 b = v := by rw [extE_ne e1 hba]; exact he1 _ rfl
  rw [hv] at h
  have h2 := deg_T0 hn hGH e2
  rw [h2] at h
  exact h

lemma endgame {n : ℕ} (hn : 3 ≤ n) {G H : SimpleGraph (Fin n)} (hGH : Recon.Hypomorphic G H)
    {u v a b : Fin n} (huv : u ≠ v) (hab : a ≠ b)
    (e1 : Recon.card H a ≃g Recon.card G u) (he1 : ∀ z : ({a}ᶜ : Set (Fin n)), z.1 = b → (e1 z).1 = v)
    (f2 : Recon.card H b ≃g Recon.card G v) (hf2' : ∀ z : ({b}ᶜ : Set (Fin n)), z.1 = a → (f2 z).1 = u)
    (hd : ∀ g : G.induce ({u, v}ᶜ : Set (Fin n)) ≃g G.induce ({u, v}ᶜ : Set (Fin n)),
      ∀ x : ({u, v}ᶜ : Set (Fin n)), (G.neighborSet (g x).1).ncard = (G.neighborSet x.1).ncard) :
    Nonempty (G ≃g H) := by
  classical
  obtain ⟨σ, hσ⟩ := hGH
  have hGH : Recon.Hypomorphic G H := ⟨σ, hσ⟩
  have hvu : v ≠ u := Ne.symm huv
  have hba : b ≠ a := Ne.symm hab
  have hf2 : (f2 ⟨a, hab⟩).1 = u := hf2' _ rfl
  let Fu := extE e1.symm
  let Fv := extE f2.symm
  have hFuu : Fu u = a := extE_a _
  have hFuv : Fu v = b := extE_symm_eq e1 b v hba (he1 _ rfl)
  have hFvv : Fv v = b := extE_a _
  have hFvu : Fv u = a := extE_symm_eq f2 a u hab hf2
  have hFuadj : ∀ x y, x ≠ u → y ≠ u → (H.Adj (Fu x) (Fu y) ↔ G.Adj x y) := extE_adj e1.symm
  have hFvadj : ∀ x y, x ≠ v → y ≠ v → (H.Adj (Fv x) (Fv y) ↔ G.Adj x y) := extE_adj f2.symm
  let ψ : Fin n ≃ Fin n := Fu.trans Fv.symm
  have hψ : ∀ x, Fv (ψ x) = Fu x := fun x => by simp [ψ]
  have hψu : ψ u = u := Fv.injective (by rw [hψ, hFuu, hFvu])
  have hψv : ψ v = v := Fv.injective (by rw [hψ, hFuv, hFvv])
  have hψne : ∀ x, x ≠ u → x ≠ v → ψ x ≠ u ∧ ψ x ≠ v := by
    intro x hxu hxv
    exact ⟨fun h => hxu (ψ.injective (h.trans hψu.symm)), fun h => hxv (ψ.injective (h.trans hψv.symm))⟩
  have memS : ∀ x, x ∈ ({u, v}ᶜ : Set (Fin n)) ↔ x ≠ u ∧ x ≠ v := by intro x; simp
  have hψS : ∀ x, x ∈ ({u, v}ᶜ : Set (Fin n)) ↔ ψ x ∈ ({u, v}ᶜ : Set (Fin n)) := by
    intro x
    rw [memS, memS]
    constructor
    · rintro ⟨h1, h2⟩; exact hψne x h1 h2
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h, hψu]), fun h => h2 (by rw [h, hψv])⟩
  have hψadj : ∀ x y, x ∈ ({u, v}ᶜ : Set (Fin n)) → y ∈ ({u, v}ᶜ : Set (Fin n)) →
      (G.Adj (ψ x) (ψ y) ↔ G.Adj x y) := by
    intro x y hx hy
    rw [memS] at hx hy
    rw [← hFvadj (ψ x) (ψ y) (hψne x hx.1 hx.2).2 (hψne y hy.1 hy.2).2, hψ, hψ]
    exact hFuadj x y hx.1 hy.1
  let g := isoOn (G := G) (H := G) ψ _ _ hψS hψadj
  have hdψ : ∀ z, (G.neighborSet (ψ z)).ncard = (G.neighborSet z).ncard := by
    intro z
    by_cases hzu : z = u
    · rw [hzu, hψu]
    by_cases hzv : z = v
    · rw [hzv, hψv]
    exact hd g ⟨z, (memS z).2 ⟨hzu, hzv⟩⟩
  let d : Fin n → ℤ := fun z => ((G.neighborSet z).ncard : ℤ)
  let dH : Fin n → ℤ := fun z => ((H.neighborSet z).ncard : ℤ)
  let c : Fin n → ℤ := fun z => if G.Adj u z then 1 else 0
  have hadjψ : ∀ z, z ≠ u → z ≠ v → (H.Adj a (Fu z) ↔ G.Adj u (ψ z)) := by
    intro z hzu hzv
    rw [← hFvu, ← hψ]
    exact hFvadj u (ψ z) huv (hψne z hzu hzv).2
  have hdu : dH a = d u := by
    simp only [dH, d]; exact_mod_cast deg_T0 hn hGH e1
  have hdb : dH b = d v := by
    simp only [dH, d]; exact_mod_cast deg_T0 hn hGH f2
  have hdeg : ∀ z, dH (Fu z) = d z + c (ψ z) - c z := by
    intro z
    by_cases hzu : z = u
    · rw [hzu, hFuu, hψu, hdu]; ring
    by_cases hzv : z = v
    · rw [hzv, hFuv, hψv, hdb]; ring
    have h := deg_extE e1.symm z hzu
    have h2 : (if H.Adj a (extE e1.symm z) then (1:ℤ) else 0) = c (ψ z) := by
      simp only [c]
      rw [show extE e1.symm z = Fu z from rfl, hadjψ z hzu hzv]
    simp only [dH, d, c] at h h2 ⊢
    rw [h2] at h
    show _ = _ + (if G.Adj u (ψ z) then (1:ℤ) else 0) - _
    linarith
  have hsq : ∑ z, (dH (Fu z))^2 = ∑ z, (d z)^2 := by
    rw [Equiv.sum_comp Fu (fun w => (dH w)^2), ← Equiv.sum_comp σ (fun w => (dH w)^2)]
    apply Finset.sum_congr rfl
    intro z _
    simp only [dH, d]
    rw [deg_T0 hn hGH (hσ z).some.symm]
  have h2 : ∑ z, d z * c (ψ z) = ∑ z, d z * c z := by
    calc ∑ z, d z * c (ψ z) = ∑ z, d (ψ z) * c (ψ z) := by
          apply Finset.sum_congr rfl; intro z _; simp only [d]; rw [hdψ z]
      _ = ∑ w, d w * c w := Equiv.sum_comp ψ (fun w => d w * c w)
  have hε : ∀ z, c (ψ z) = c z := by
    have hexp : ∀ z, (d z + c (ψ z) - c z)^2 = (d z)^2 + 2 * (d z * c (ψ z)) - 2 * (d z * c z) + (c (ψ z) - c z)^2 := by
      intro z; ring
    simp_rw [hdeg, hexp] at hsq
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, h2] at hsq
    have h0 : ∑ z, (c (ψ z) - c z)^2 = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun z _ => sq_nonneg _)] at h0
    intro z
    have := h0 z (Finset.mem_univ z)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  have hkey : ∀ z, (H.Adj a (Fu z) ↔ G.Adj u z) := by
    intro z
    by_cases hzu : z = u
    · rw [hzu, hFuu]; simp
    have h : dH (Fu z) + c z = d z + (if H.Adj a (Fu z) then 1 else 0) := deg_extE e1.symm z hzu
    have hz := hdeg z
    rw [hε z] at hz
    have h4 : (if H.Adj a (Fu z) then (1:ℤ) else 0) = c z := by linarith
    simp only [c] at h4
    by_cases h1 : G.Adj u z <;> by_cases h3 : H.Adj a (Fu z) <;>
      simp only [h1, h3, ite_true, ite_false, iff_self, iff_false, false_iff, not_true] at h4 ⊢ <;> omega
  refine ⟨{ toEquiv := Fu, map_rel_iff' := ?_ }⟩
  intro x y
  show H.Adj (Fu x) (Fu y) ↔ G.Adj x y
  by_cases hx : x = u
  · rw [hx, hFuu]; exact hkey y
  by_cases hy : y = u
  · rw [hy, hFuu, H.adj_comm, G.adj_comm]; exact hkey x
  exact hFuadj x y hx hy

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_asymmetric

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_asymmetric : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_asymmetric := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_asymmetric in
  classical
  intro n hn G ⟨u, v, huv, hA1, hA0, hcount, hd⟩ H ⟨σ, hσ⟩
  have hGH : Recon.Hypomorphic G H := ⟨σ, hσ⟩
  rw [← census_A σ hσ u v, ← census_R σ hσ u v u v] at hcount
  have hex : ∃ a b : Fin n, a ≠ b ∧
      (∃ e : H.induce ({a}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)),
        ∀ z : ({a}ᶜ : Set (Fin n)), z.1 = b → (e z).1 = v) ∧
      (∃ x' y' : Fin n, (x' ≠ y' ∧ ∃ e : G.induce ({x'}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)),
        ∀ z : ({x'}ᶜ : Set (Fin n)), z.1 = y' → (e z).1 = v) ∧
        ∃ e : H.induce ({b}ᶜ : Set (Fin n)) ≃g G.induce ({y'}ᶜ : Set (Fin n)),
          ∀ z : ({b}ᶜ : Set (Fin n)), z.1 = a → (e z).1 = x') := by
    by_contra hne
    have hle := Set.ncard_le_ncard_of_injOn Prod.swap (fun p hp => ?_) Prod.swap_injective.injOn
      (Set.toFinite _) (s := {p : Fin n × Fin n | p.1 ≠ p.2 ∧ ∃ e : H.induce ({p.1}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = v})
      (t := {p : Fin n × Fin n | p.1 ≠ p.2 ∧ Nonempty (H.induce ({p.1, p.2}ᶜ : Set (Fin n)) ≃g G.induce ({u, v}ᶜ : Set (Fin n))) ∧ ¬ (p.1 ≠ p.2 ∧ ∃ e : H.induce ({p.1}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = v) ∧ ¬ (p.1 ≠ p.2 ∧ ∃ x' y' : Fin n, (x' ≠ y' ∧ ∃ e : G.induce ({x'}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)), ∀ z : ({x'}ᶜ : Set (Fin n)), z.1 = y' → (e z).1 = v) ∧ ∃ e : H.induce ({p.1}ᶜ : Set (Fin n)) ≃g G.induce ({y'}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = x')})
    · omega
    · obtain ⟨hp1, e, he⟩ := hp
      refine ⟨Ne.symm hp1, ?_, ?_, fun ⟨_, h⟩ => hne ⟨p.1, p.2, hp1, ⟨e, he⟩, h⟩⟩
      · obtain ⟨R⟩ := restrict e p.2 v (Ne.symm hp1) (by rw [extE_ne e (Ne.symm hp1)]; exact he _ rfl)
        show Nonempty (H.induce ({p.2, p.1}ᶜ : Set (Fin n)) ≃g G.induce ({u, v}ᶜ : Set (Fin n)))
        rw [Set.pair_comm]
        exact ⟨R⟩
      · rintro ⟨_, e2, _⟩
        have h := deg_rev hn hGH hp1 e he e2
        by_cases hG : G.Adj u v <;> by_cases hH : H.Adj p.1 p.2 <;>
          simp only [hG, hH, ite_true, ite_false] at h
        · have := hA1 hG; omega
        · have := hA1 hG; omega
        · have := hA0 hG; omega
        · have := hA0 hG; omega
  obtain ⟨a, b, hab, ⟨e1, he1⟩, x', y', ⟨hxy', e0, he0⟩, e2, he2⟩ := hex
  have hy' : y' ≠ x' := Ne.symm hxy'
  have he1' : ∀ z : ({a}ᶜ : Set (Fin n)), z.1 = b → ((e1.trans e0.symm) z).1 = y' := by
    intro z hz
    have h1 : e1 z = e0 ⟨y', hy'⟩ := Subtype.ext ((he1 z hz).trans (he0 _ rfl).symm)
    show (e0.symm (e1 z)).1 = y'
    rw [h1]
    simp
  exact endgame hn hGH hxy' hab (e1.trans e0.symm) he1' e2 he2 (hd x' y' ⟨hxy', e0, he0⟩)
