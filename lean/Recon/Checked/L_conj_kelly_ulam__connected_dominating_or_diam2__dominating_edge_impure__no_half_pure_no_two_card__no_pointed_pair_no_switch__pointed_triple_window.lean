import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__pointed_triple_window
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__pointed_triple_window

open SimpleGraph
open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric

/-- Triples whose doubly pointed card in K matches (M - u; v, w). -/
def Aset {n : ℕ} (K M : SimpleGraph (Fin n)) (u v w : Fin n) : Set (Fin n × Fin n × Fin n) :=
  {p : Fin n × Fin n × Fin n | p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧ ∃ e : K.induce ({p.1}ᶜ : Set (Fin n)) ≃g M.induce ({u}ᶜ : Set (Fin n)), ∀ t : ({p.1}ᶜ : Set (Fin n)), (t.1 = p.2.1 → (e t).1 = v) ∧ (t.1 = p.2.2 → (e t).1 = w)}

/-- The remainder set of the window census. -/
def Rset {n : ℕ} (K M : SimpleGraph (Fin n)) (u v w : Fin n) : Set (Fin n × Fin n × Fin n) :=
  {p : Fin n × Fin n × Fin n | p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧ (∃ e : K.induce ({p.1, p.2.1}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n)), ∀ t : ({p.1, p.2.1}ᶜ : Set (Fin n)), t.1 = p.2.2 → (e t).1 = w) ∧ (M.Adj u v → ((K.neighborSet p.1).ncard + 1 = (M.neighborSet v).ncard ∨ (K.neighborSet p.1).ncard = (M.neighborSet v).ncard)) ∧ (¬ M.Adj u v → ((K.neighborSet p.1).ncard = (M.neighborSet v).ncard ∨ (K.neighborSet p.1).ncard = (M.neighborSet v).ncard + 1)) ∧ ¬ ∃ x' y' z' : Fin n, (x' ≠ y' ∧ x' ≠ z' ∧ y' ≠ z' ∧ ∃ e : M.induce ({x'}ᶜ : Set (Fin n)) ≃g M.induce ({u}ᶜ : Set (Fin n)), ∀ t : ({x'}ᶜ : Set (Fin n)), (t.1 = y' → (e t).1 = v) ∧ (t.1 = z' → (e t).1 = w)) ∧ ∃ e : K.induce ({p.1}ᶜ : Set (Fin n)) ≃g M.induce ({y'}ᶜ : Set (Fin n)), ∀ t : ({p.1}ᶜ : Set (Fin n)), (t.1 = p.2.1 → (e t).1 = x') ∧ (t.1 = p.2.2 → (e t).1 = z')}

lemma extE_coe {V W : Type*} [DecidableEq V] [DecidableEq W] {K : SimpleGraph V}
    {L : SimpleGraph W} {p : V} {q : W} (f : Recon.card K p ≃g Recon.card L q)
    (t : ({p}ᶜ : Set V)) : extE f t.1 = (f t).1 := extE_ne f t.2

lemma ptd2_iff {V W X : Type*} [DecidableEq V] [DecidableEq W] {K : SimpleGraph V}
    {L : SimpleGraph W} {M : SimpleGraph X} {p : V} {q : W} {r s1 s2 : X}
    (f : Recon.card K p ≃g Recon.card L q) (y z : V) :
    (∃ e : L.induce ({q}ᶜ : Set W) ≃g M.induce ({r}ᶜ : Set X),
      ∀ t : ({q}ᶜ : Set W), (t.1 = extE f y → (e t).1 = s1) ∧ (t.1 = extE f z → (e t).1 = s2)) ↔
    (∃ e : K.induce ({p}ᶜ : Set V) ≃g M.induce ({r}ᶜ : Set X),
      ∀ t : ({p}ᶜ : Set V), (t.1 = y → (e t).1 = s1) ∧ (t.1 = z → (e t).1 = s2)) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨f.trans e, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
    · exact (he (f t)).1 (by rw [← extE_coe f t, ht])
    · exact (he (f t)).2 (by rw [← extE_coe f t, ht])
  · rintro ⟨e, he⟩
    refine ⟨f.symm.trans e, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
    · have h : (f.symm t).1 = y := by
        apply (extE f).injective
        rw [extE_coe f, ← ht]
        simp
      exact (he (f.symm t)).1 h
    · have h : (f.symm t).1 = z := by
        apply (extE f).injective
        rw [extE_coe f, ← ht]
        simp
      exact (he (f.symm t)).2 h

def isoPort {V W : Type*} [DecidableEq V] [DecidableEq W] {K : SimpleGraph V}
    {L : SimpleGraph W} {p : V} {q : W} (f : Recon.card K p ≃g Recon.card L q) (y : V)
    (C : Set V) (D : Set W) (hC : ∀ x, x ∈ C ↔ x ≠ p ∧ x ≠ y)
    (hD : ∀ x, x ∈ D ↔ x ≠ q ∧ x ≠ extE f y) : K.induce C ≃g L.induce D :=
  isoOn (extE f) C D (fun x => by
      rw [hC, hD]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h1 ((extE f).injective (h.trans (extE_a f).symm)),
          fun h => h2 ((extE f).injective h)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h1 (by rw [h]; exact extE_a f), fun h => h2 (by rw [h])⟩)
    (fun x z hx hz => extE_adj f x z ((hC x).1 hx).1 ((hC z).1 hz).1)

lemma isoPort_coe {V W : Type*} [DecidableEq V] [DecidableEq W] {K : SimpleGraph V}
    {L : SimpleGraph W} {p : V} {q : W} (f : Recon.card K p ≃g Recon.card L q) (y : V)
    (C : Set V) (D : Set W) (hC : ∀ x, x ∈ C ↔ x ≠ p ∧ x ≠ y)
    (hD : ∀ x, x ∈ D ↔ x ≠ q ∧ x ≠ extE f y) (t : C) :
    (isoPort f y C D hC hD t).1 = extE f t.1 := rfl

lemma port_iff {V W X : Type*} [DecidableEq V] [DecidableEq W] {K : SimpleGraph V}
    {L : SimpleGraph W} {M : SimpleGraph X} {p : V} {q : W} {r1 r2 s : X}
    (f : Recon.card K p ≃g Recon.card L q) (y z : V) :
    (∃ e : L.induce ({q, extE f y}ᶜ : Set W) ≃g M.induce ({r1, r2}ᶜ : Set X),
      ∀ t : ({q, extE f y}ᶜ : Set W), t.1 = extE f z → (e t).1 = s) ↔
    (∃ e : K.induce ({p, y}ᶜ : Set V) ≃g M.induce ({r1, r2}ᶜ : Set X),
      ∀ t : ({p, y}ᶜ : Set V), t.1 = z → (e t).1 = s) := by
  let R := isoPort f y ({p, y}ᶜ : Set V) ({q, extE f y}ᶜ : Set W) (fun x => by simp)
    (fun x => by simp)
  constructor
  · rintro ⟨e, he⟩
    refine ⟨R.trans e, fun t ht => ?_⟩
    exact he (R t) (by rw [isoPort_coe, ht])
  · rintro ⟨e, he⟩
    refine ⟨R.symm.trans e, fun t ht => ?_⟩
    have h3 : extE f (R.symm t).1 = extE f z :=
      (congrArg Subtype.val (R.apply_symm_apply t)).trans ht
    have h : (R.symm t).1 = z := (extE f).injective h3
    exact he (R.symm t) h

def tripleEquiv {n : ℕ} (σ : Fin n ≃ Fin n) (E : Fin n → Fin n ≃ Fin n) :
    Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n where
  toFun p := (σ p.1, E p.1 p.2.1, E p.1 p.2.2)
  invFun q := (σ.symm q.1, (E (σ.symm q.1)).symm q.2.1, (E (σ.symm q.1)).symm q.2.2)
  left_inv p := by simp
  right_inv q := by simp

lemma census3_A {n : ℕ} {G H M : SimpleGraph (Fin n)} (σ : Fin n ≃ Fin n)
    (hσ : ∀ x, Nonempty (Recon.card G x ≃g Recon.card H (σ x))) (u v w : Fin n) :
    (Aset H M u v w).ncard = (Aset G M u v w).ncard := by
  classical
  let Φ := tripleEquiv σ (fun x => extE (hσ x).some)
  rw [← Set.ncard_preimage_of_injective_subset_range Φ.injective (by simp)]
  congr 1
  ext ⟨x, y, z⟩
  simp only [Set.mem_preimage, Aset, Set.mem_ofPred_eq, Φ, tripleEquiv, Equiv.coe_fn_mk]
  rw [ne_iff (hσ x).some y, ne_iff (hσ x).some z, (extE (hσ x).some).injective.ne_iff,
    ptd2_iff (hσ x).some y z]

lemma census3_R {n : ℕ} (hn : 3 ≤ n) {G H M : SimpleGraph (Fin n)} (σ : Fin n ≃ Fin n)
    (hσ : ∀ x, Nonempty (Recon.card G x ≃g Recon.card H (σ x))) (u v w : Fin n) :
    (Rset H M u v w).ncard = (Rset G M u v w).ncard := by
  classical
  have hGH : Recon.Hypomorphic G H := ⟨σ, hσ⟩
  let Φ := tripleEquiv σ (fun x => extE (hσ x).some)
  rw [← Set.ncard_preimage_of_injective_subset_range Φ.injective (by simp)]
  congr 1
  ext ⟨x, y, z⟩
  simp only [Set.mem_preimage, Rset, Set.mem_ofPred_eq, Φ, tripleEquiv, Equiv.coe_fn_mk]
  rw [ne_iff (hσ x).some y, ne_iff (hσ x).some z, (extE (hσ x).some).injective.ne_iff,
    port_iff (hσ x).some y z, deg_T0 hn hGH (hσ x).some.symm]
  simp only [ptd2_iff (hσ x).some y z]

open Classical in
lemma endgameK {n : ℕ} (hn : 3 ≤ n) {G H : SimpleGraph (Fin n)} (hGH : Recon.Hypomorphic G H)
    {u v w a b c : Fin n} (huv : u ≠ v) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (e1 : Recon.card H a ≃g Recon.card G u)
    (he1 : ∀ t : ({a}ᶜ : Set (Fin n)), (t.1 = b → (e1 t).1 = v) ∧ (t.1 = c → (e1 t).1 = w))
    (f2 : Recon.card H b ≃g Recon.card G v)
    (hf2' : ∀ t : ({b}ᶜ : Set (Fin n)), (t.1 = a → (f2 t).1 = u) ∧ (t.1 = c → (f2 t).1 = w))
    (hK : ∀ g : G.induce ({u, v}ᶜ : Set (Fin n)) ≃g G.induce ({u, v}ᶜ : Set (Fin n)),
      (∀ t : ({u, v}ᶜ : Set (Fin n)), t.1 = w → (g t).1 = w) →
      (∀ t : ({u, v}ᶜ : Set (Fin n)), G.Adj u (g t).1 ↔ G.Adj u t.1) ∨
      (∀ t : ({u, v}ᶜ : Set (Fin n)), (G.neighborSet (g t).1).ncard = (G.neighborSet t.1).ncard)) :
    Nonempty (G ≃g H) := by
  classical
  obtain ⟨σ, hσ⟩ := hGH
  have hGH : Recon.Hypomorphic G H := ⟨σ, hσ⟩
  have hba : b ≠ a := Ne.symm hab
  have hf2 : (f2 ⟨a, hab⟩).1 = u := (hf2' _).1 rfl
  let Fu := extE e1.symm
  let Fv := extE f2.symm
  have hFuu : Fu u = a := extE_a _
  have hFuv : Fu v = b := extE_symm_eq e1 b v hba ((he1 _).1 rfl)
  have hFuw : Fu w = c := extE_symm_eq e1 c w hca ((he1 _).2 rfl)
  have hFvv : Fv v = b := extE_a _
  have hFvu : Fv u = a := extE_symm_eq f2 a u hab hf2
  have hFvw : Fv w = c := extE_symm_eq f2 c w hcb ((hf2' _).2 rfl)
  have hFuadj : ∀ x y, x ≠ u → y ≠ u → (H.Adj (Fu x) (Fu y) ↔ G.Adj x y) := extE_adj e1.symm
  have hFvadj : ∀ x y, x ≠ v → y ≠ v → (H.Adj (Fv x) (Fv y) ↔ G.Adj x y) := extE_adj f2.symm
  let ψ : Fin n ≃ Fin n := Fu.trans Fv.symm
  have hψ : ∀ x, Fv (ψ x) = Fu x := fun x => by simp [ψ]
  have hψu : ψ u = u := Fv.injective (by rw [hψ, hFuu, hFvu])
  have hψv : ψ v = v := Fv.injective (by rw [hψ, hFuv, hFvv])
  have hψw : ψ w = w := Fv.injective (by rw [hψ, hFuw, hFvw])
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
  have hgfix : ∀ t : ({u, v}ᶜ : Set (Fin n)), t.1 = w → (g t).1 = w := by
    intro t ht
    show ψ t.1 = w
    rw [ht, hψw]
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
  have hε : ∀ z, c (ψ z) = c z := by
    rcases hK g hgfix with htriv | hdp
    · intro z
      by_cases hzu : z = u
      · rw [hzu, hψu]
      by_cases hzv : z = v
      · rw [hzv, hψv]
      have h : G.Adj u (ψ z) ↔ G.Adj u z := htriv ⟨z, (memS z).2 ⟨hzu, hzv⟩⟩
      simp only [c, h]
    · have hdψ : ∀ z, (G.neighborSet (ψ z)).ncard = (G.neighborSet z).ncard := by
        intro z
        by_cases hzu : z = u
        · rw [hzu, hψu]
        by_cases hzv : z = v
        · rw [hzv, hψv]
        exact hdp ⟨z, (memS z).2 ⟨hzu, hzv⟩⟩
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

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__pointed_triple_window

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__pointed_triple_window : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__pointed_triple_window := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__pointed_triple_window in
  classical
  intro n hn G ⟨u, v, w, huv, huw, hvw, hcount, hK⟩ H ⟨σ, hσ⟩
  have hGH : Recon.Hypomorphic G H := ⟨σ, hσ⟩
  change (Rset G G u v w).ncard < (Aset G G u v w).ncard at hcount
  rw [← census3_A σ hσ u v w, ← census3_R hn σ hσ u v w] at hcount
  have hex : ∃ a b c : Fin n, (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∃ e : H.induce ({a}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)),
        ∀ t : ({a}ᶜ : Set (Fin n)), (t.1 = b → (e t).1 = v) ∧ (t.1 = c → (e t).1 = w)) ∧
      ∃ x' y' z' : Fin n, (x' ≠ y' ∧ x' ≠ z' ∧ y' ≠ z' ∧
        ∃ e : G.induce ({x'}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)),
          ∀ t : ({x'}ᶜ : Set (Fin n)), (t.1 = y' → (e t).1 = v) ∧ (t.1 = z' → (e t).1 = w)) ∧
        ∃ e : H.induce ({b}ᶜ : Set (Fin n)) ≃g G.induce ({y'}ᶜ : Set (Fin n)),
          ∀ t : ({b}ᶜ : Set (Fin n)), (t.1 = a → (e t).1 = x') ∧ (t.1 = c → (e t).1 = z') := by
    by_contra hne
    have hinj : Set.InjOn (fun p : Fin n × Fin n × Fin n => (p.2.1, p.1, p.2.2))
        (Aset H G u v w) := by
      rintro ⟨a, b, c⟩ _ ⟨a', b', c'⟩ _ h
      simp only [Prod.mk.injEq] at h ⊢
      tauto
    have hle := Set.ncard_le_ncard_of_injOn (fun p : Fin n × Fin n × Fin n => (p.2.1, p.1, p.2.2))
      (fun p hp => ?_) hinj (Set.toFinite (Rset H G u v w))
    · omega
    · obtain ⟨a, b, c⟩ := p
      obtain ⟨h1, h2, h3, e, he⟩ := hp
      have hba : b ≠ a := Ne.symm h1
      have hv : extE e b = v := by rw [extE_coe e ⟨b, hba⟩]; exact (he _).1 rfl
      have hw : extE e c = w := by rw [extE_coe e ⟨c, Ne.symm h2⟩]; exact (he _).2 rfl
      have h := deg_extE e b hba
      rw [hv] at h
      simp only [Rset, Set.mem_ofPred_eq]
      refine ⟨hba, h3, h2, ?_, ?_, ?_, fun hc => hne ⟨a, b, c, ⟨h1, h2, h3, e, he⟩, hc⟩⟩
      · refine ⟨isoPort e b ({b, a}ᶜ : Set (Fin n)) ({u, v}ᶜ : Set (Fin n))
          (fun x => by simp; tauto) (fun x => by rw [hv]; simp), fun t ht => ?_⟩
        rw [isoPort_coe, ht, hw]
      · intro hG
        by_cases hH : H.Adj a b <;> simp only [hG, hH, ite_true, ite_false] at h <;> omega
      · intro hG
        by_cases hH : H.Adj a b <;> simp only [hG, hH, ite_true, ite_false] at h <;> omega
  obtain ⟨a, b, c, ⟨hab, hac, hbc, e1, he1⟩, x', y', z', ⟨hxy', hxz', hyz', e0, he0⟩, e2, he2⟩ := hex
  have hy' : y' ≠ x' := Ne.symm hxy'
  have hz' : z' ≠ x' := Ne.symm hxz'
  have he1' : ∀ t : ({a}ᶜ : Set (Fin n)),
      (t.1 = b → ((e1.trans e0.symm) t).1 = y') ∧ (t.1 = c → ((e1.trans e0.symm) t).1 = z') := by
    intro t
    constructor
    · intro ht
      have h1 : e1 t = e0 ⟨y', hy'⟩ := Subtype.ext (((he1 t).1 ht).trans ((he0 _).1 rfl).symm)
      show (e0.symm (e1 t)).1 = y'
      rw [h1]
      simp
    · intro ht
      have h1 : e1 t = e0 ⟨z', hz'⟩ := Subtype.ext (((he1 t).2 ht).trans ((he0 _).2 rfl).symm)
      show (e0.symm (e1 t)).1 = z'
      rw [h1]
      simp
  exact endgameK hn hGH hxy' hab (Ne.symm hac) (Ne.symm hbc) (e1.trans e0.symm) he1' e2 he2
    (hK x' y' z' ⟨hxy', hxz', hyz', e0, he0⟩)
