import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__unique_switch
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__unique_switch

open SimpleGraph
open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class

lemma ncard_nbr_iso' {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (v : V) :
    (G.neighborSet v).ncard = (H.neighborSet (e v)).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (e.mapNeighborSet v)

noncomputable def dg {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) : ℤ := ((G.neighborSet x).ncard : ℤ)

noncomputable def ad {n : ℕ} (G : SimpleGraph (Fin n)) (x y : Fin n) : ℤ :=
  Set.indicator (G.neighborSet x) (fun _ => (1 : ℤ)) y

noncomputable def w2 {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) : ℤ :=
  ∑ y : Fin n, Set.indicator (G.neighborSet x) (fun y => dg G y) y

lemma ad_of_adj {n : ℕ} {G : SimpleGraph (Fin n)} {x y : Fin n} (h : G.Adj x y) : ad G x y = 1 :=
  Set.indicator_of_mem h _

lemma ad_of_not {n : ℕ} {G : SimpleGraph (Fin n)} {x y : Fin n} (h : ¬ G.Adj x y) :
    ad G x y = 0 :=
  Set.indicator_of_notMem h _

lemma ad_self {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) : ad G x x = 0 :=
  ad_of_not (G.loopless.irrefl x)

lemma ad_symm {n : ℕ} (G : SimpleGraph (Fin n)) (x y : Fin n) : ad G x y = ad G y x := by
  by_cases h : G.Adj x y
  · rw [ad_of_adj h, ad_of_adj h.symm]
  · rw [ad_of_not h, ad_of_not (fun h' => h h'.symm)]

lemma ad_cases {n : ℕ} (G : SimpleGraph (Fin n)) (x y : Fin n) : ad G x y = 0 ∨ ad G x y = 1 := by
  by_cases h : G.Adj x y
  · exact Or.inr (ad_of_adj h)
  · exact Or.inl (ad_of_not h)

lemma ad_iff {n : ℕ} {G K : SimpleGraph (Fin n)} {x y x' y' : Fin n}
    (h : ad G x y = ad K x' y') : G.Adj x y ↔ K.Adj x' y' := by
  by_cases h1 : G.Adj x y <;> by_cases h2 : K.Adj x' y'
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · rw [ad_of_adj h1, ad_of_not h2] at h; exact absurd h one_ne_zero
  · rw [ad_of_not h1, ad_of_adj h2] at h; exact absurd h zero_ne_one
  · exact ⟨fun h' => (h1 h').elim, fun h' => (h2 h').elim⟩

lemma ind_mul {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) (g : Fin n → ℤ) (y : Fin n) :
    Set.indicator (G.neighborSet x) g y = ad G x y * g y := by
  by_cases h : G.Adj x y
  · rw [ad_of_adj h, Set.indicator_of_mem h]; ring
  · rw [ad_of_not h, Set.indicator_of_notMem h]; ring

lemma sum_ad {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) : ∑ y, ad G x y = dg G x := by
  classical
  unfold ad dg
  rw [Finset.sum_indicator_eq_sum_filter]
  simp [Set.ncard_eq_toFinset_card']

lemma w2_eq {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) :
    w2 G x = ∑ y, ad G x y * dg G y := by
  unfold w2
  exact Finset.sum_congr rfl (fun y _ => ind_mul G x _ y)

def ext {n : ℕ} {G K : SimpleGraph (Fin n)} {u w : Fin n}
    (e : G.induce ({u}ᶜ : Set (Fin n)) ≃g K.induce ({w}ᶜ : Set (Fin n))) (x : Fin n) : Fin n :=
  if h : x = u then w else (e ⟨x, h⟩).1

variable {n : ℕ} {G K : SimpleGraph (Fin n)} {u w : Fin n}
    (e : G.induce ({u}ᶜ : Set (Fin n)) ≃g K.induce ({w}ᶜ : Set (Fin n)))

lemma ext_u : ext e u = w := dite_eq_left rfl

lemma ext_ne (x : Fin n) (h : x ≠ u) : ext e x = (e ⟨x, h⟩).1 := dite_eq_right h

lemma ext_ne' (x : Fin n) (h : x ≠ u) : ext e x ≠ w := by
  rw [ext_ne e x h]; exact (e ⟨x, h⟩).2

lemma ext_inj : Function.Injective (ext e) := by
  intro a b hab
  by_cases ha : a = u
  · by_cases hb : b = u
    · rw [ha, hb]
    · rw [ha, ext_u, ext_ne e b hb] at hab
      exact ((e ⟨b, hb⟩).2 hab.symm).elim
  · by_cases hb : b = u
    · rw [hb, ext_u, ext_ne e a ha] at hab
      exact ((e ⟨a, ha⟩).2 hab).elim
    · rw [ext_ne e a ha, ext_ne e b hb] at hab
      exact congrArg Subtype.val (e.injective (Subtype.ext hab))

noncomputable def extE : Fin n ≃ Fin n :=
  Equiv.ofBijective (ext e) (Finite.injective_iff_bijective.mp (ext_inj e))

lemma ext_adj (x y : Fin n) (hx : x ≠ u) (hy : y ≠ u) :
    K.Adj (ext e x) (ext e y) ↔ G.Adj x y := by
  rw [ext_ne e x hx, ext_ne e y hy]
  exact e.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)

lemma ext_deg (hδ : dg G u = dg K w) (x : Fin n) :
    dg K (ext e x) = dg G x - (ad G u x - ad K w (ext e x)) := by
  by_cases hx : x = u
  · subst hx
    rw [ext_u, ad_self, ad_self, hδ]; ring
  · have h1 := deg_in_card G u x hx
    have h2 := deg_in_card K w (ext e x) (ext_ne' e x hx)
    have h3 := ncard_nbr_iso' e ⟨x, hx⟩
    have h4 : (⟨ext e x, ext_ne' e x hx⟩ : ({w}ᶜ : Set (Fin n))) = e ⟨x, hx⟩ :=
      Subtype.ext (ext_ne e x hx)
    rw [h4] at h2
    unfold dg
    by_cases a1 : G.Adj u x <;> by_cases a2 : K.Adj w (ext e x) <;>
      simp only [a1, a2, ad_of_adj, ad_of_not, not_false_eq_true, ite_true, ite_false] at h1 h2 ⊢ <;>
      omega

lemma ad_ext (x y : Fin n) (hx : x ≠ u) (hy : y ≠ u) :
    ad K (ext e x) (ext e y) = ad G x y := by
  by_cases h : G.Adj x y
  · rw [ad_of_adj h, ad_of_adj ((ext_adj e x y hx hy).2 h)]
  · rw [ad_of_not h, ad_of_not (fun h' => h ((ext_adj e x y hx hy).1 h'))]

lemma ext_split (x : Fin n) (hx : x ≠ u) (g : Fin n → ℤ) :
    ∑ y, ad K (ext e x) (ext e y) * g y =
      ∑ y, ad G x y * g y + (ad K w (ext e x) - ad G u x) * g u := by
  have e1 : ∑ y, ad K (ext e x) (ext e y) * g y =
      ∑ y, ad G x y * g y + ∑ y, (ad K (ext e x) (ext e y) - ad G x y) * g y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  have e2 : ∑ y, (ad K (ext e x) (ext e y) - ad G x y) * g y =
      (ad K w (ext e x) - ad G u x) * g u := by
    rw [Finset.sum_eq_single u]
    · rw [ext_u, ad_symm K, ad_symm G]
    · intro y _ hy
      rw [ad_ext e x y hx hy]; ring
    · intro h; exact (h (Finset.mem_univ u)).elim
  rw [e1, e2]

lemma rel (a b : ℤ) (hG : ∀ x, w2 G x = a * dg G x + b) (hK : ∀ y, w2 K y = a * dg K y + b)
    (hδ : dg G u = dg K w) (x : Fin n) (hx : x ≠ u) :
    ∑ y, Set.indicator (G.neighborSet x) (fun y => ad G u y - ad K w (ext e y)) y =
      (a - dg G u) * (ad G u x - ad K w (ext e x)) := by
  have hw2K : w2 K (ext e x) = ∑ y, ad K (ext e x) (ext e y) * dg K (ext e y) := by
    rw [w2_eq]
    exact (Equiv.sum_comp (extE e) (fun y' => ad K (ext e x) y' * dg K y')).symm
  have h1 := hK (ext e x)
  rw [hw2K, ext_split e x hx, ext_u] at h1
  have h2 : ∑ y, ad G x y * dg K (ext e y) =
      w2 G x - ∑ y, ad G x y * (ad G u y - ad K w (ext e y)) := by
    rw [w2_eq, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun y _ => by rw [ext_deg e hδ y]; ring)
  have h3 : ∑ y, Set.indicator (G.neighborSet x) (fun y => ad G u y - ad K w (ext e y)) y =
      ∑ y, ad G x y * (ad G u y - ad K w (ext e y)) :=
    Finset.sum_congr rfl (fun y _ => ind_mul G x _ y)
  rw [h3]
  rw [h2, ext_deg e hδ x, hG x, ← hδ] at h1
  linear_combination -h1


lemma sq_id {n : ℕ} (X : SimpleGraph (Fin n)) (x : Fin n) :
    ∑ y : ({x}ᶜ : Set (Fin n)), (((X.induce ({x}ᶜ : Set (Fin n))).neighborSet y).ncard : ℤ) ^ 2 =
      (∑ y, dg X y ^ 2) - dg X x ^ 2 - 2 * w2 X x + dg X x := by
  have hc : ∀ y : ({x}ᶜ : Set (Fin n)),
      (((X.induce ({x}ᶜ : Set (Fin n))).neighborSet y).ncard : ℤ) = dg X y.1 - ad X x y.1 := by
    intro y
    obtain ⟨y, hy⟩ := y
    have := deg_in_card X x y hy
    unfold dg
    by_cases h : X.Adj x y <;>
      simp only [h, ad_of_adj, ad_of_not, not_false_eq_true, ite_true, ite_false] at this ⊢ <;>
      omega
  rw [Finset.sum_congr rfl (fun y _ => by rw [hc y])]
  have hsub : ∑ y : ({x}ᶜ : Set (Fin n)), (dg X y.1 - ad X x y.1) ^ 2 =
      ∑ y ∈ Finset.univ.erase x, (dg X y - ad X x y) ^ 2 :=
    (Finset.sum_subtype _ (fun y => by simp) (fun y => (dg X y - ad X x y) ^ 2)).symm
  have hadd := Finset.add_sum_erase Finset.univ (fun y => (dg X y - ad X x y) ^ 2)
    (Finset.mem_univ x)
  have hterm : ∀ y, (dg X y - ad X x y) ^ 2 = dg X y ^ 2 - 2 * (ad X x y * dg X y) + ad X x y := by
    intro y
    rcases ad_cases X x y with h | h <;> rw [h] <;> ring
  have htot : ∑ y, (dg X y - ad X x y) ^ 2 = (∑ y, dg X y ^ 2) - 2 * w2 X x + dg X x := by
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sum_ad, ← w2_eq]
  simp only [ad_self, sub_zero] at hadd
  rw [hsub]
  linarith

lemma w2_tied {n : ℕ} (G H : SimpleGraph (Fin n)) (σ : Fin n ≃ Fin n)
    (f : ∀ x, G.induce ({x}ᶜ : Set (Fin n)) ≃g H.induce ({σ x}ᶜ : Set (Fin n)))
    (hdeg : ∀ x, dg G x = dg H (σ x)) (x : Fin n) : w2 H (σ x) = w2 G x := by
  have hQ : ∑ y, dg H y ^ 2 = ∑ y, dg G y ^ 2 := by
    rw [← Equiv.sum_comp σ]
    exact Finset.sum_congr rfl (fun y _ => by rw [hdeg y])
  have hq : ∑ y : ({x}ᶜ : Set (Fin n)),
      (((G.induce ({x}ᶜ : Set (Fin n))).neighborSet y).ncard : ℤ) ^ 2 =
      ∑ y : ({σ x}ᶜ : Set (Fin n)),
      (((H.induce ({σ x}ᶜ : Set (Fin n))).neighborSet y).ncard : ℤ) ^ 2 :=
    Fintype.sum_equiv (f x).toEquiv _ _ (fun y => by rw [ncard_nbr_iso' (f x) y]; rfl)
  have h1 := sq_id G x
  have h2 := sq_id H (σ x)
  rw [← hdeg x, hQ] at h2
  linarith

lemma k_nonneg {n : ℕ} (G K : SimpleGraph (Fin n)) (u w : Fin n) (φ : Fin n → Fin n) :
    0 ≤ ∑ y, Set.indicator (G.neighborSet u) (fun y => ad G u y - ad K w (φ y)) y := by
  apply Finset.sum_nonneg
  intro y _
  by_cases h : G.Adj u y
  · rw [Set.indicator_of_mem h, ad_of_adj h]
    rcases ad_cases K w (φ y) with h' | h' <;> rw [h'] <;> norm_num
  · rw [Set.indicator_of_notMem h]

theorem prop_of_kernel {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℤ) (u : Fin n)
    (hker : ∀ f : Fin n → ℤ, (∀ x : Fin n, ∑ y : Fin n, Set.indicator (G.neighborSet x) f y =
      c * f x) → f = 0)
    (z1 z2 : Fin n → ℤ) (k1 k2 : ℤ)
    (h1 : ∀ x : Fin n, ∑ y : Fin n, Set.indicator (G.neighborSet x) z1 y =
      c * z1 x + (if x = u then k1 else 0))
    (h2 : ∀ x : Fin n, ∑ y : Fin n, Set.indicator (G.neighborSet x) z2 y =
      c * z2 x + (if x = u then k2 else 0)) :
    ∀ x, k2 * z1 x = k1 * z2 x := by
  have := hker (fun x => k2 * z1 x - k1 * z2 x) (by
    intro x
    have e1 : ∀ y, Set.indicator (G.neighborSet x) (fun x => k2 * z1 x - k1 * z2 x) y =
        k2 * Set.indicator (G.neighborSet x) z1 y - k1 * Set.indicator (G.neighborSet x) z2 y := by
      intro y
      by_cases hy : y ∈ G.neighborSet x
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, h1 x, h2 x]
    split_ifs <;> ring)
  intro x
  have hx := congrFun this x
  simp only [Pi.zero_apply] at hx
  linarith

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__unique_switch

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__unique_switch : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__unique_switch := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class in
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__unique_switch in
  intro n hn G ⟨a, b, h2wl, u', hker, u, α, x0, hux0, hnx0⟩ H ⟨σ, hσ⟩
  have hG : ∀ x, w2 G x = a * dg G x + b := fun x => h2wl x
  have hE := Recon.Checked.L_kelly_edge_count n hn G H ⟨σ, hσ⟩
  let f : ∀ x, G.induce ({x}ᶜ : Set (Fin n)) ≃g H.induce ({σ x}ᶜ : Set (Fin n)) :=
    fun x => (hσ x).some
  have hdeg : ∀ x, dg G x = dg H (σ x) := fun x => by
    have h1 := card_add_deg G x
    have h2 := card_add_deg H (σ x)
    have h3 := ncard_iso (f x)
    have : (G.neighborSet x).ncard = (H.neighborSet (σ x)).ncard := by omega
    unfold dg; rw [this]
  have hH : ∀ y, w2 H y = a * dg H y + b := by
    intro y
    obtain ⟨x, rfl⟩ := σ.surjective y
    rw [w2_tied G H σ f hdeg x, hG x, hdeg x]
  have hδα : dg G u' = dg G u := by
    have h1 := card_add_deg G u
    have h2 := card_add_deg G u'
    have h3 := ncard_iso α
    have : (G.neighborSet u').ncard = (G.neighborSet u).ncard := by omega
    unfold dg; rw [this]
  have r1 := rel (f u') a b hG hH (hdeg u')
  have r2 := rel α.symm a b hG hG hδα
  have hk := prop_of_kernel G (a - dg G u') u' hker
    (fun y => ad G u' y - ad H (σ u') (ext (f u') y))
    (fun y => ad G u' y - ad G u (ext α.symm y))
    (∑ y, Set.indicator (G.neighborSet u') (fun y => ad G u' y - ad H (σ u') (ext (f u') y)) y)
    (∑ y, Set.indicator (G.neighborSet u') (fun y => ad G u' y - ad G u (ext α.symm y)) y)
    (fun x => by
      by_cases hx : x = u'
      · subst hx
        rw [ite_eq_left rfl, ext_u, ad_self, ad_self]; ring
      · rw [ite_eq_right hx, r1 x hx]; ring)
    (fun x => by
      by_cases hx : x = u'
      · subst hx
        rw [ite_eq_left rfl, ext_u, ad_self, ad_self]; ring
      · rw [ite_eq_right hx, r2 x hx]; ring)
  have hk1n := k_nonneg G H u' (σ u') (ext (f u'))
  have hk2n := k_nonneg G G u' u (ext α.symm)
  set k1 := ∑ y, Set.indicator (G.neighborSet u') (fun y => ad G u' y - ad H (σ u') (ext (f u') y)) y with hk1
  set k2 := ∑ y, Set.indicator (G.neighborSet u') (fun y => ad G u' y - ad G u (ext α.symm y)) y with hk2
  by_cases h0 : k1 = 0
  · have hz : (fun y => ad G u' y - ad H (σ u') (ext (f u') y)) = 0 := by
      apply hker
      intro x
      by_cases hx : x = u'
      · subst hx
        rw [← hk1, h0, ext_u, ad_self, ad_self]; ring
      · exact r1 x hx
    refine iso_of_nbhd (f u') (fun x hx => ?_)
    have h := congrFun hz x
    simp only [Pi.zero_apply] at h
    have h' := ad_iff (sub_eq_zero.mp h)
    rw [ext_ne _ x hx] at h'
    exact h'
  · have hk1p : 0 < k1 := lt_of_le_of_ne hk1n (Ne.symm h0)
    have hy0 : (α x0).1 ≠ u' := (α x0).2
    have hz2 : ad G u' (α x0).1 - ad G u (ext α.symm (α x0).1) = -1 := by
      rw [ext_ne _ _ hy0, ad_of_not hnx0]
      have : (⟨(α x0).1, hy0⟩ : ({u'}ᶜ : Set (Fin n))) = α x0 := rfl
      rw [this, RelIso.symm_apply_apply, ad_of_adj hux0]
      ring
    have hky := hk (α x0).1
    rw [hz2] at hky
    have h21 : k2 = k1 := by
      rcases ad_cases G u' (α x0).1 with h | h <;>
      rcases ad_cases H (σ u') (ext (f u') (α x0).1) with h' | h' <;>
      rw [h, h'] at hky <;> linarith
    refine iso_of_nbhd (α.trans (f u')) (fun x hx => ?_)
    have hy : (α ⟨x, hx⟩).1 ≠ u' := (α ⟨x, hx⟩).2
    have hzz := hk (α ⟨x, hx⟩).1
    rw [h21] at hzz
    have hzz' := mul_left_cancel₀ (ne_of_gt hk1p) hzz
    have h' : ad G u x = ad H (σ u') (f u' (α ⟨x, hx⟩)).1 := by
      have e1 := ext_ne (f u') _ hy
      have e2 := ext_ne α.symm _ hy
      have e3 : (⟨(α ⟨x, hx⟩).1, hy⟩ : ({u'}ᶜ : Set (Fin n))) = α ⟨x, hx⟩ := rfl
      rw [e3] at e1 e2
      rw [e1, e2, RelIso.symm_apply_apply] at hzz'
      linarith
    exact ad_iff h'
