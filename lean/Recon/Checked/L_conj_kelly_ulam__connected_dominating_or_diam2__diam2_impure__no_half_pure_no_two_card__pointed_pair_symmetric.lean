import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric
import Recon.Checked.L_kelly_edge_count
import Recon.Checked.L_kelly_card_edges_add_degree

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric

open SimpleGraph

def extE {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    {a : V} {b : W} (e : Recon.card G a ≃g Recon.card H b) : V ≃ W where
  toFun x := if h : x = a then b else (e ⟨x, h⟩ : W)
  invFun y := if h : y = b then a else (e.symm ⟨y, h⟩ : V)
  left_inv x := by
    by_cases h : x = a
    · subst h; simp
    · have h2 : ¬ (e ⟨x, h⟩ : W) = b := (e ⟨x, h⟩).2
      simp [h, h2]
  right_inv y := by
    by_cases h : y = b
    · subst h; simp
    · have h2 : ¬ (e.symm ⟨y, h⟩ : V) = a := (e.symm ⟨y, h⟩).2
      simp [h, h2]

lemma extE_a {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} {a : V} {b : W} (e : Recon.card G a ≃g Recon.card H b) :
    extE e a = b := by
  simp [extE]

lemma extE_ne {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} {a : V} {b : W} (e : Recon.card G a ≃g Recon.card H b) {x : V}
    (h : x ≠ a) : extE e x = (e ⟨x, h⟩ : W) := by
  simp [extE, h]

lemma extE_adj {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} {a : V} {b : W} (e : Recon.card G a ≃g Recon.card H b) (x y : V)
    (hx : x ≠ a) (hy : y ≠ a) : H.Adj (extE e x) (extE e y) ↔ G.Adj x y := by
  rw [extE_ne e hx, extE_ne e hy]
  exact e.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)

def isoOn {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (φ : V ≃ W) (C : Set V)
    (D : Set W) (hCD : ∀ x, x ∈ C ↔ φ x ∈ D)
    (hadj : ∀ x y, x ∈ C → y ∈ C → (H.Adj (φ x) (φ y) ↔ G.Adj x y)) :
    G.induce C ≃g H.induce D where
  toEquiv := φ.subtypeEquiv hCD
  map_rel_iff' := by
    intro a b
    exact hadj a.1 b.1 a.2 b.2

lemma extE_symm_eq {V W : Type*} [DecidableEq V] [DecidableEq W] {K : SimpleGraph V}
    {L : SimpleGraph W} {p : V} {q : W} (f : Recon.card K p ≃g Recon.card L q) (y : V) (c : W)
    (hy : y ≠ p) (h : (f ⟨y, hy⟩).1 = c) : extE f.symm c = y := by
  have hc : c ≠ q := by rw [← h]; exact (f ⟨y, hy⟩).2
  rw [extE_ne f.symm hc]
  have : (⟨c, hc⟩ : ({q}ᶜ : Set W)) = f ⟨y, hy⟩ := Subtype.ext h.symm
  rw [this]
  simp

lemma ne_iff {V W : Type*} [DecidableEq V] [DecidableEq W] {K : SimpleGraph V}
    {L : SimpleGraph W} {p : V} {q : W} (f : Recon.card K p ≃g Recon.card L q) (y : V) :
    q ≠ extE f y ↔ p ≠ y := by
  constructor
  · intro h hpy
    apply h
    rw [← hpy]
    exact (extE_a f).symm
  · intro h hq
    apply h
    apply (extE f).injective
    rw [extE_a f]
    exact hq

lemma ptd_iff {V W X : Type*} [DecidableEq V] [DecidableEq W] {K : SimpleGraph V}
    {L : SimpleGraph W} {M : SimpleGraph X} {p : V} {q : W} {r s : X}
    (f : Recon.card K p ≃g Recon.card L q) (y : V) (hy : y ≠ p) :
    (∃ e : L.induce ({q}ᶜ : Set W) ≃g M.induce ({r}ᶜ : Set X),
      ∀ z : ({q}ᶜ : Set W), z.1 = extE f y → (e z).1 = s) ↔
    (∃ e : K.induce ({p}ᶜ : Set V) ≃g M.induce ({r}ᶜ : Set X),
      ∀ z : ({p}ᶜ : Set V), z.1 = y → (e z).1 = s) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨f.trans e, fun z hz => ?_⟩
    have : z = ⟨y, hy⟩ := Subtype.ext hz
    subst this
    exact he _ (extE_ne f hy).symm
  · rintro ⟨e, he⟩
    refine ⟨f.symm.trans e, fun z hz => ?_⟩
    have : f.symm z = ⟨y, hy⟩ := by
      have hz' : z = f ⟨y, hy⟩ := Subtype.ext (by rw [hz, extE_ne f hy])
      rw [hz']
      simp
    show (e (f.symm z)).1 = s
    rw [this]
    exact he _ rfl

lemma restrict {V W : Type*} [DecidableEq V] [DecidableEq W] {K : SimpleGraph V}
    {L : SimpleGraph W} {p : V} {q : W} (f : Recon.card K p ≃g Recon.card L q) (y : V) (c : W)
    (_hy : y ≠ p) (hc : extE f y = c) :
    Nonempty (K.induce ({p, y}ᶜ : Set V) ≃g L.induce ({q, c}ᶜ : Set W)) := by
  subst hc
  refine ⟨isoOn (extE f) _ _ ?_ ?_⟩
  · intro x
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 ((extE f).injective (h.trans (extE_a f).symm)), fun h => h2 ((extE f).injective h)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 (by rw [h]; exact extE_a f), fun h => h2 (by rw [h])⟩
  · intro x z hx hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx hz
    exact extE_adj f x z hx.1 hz.1

def pairEquiv {n : ℕ} (σ : Fin n ≃ Fin n) (E : Fin n → Fin n ≃ Fin n) :
    Fin n × Fin n ≃ Fin n × Fin n where
  toFun p := (σ p.1, E p.1 p.2)
  invFun q := (σ.symm q.1, (E (σ.symm q.1)).symm q.2)
  left_inv p := by simp
  right_inv q := by simp

lemma census_A {n : ℕ} {G H M : SimpleGraph (Fin n)} (σ : Fin n ≃ Fin n)
    (hσ : ∀ x, Nonempty (Recon.card G x ≃g Recon.card H (σ x))) (r s : Fin n) :
    {p : Fin n × Fin n | p.1 ≠ p.2 ∧ ∃ e : H.induce ({p.1}ᶜ : Set (Fin n)) ≃g M.induce ({r}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = s}.ncard =
    {p : Fin n × Fin n | p.1 ≠ p.2 ∧ ∃ e : G.induce ({p.1}ᶜ : Set (Fin n)) ≃g M.induce ({r}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = s}.ncard := by
  classical
  let Φ := pairEquiv σ (fun x => extE (hσ x).some)
  rw [← Set.ncard_preimage_of_injective_subset_range Φ.injective (by simp)]
  congr 1
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Φ, pairEquiv, Equiv.coe_fn_mk]
  by_cases hxy : x = y
  · subst hxy
    simp [extE_a]
  · rw [ne_iff, ptd_iff (hσ x).some y (Ne.symm hxy)]

lemma census_B {n : ℕ} {G H M : SimpleGraph (Fin n)} (σ : Fin n ≃ Fin n)
    (hσ : ∀ x, Nonempty (Recon.card G x ≃g Recon.card H (σ x))) (u v r s : Fin n) :
    {p : Fin n × Fin n | p.1 ≠ p.2 ∧ Nonempty (H.induce ({p.1, p.2}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n))) ∧ ¬ ∃ e : H.induce ({p.1}ᶜ : Set (Fin n)) ≃g M.induce ({r}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = s}.ncard =
    {p : Fin n × Fin n | p.1 ≠ p.2 ∧ Nonempty (G.induce ({p.1, p.2}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n))) ∧ ¬ ∃ e : G.induce ({p.1}ᶜ : Set (Fin n)) ≃g M.induce ({r}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = s}.ncard := by
  classical
  let Φ := pairEquiv σ (fun x => extE (hσ x).some)
  rw [← Set.ncard_preimage_of_injective_subset_range Φ.injective (by simp)]
  congr 1
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Φ, pairEquiv, Equiv.coe_fn_mk]
  by_cases hxy : x = y
  · subst hxy
    simp [extE_a]
  · rw [ne_iff, ptd_iff (hσ x).some y (Ne.symm hxy)]
    obtain ⟨R⟩ := restrict (hσ x).some y _ (Ne.symm hxy) rfl
    have : Nonempty (H.induce ({σ x, extE (hσ x).some y}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n))) ↔
        Nonempty (G.induce ({x, y}ᶜ : Set (Fin n)) ≃g M.induce ({u, v}ᶜ : Set (Fin n))) :=
      ⟨fun ⟨w⟩ => ⟨R.trans w⟩, fun ⟨w⟩ => ⟨R.symm.trans w⟩⟩
    rw [this]

open Classical in
lemma ncard_sum {n : ℕ} (M : SimpleGraph (Fin n)) (w : Fin n) :
    ((M.neighborSet w).ncard : ℤ) = ∑ y, if M.Adj w y then (1 : ℤ) else 0 := by
  classical
  rw [SimpleGraph.ncard_neighborSet, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]
  rw [Finset.card_filter]
  push_cast
  rfl

open Classical in
lemma deg_extE {n : ℕ} {K L : SimpleGraph (Fin n)} {p q : Fin n}
    (f : Recon.card K p ≃g Recon.card L q) (x : Fin n) (hx : x ≠ p) :
    ((L.neighborSet (extE f x)).ncard : ℤ) + (if K.Adj p x then 1 else 0) =
      ((K.neighborSet x).ncard : ℤ) + (if L.Adj q (extE f x) then 1 else 0) := by
  classical
  rw [ncard_sum, ncard_sum, ← Equiv.sum_comp (extE f) (fun y => if L.Adj (extE f x) y then (1:ℤ) else 0)]
  rw [← Finset.add_sum_erase Finset.univ (fun y => if L.Adj (extE f x) (extE f y) then (1:ℤ) else 0) (Finset.mem_univ p),
    ← Finset.add_sum_erase Finset.univ (fun y => if K.Adj x y then (1:ℤ) else 0) (Finset.mem_univ p)]
  have hrest : ∑ y ∈ Finset.univ.erase p, (if L.Adj (extE f x) (extE f y) then (1:ℤ) else 0) =
      ∑ y ∈ Finset.univ.erase p, (if K.Adj x y then (1:ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [extE_adj f x y hx (Finset.ne_of_mem_erase hy)]
  rw [hrest, extE_a f, K.adj_comm p x, L.adj_comm q]
  ring

lemma deg_T0 {n : ℕ} (hn : 3 ≤ n) {G H : SimpleGraph (Fin n)} (hGH : Recon.Hypomorphic G H)
    {a x : Fin n} (f : Recon.card H a ≃g Recon.card G x) :
    (H.neighborSet a).ncard = (G.neighborSet x).ncard := by
  have e1 := Recon.Checked.L_kelly_card_edges_add_degree n G x
  have e2 := Recon.Checked.L_kelly_card_edges_add_degree n H a
  have e3 := Recon.Checked.L_kelly_edge_count.ncard_eq_of_iso f
  have e4 := Recon.Checked.L_kelly_edge_count n hn G H hGH
  omega

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric in
  classical
  intro n hn G ⟨u, v, huv, ⟨κ, hκ⟩, hcount, hd⟩ H ⟨σ, hσ⟩
  have hGH : Recon.Hypomorphic G H := ⟨σ, hσ⟩
  rw [← census_A σ hσ u v, ← census_B σ hσ u v u v] at hcount
  -- step 2: an anchored pair
  have hex : ∃ a b : Fin n, a ≠ b ∧
      (∃ e : H.induce ({a}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)),
        ∀ z : ({a}ᶜ : Set (Fin n)), z.1 = b → (e z).1 = v) ∧
      (∃ e : H.induce ({b}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)),
        ∀ z : ({b}ᶜ : Set (Fin n)), z.1 = a → (e z).1 = v) := by
    by_contra hne
    have hle := Set.ncard_le_ncard_of_injOn Prod.swap (fun p hp => ?_) Prod.swap_injective.injOn
      (Set.toFinite _) (s := {p : Fin n × Fin n | p.1 ≠ p.2 ∧ ∃ e : H.induce ({p.1}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = v})
      (t := {p : Fin n × Fin n | p.1 ≠ p.2 ∧ Nonempty (H.induce ({p.1, p.2}ᶜ : Set (Fin n)) ≃g G.induce ({u, v}ᶜ : Set (Fin n))) ∧ ¬ ∃ e : H.induce ({p.1}ᶜ : Set (Fin n)) ≃g G.induce ({u}ᶜ : Set (Fin n)), ∀ z : ({p.1}ᶜ : Set (Fin n)), z.1 = p.2 → (e z).1 = v})
    · omega
    · obtain ⟨hp1, e, he⟩ := hp
      refine ⟨Ne.symm hp1, ?_, fun h => hne ⟨p.1, p.2, hp1, ⟨e, he⟩, h⟩⟩
      obtain ⟨R⟩ := restrict e p.2 v (Ne.symm hp1) (by rw [extE_ne e (Ne.symm hp1)]; exact he _ rfl)
      show Nonempty (H.induce ({p.2, p.1}ᶜ : Set (Fin n)) ≃g G.induce ({u, v}ᶜ : Set (Fin n)))
      rw [Set.pair_comm]
      exact ⟨R⟩
  obtain ⟨a, b, hab, ⟨e1, he1⟩, ⟨e2, he2⟩⟩ := hex
  have hvu : v ≠ u := Ne.symm huv
  have hba : b ≠ a := Ne.symm hab
  let f2 : Recon.card H b ≃g Recon.card G v := e2.trans κ
  have hf2 : (f2 ⟨a, hab⟩).1 = u := hκ _ (he2 _ rfl)
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
  -- degrees
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
