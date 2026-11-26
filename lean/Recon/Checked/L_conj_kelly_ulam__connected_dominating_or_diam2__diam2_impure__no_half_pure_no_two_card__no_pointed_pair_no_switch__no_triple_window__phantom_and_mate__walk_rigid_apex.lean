import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_rigid_apex
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degree_corank_one
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_rigid_apex

open SimpleGraph
open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degree_corank_one

lemma tele {R : Type*} [Ring R] (a b : R) (m : ℕ) :
    a ^ m = b ^ m + ∑ i ∈ Finset.range m, a ^ i * (a - b) * b ^ (m - 1 - i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ', pow_succ' a m, ih]
    have e : ∀ i ∈ Finset.range m, a ^ (i + 1) * (a - b) * b ^ (m + 1 - 1 - (i + 1)) =
        a * (a ^ i * (a - b) * b ^ (m - 1 - i)) := by
      intro i _
      rw [pow_succ', show m + 1 - 1 - (i + 1) = m - 1 - i by omega]
      simp only [mul_assoc]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, pow_succ' b m]
    simp only [pow_zero, one_mul, Nat.add_sub_cancel, Nat.sub_zero, mul_add, sub_mul]
    abel

def u {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℤ) (x : ι) (j : ℕ) : ℤ :=
  ∑ w, A x w * ww B j w

lemma ww_del_x {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (x : ι) (j : ℕ) :
    ww (del A x) j x = if j = 0 then 1 else 0 := by
  rcases j with _ | j
  · simp [ww, Matrix.one_apply]
  · rw [ww_succ]; simp [del_apply]

lemma key {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (x : ι) (hA : A x x = 0)
    (i j : ℕ) :
    ∑ y, (A ^ i * (A - del A x) * (del A x) ^ j) x y =
      cc A i x * u A (del A x) x j + if j = 0 then cc A (i + 1) x else 0 := by
  set B := del A x with hB
  have hr : ∀ z, ∑ w, (A - B) z w * ww B j w =
      (if z = x then u A B x j else 0) + (if j = 0 then A z x else 0) := by
    intro z
    by_cases hz : z = x
    · subst hz
      have : ∀ w, (A - B) z w = A z w := fun w => by simp [hB, del_apply]
      simp only [this, u, ite_true, hA, ite_self, add_zero]
    · have : ∀ w, (A - B) z w * ww B j w = if w = x then A z x * ww B j x else 0 := by
        intro w
        by_cases hw : w = x
        · subst hw; simp [hB, del_apply]
        · simp [hB, del_apply, hz, hw]
      rw [Finset.sum_congr rfl fun w _ => this w, Finset.sum_ite_eq' Finset.univ x, hB,
        ww_del_x]
      simp [hz]
  have h1 : ∀ y, (A ^ i * (A - B) * B ^ j) x y = ∑ z, (A ^ i) x z * ((A - B) * B ^ j) z y := by
    intro y; rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ z, ∑ y, (A ^ i) x z * ((A - B) * B ^ j) z y =
      (A ^ i) x z * ((if z = x then u A B x j else 0) + (if j = 0 then A z x else 0)) := by
    intro z
    rw [← Finset.mul_sum, ← hr z]
    congr 1
    simp only [Matrix.mul_apply, ww, Finset.mul_sum]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun z _ => h2 z]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq' Finset.univ x,
    Finset.mem_univ, ite_true]
  congr 1
  split_ifs
  · rw [cc, pow_succ, Matrix.mul_apply]
  · simp

lemma row_id {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (x : ι) (hA : A x x = 0)
    (m : ℕ) :
    ww A (m + 1) x = ∑ i ∈ Finset.range (m + 1),
      (cc A i x * u A (del A x) x (m - i) + if m - i = 0 then cc A (i + 1) x else 0) := by
  have h0 : ∑ y : ι, (((del A x) ^ (m + 1) : Matrix ι ι ℤ) x y) = 0 := by
    have := ww_del_x A x (m + 1); simpa [ww] using this
  rw [ww, tele A (del A x) (m + 1)]
  simp only [Matrix.add_apply, Finset.sum_add_distrib, Matrix.sum_apply, h0, zero_add]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show m + 1 - 1 - i = m - i by omega]
  exact key A x hA i (m - i)

lemma u_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A A' B : Matrix ι ι ℤ) (x : ι)
    (hA : A x x = 0) (hA' : A' x x = 0) (hB : del A x = B) (hB' : del A' x = B)
    (hcc : ∀ k, cc A k x = cc A' k x) (hww : ∀ k, ww A k x = ww A' k x) :
    ∀ m, u A B x m = u A' B x m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h1 := row_id A x hA m
    have h2 := row_id A' x hA' m
    rw [hB] at h1
    rw [hB'] at h2
    rw [Finset.sum_range_succ'] at h1 h2
    have e : ∑ i ∈ Finset.range m, (cc A (i + 1) x * u A B x (m - (i + 1)) +
          if m - (i + 1) = 0 then cc A (i + 1 + 1) x else 0) =
        ∑ i ∈ Finset.range m, (cc A' (i + 1) x * u A' B x (m - (i + 1)) +
          if m - (i + 1) = 0 then cc A' (i + 1 + 1) x else 0) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [hcc, hcc, ih (m - (i + 1)) (by omega)]
    rw [e, hww] at h1
    have c0 : cc A 0 x = 1 := by simp [cc]
    have c0' : cc A' 0 x = 1 := by simp [cc]
    rw [c0] at h1
    rw [c0'] at h2
    rw [hcc 1] at h1
    simp only [Nat.sub_zero, zero_add, one_mul] at h1 h2
    linarith

lemma nb_split {n : ℕ} (M : SimpleGraph (Fin n)) [DecidableRel M.Adj] (a x : Fin n) :
    (M.neighborSet a).ncard = {z | M.Adj a z ∧ z ≠ x}.ncard + if M.Adj a x then 1 else 0 := by
  classical
  by_cases h : M.Adj a x
  · have e : M.neighborSet a = insert x {z | M.Adj a z ∧ z ≠ x} := by
      ext z
      simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_ofPred_eq]
      constructor
      · intro hz; by_cases hzx : z = x
        · exact Or.inl hzx
        · exact Or.inr ⟨hz, hzx⟩
      · rintro (rfl | ⟨hz, _⟩)
        · exact h
        · exact hz
    rw [e, Set.ncard_insert_of_notMem (by simp) (Set.toFinite _)]
    simp [h]
  · have e : M.neighborSet a = {z | M.Adj a z ∧ z ≠ x} := by
      ext z
      simp only [SimpleGraph.mem_neighborSet, Set.mem_ofPred_eq]
      constructor
      · intro hz; exact ⟨hz, fun hzx => h (hzx ▸ hz)⟩
      · exact fun h => h.1
    rw [e]; simp [h]

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_rigid_apex

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_rigid_apex : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_rigid_apex := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_rigid_apex Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degree_corank_one in
  intro n hn G hP H ⟨σ, hσ⟩
  classical
  obtain ⟨x, hx⟩ := hP
  let K : SimpleGraph (Fin n) := H.comap σ
  have eKH : K ≃g H := { toEquiv := σ, map_rel_iff' := Iff.rfl }
  have g : ∀ x, G.induce ({x}ᶜ : Set (Fin n)) ≃g K.induce ({x}ᶜ : Set (Fin n)) := fun x =>
    (hσ x).some.trans (Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.isoOn (G := K) (H := H) σ ({x}ᶜ : Set (Fin n)) ({σ x}ᶜ : Set (Fin n))
      (fun a => by simp) (fun a b _ _ => Iff.rfl)).symm
  have hGK : Recon.Hypomorphic G K := ⟨Equiv.refl _, fun x => ⟨g x⟩⟩
  have hdeg : ∀ x, (K.neighborSet x).ncard = (G.neighborSet x).ncard := fun x =>
    Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.deg_T0 hn hGK (g x).symm
  set AG := G.adjMatrix ℤ with hAG
  set AK := K.adjMatrix ℤ with hAK
  have hgG := good AG (G.isSymm_adjMatrix)
  have hgK := good AK (K.isSymm_adjMatrix)
  have e1 : (fun k v => tr (del AK v) k) = (fun k v => tr (del AG v) k) :=
    funext fun k => funext fun v => (card_tr G K v (g v) k).1
  have e2 : (fun k v => WW (del AK v) k) = (fun k v => WW (del AG v) k) :=
    funext fun k => funext fun v => (card_tr G K v (g v) k).2
  rw [e1, e2] at hgK
  have hn' : 3 ≤ Fintype.card (Fin n) := by simpa using hn
  have hHg := hagos_induction hn' _ _ _ _ _ _ _ _ _ _ hgG hgK
  have hccGK : ∀ k v, cc AG k v = cc AK k v := fun k v => (hHg k).2.2.1 v
  have hwwGK : ∀ k v, ww AG k v = ww AK k v := fun k v => (hHg k).2.2.2 v
  -- the re-attachment at x
  set φ : Fin n ≃ Fin n := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.extE (g x) with hφ
  have hφx : φ x = x := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.extE_a (g x)
  have hφne : ∀ y, y ≠ x → φ y ≠ x := by
    intro y hy h
    apply hy
    apply φ.injective
    rw [h, hφx]
  have hφadj : ∀ a b, a ≠ x → b ≠ x → (K.Adj (φ a) (φ b) ↔ G.Adj a b) := fun a b ha hb =>
    Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.extE_adj (g x) a b ha hb
  set A' : Matrix (Fin n) (Fin n) ℤ := AK.submatrix φ φ with hA'
  set B := del AG x with hB
  have hAGx : AG x x = 0 := by simp [hAG]
  have hA'x : A' x x = 0 := by simp [hA', hAK, hφx]
  have hdel : del A' x = B := by
    ext a b
    rw [hB, del_apply, del_apply]
    by_cases ha : a = x
    · simp [ha]
    by_cases hb : b = x
    · simp [hb]
    simp only [ha, hb, or_self, ite_false, hA', Matrix.submatrix_apply, hAK, hAG,
      SimpleGraph.adjMatrix_apply, hφadj a b ha hb]
  have hpow : ∀ k, A' ^ k = (AK ^ k).submatrix φ φ := fun k => submatrix_pow_equiv AK φ k
  have hcc' : ∀ k, cc AG k x = cc A' k x := by
    intro k
    rw [hccGK, cc, cc, hpow, Matrix.submatrix_apply, hφx]
  have hww' : ∀ k, ww AG k x = ww A' k x := by
    intro k
    rw [hwwGK, ww, ww, hpow]
    simp only [Matrix.submatrix_apply, hφx]
    exact (Equiv.sum_comp φ (fun y => (AK ^ k) x y)).symm
  have hu := u_eq AG A' B x hAGx hA'x hB.symm hdel hcc' hww'
  -- the swap vector
  let δ : Fin n → ℤ := fun y => (if K.Adj x (φ y) then 1 else 0) - (if G.Adj x y then 1 else 0)
  have hw0 : ∀ y : Fin n, ww B 0 y = 1 := fun y => by simp [ww, Matrix.one_apply]
  have hws : ∀ k : ℕ, ∀ y : Fin n, ww B (k + 1) y = ∑ z : Fin n,
      Set.indicator {z : Fin n | G.Adj y z ∧ y ≠ x ∧ z ≠ x} (ww B k) z := by
    intro k y
    rw [ww_succ]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Set.indicator_apply, hB, del_apply, hAG, SimpleGraph.adjMatrix_apply]
    by_cases h1 : y = x <;> by_cases h2 : z = x <;> by_cases h3 : G.Adj y z <;>
      simp [h1, h2, h3]
  have hδx : δ x = 0 := by simp [δ, hφx]
  have hs1 : ∀ y : Fin n, G.Adj x y → δ y = 0 ∨ δ y = -1 := by
    intro y hy
    by_cases h : K.Adj x (φ y) <;> simp [δ, h, hy]
  have hs2 : ∀ y : Fin n, ¬ G.Adj x y → δ y = 0 ∨ δ y = 1 := by
    intro y hy
    by_cases h : K.Adj x (φ y) <;> simp [δ, h, hy]
  have hwalk : ∀ k : ℕ, ∑ y : Fin n, δ y * ww B k y = 0 := by
    intro k
    have h := hu k
    simp only [u] at h
    have q : ∀ y, δ y * ww B k y = A' x y * ww B k y - AG x y * ww B k y := by
      intro y
      simp only [δ, hA', hAK, hAG, Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, hφx, sub_mul]
    rw [Finset.sum_congr rfl fun y _ => q y, Finset.sum_sub_distrib, h]
    ring
  have hbal : ∀ j : ℕ, ∑ y : Fin n,
      Set.indicator {y : Fin n | {z : Fin n | G.Adj y z ∧ z ≠ x}.ncard = j} δ y = 0 := by
    intro j
    let J : Fin n → ℕ := fun y => {z : Fin n | G.Adj y z ∧ z ≠ x}.ncard
    have hJP : ∀ a, J a + (if G.Adj x a then 1 else 0) = (G.neighborSet a).ncard := by
      intro a
      rw [nb_split G a x, G.adj_comm x a]
    have hJQ : ∀ a, J a + (if K.Adj x (φ a) then 1 else 0) = (G.neighborSet (φ a)).ncard := by
      intro a
      by_cases ha : a = x
      · subst ha
        have h := hJP a
        rw [hφx]
        simp only [SimpleGraph.irrefl, ite_false] at h ⊢
        exact h
      · have h1 := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.deg_extE (g x) a ha
        rw [← hφ] at h1
        have h2 := hdeg (φ a)
        have h3 := hJP a
        split_ifs at h1 h3 ⊢ <;> omega
    have hcount : ∀ k, (Finset.univ.filter (fun a => J a + (if G.Adj x a then 1 else 0) = k)).card =
        (Finset.univ.filter (fun a => J a + (if K.Adj x (φ a) then 1 else 0) = k)).card := by
      intro k
      have e1 : Finset.univ.filter (fun a => J a + (if G.Adj x a then 1 else 0) = k) =
          Finset.univ.filter (fun a => (G.neighborSet a).ncard = k) :=
        Finset.filter_congr fun a _ => by rw [hJP a]
      have e2 : Finset.univ.filter (fun a => J a + (if K.Adj x (φ a) then 1 else 0) = k) =
          Finset.univ.filter (fun a => (G.neighborSet (φ a)).ncard = k) :=
        Finset.filter_congr fun a _ => by rw [hJQ a]
      rw [e1, e2]
      exact (Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure.card_comp φ (fun a => (G.neighborSet a).ncard = k)).symm
    have hlev := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure.level_bal J (fun a => G.Adj x a) (fun a => K.Adj x (φ a)) hcount j
    have q : ∀ y, Set.indicator {y : Fin n | {z : Fin n | G.Adj y z ∧ z ≠ x}.ncard = j} δ y =
        (if J y = j ∧ K.Adj x (φ y) then (1 : ℤ) else 0) - (if J y = j ∧ G.Adj x y then (1 : ℤ) else 0) := by
      intro y
      have hm : y ∈ {y : Fin n | {z : Fin n | G.Adj y z ∧ z ≠ x}.ncard = j} ↔ J y = j := Iff.rfl
      by_cases h1 : J y = j
      · rw [Set.indicator_of_mem (hm.mpr h1)]
        simp only [δ, h1, true_and]
      · rw [Set.indicator_of_notMem (fun h => h1 (hm.mp h))]
        simp only [h1, false_and, ite_false, sub_zero]
    rw [Finset.sum_congr rfl fun y _ => q y, Finset.sum_sub_distrib, Finset.sum_boole,
      Finset.sum_boole, ← hlev, sub_self]
  have hδ := hx (ww B) hw0 hws δ hδx hs1 hs2 hbal hwalk
  have hadjx : ∀ y, K.Adj x (φ y) ↔ G.Adj x y := by
    intro y
    have h := congrFun hδ y
    simp only [δ, Pi.zero_apply] at h
    by_cases h1 : K.Adj x (φ y) <;> by_cases h2 : G.Adj x y <;> simp_all
  have hiso : ∀ a b, K.Adj (φ a) (φ b) ↔ G.Adj a b := by
    intro a b
    by_cases ha : a = x
    · subst ha; rw [hφx]; exact hadjx b
    by_cases hb : b = x
    · subst hb; rw [hφx, K.adj_comm, G.adj_comm]; exact hadjx a
    exact hφadj a b ha hb
  have eGK : G ≃g K := { toEquiv := φ, map_rel_iff' := fun {a b} => hiso a b }
  exact ⟨eGK.trans eKH⟩
