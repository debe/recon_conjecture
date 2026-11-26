import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degree_corank_one
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__aligned_switch_kelly4
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degree_corank_one

open SimpleGraph PowerSeries

lemma alg {S R : Type*} [CommRing S] [Ring R] [Algebra S R] (t c : S) (A A₀ E N N₀ : R)
    (h1 : N - t • (A * N) = 1) (h2 : N₀ - t • (N₀ * A₀) = 1)
    (h3 : A₀ = (1 - E) * A * (1 - E)) (h4 : E * E = E) (h5 : E * N * E = c • E) :
    c • (N - N₀ + E) = N * E * N := by
  set Y := c • N - N * E * N + c • E with hY
  have hEY : E * Y = c • E := by
    have : E * Y = c • (E * N) - (E * N * E) * N + c • (E * E) := by
      rw [hY]; simp only [mul_add, mul_sub, mul_smul_comm, mul_assoc]
    rw [this, h5, h4, smul_mul_assoc]; abel
  have hAN : t • (A * N) = N - 1 := by rw [← h1]; abel
  have hPY : (1 - E) * Y = c • N - N * E * N := by
    rw [sub_mul, one_mul, hEY, hY]; abel
  have hT : t • (A₀ * Y) = Y - c • 1 := by
    have e1 : t • (A₀ * Y) = (1 - E) * (t • (A * ((1 - E) * Y))) := by
      rw [h3]; simp only [mul_smul_comm, mul_assoc]
    have e2 : t • (A * (c • N - N * E * N)) = c • (t • (A * N)) - (t • (A * N)) * E * N := by
      simp only [mul_sub, mul_smul_comm, smul_sub, smul_mul_assoc, mul_assoc, smul_comm t c]
    rw [e1, hPY, e2, hAN]
    have e3 : E * N * E * N = c • (E * N) := by rw [h5, smul_mul_assoc]
    rw [hY]
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_sub, mul_smul_comm, ← mul_assoc, e3, h4]
    abel
  have hY' : Y = c • N₀ := by
    calc Y = (N₀ - t • (N₀ * A₀)) * Y := by rw [h2, one_mul]
      _ = N₀ * (Y - t • (A₀ * Y)) := by
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc]
      _ = c • N₀ := by rw [hT]; simp
  rw [smul_add, smul_sub, ← hY', hY]; abel

noncomputable def ser {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) :
    Matrix ι ι (PowerSeries ℤ) :=
  Matrix.of fun x y => PowerSeries.mk fun k => (M ^ k) x y

lemma coeff_one_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι) (k : ℕ) :
    coeff k ((1 : Matrix ι ι (PowerSeries ℤ)) x y) = if k = 0 then (1 : Matrix ι ι ℤ) x y else 0 := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp_all [coeff_one]

lemma ser_left {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) :
    ser M - (PowerSeries.X (R := ℤ)) • ((PowerSeries.C (R := ℤ)).mapMatrix M * ser M) = 1 := by
  ext x y k
  rw [coeff_one_apply]
  rcases k with _ | k
  · simp [ser]
  · simp [ser, Matrix.mul_apply, coeff_succ_X_mul, pow_succ', map_sum]

lemma ser_right {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) :
    ser M - (PowerSeries.X (R := ℤ)) • (ser M * (PowerSeries.C (R := ℤ)).mapMatrix M) = 1 := by
  ext x y k
  rw [coeff_one_apply]
  rcases k with _ | k
  · simp [ser]
  · simp [ser, Matrix.mul_apply, coeff_succ_X_mul, pow_succ, map_sum]

def proj {ι : Type*} [DecidableEq ι] (v : ι) : ι → ℤ := fun x => if x = v then 0 else 1

def del {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (v : ι) : Matrix ι ι ℤ :=
  Matrix.diagonal (proj v) * A * Matrix.diagonal (proj v)

lemma del_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (v x y : ι) :
    del A v x y = if x = v ∨ y = v then 0 else A x y := by
  simp only [del, Matrix.diagonal_mul, Matrix.mul_diagonal, proj]
  by_cases hx : x = v <;> by_cases hy : y = v <;> simp [hx, hy]

noncomputable def Es {ι : Type*} [DecidableEq ι] (v : ι) : Matrix ι ι (PowerSeries ℤ) :=
  Matrix.diagonal fun x => if x = v then 1 else 0

lemma alpha {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (v : ι) :
    (ser A v v) • (ser A - ser (del A v) + Es v) = ser A * Es v * ser A := by
  refine alg (PowerSeries.X (R := ℤ)) (ser A v v) ((PowerSeries.C (R := ℤ)).mapMatrix A)
    ((PowerSeries.C (R := ℤ)).mapMatrix (del A v)) (Es v) (ser A) (ser (del A v))
    (ser_left A) (ser_right _) ?_ ?_ ?_
  · ext x y
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, del_apply, Es, sub_mul, mul_sub,
      Matrix.sub_apply, one_mul, mul_one, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.one_apply]
    by_cases hx : x = v <;> by_cases hy : y = v <;> simp [hx, hy]
  · ext x y
    simp only [Es, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
    split_ifs <;> simp
  · ext x y : 2
    simp only [Es, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_apply]
    by_cases hx : x = v <;> by_cases hy : y = v
    · subst hx; subst hy; simp
    · subst hx; simp [hy, Ne.symm hy]
    · subst hy; simp [hx, Ne.symm hx]
    · simp [hx, hy]

lemma coeff_ser {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (x y : ι) (k : ℕ) :
    coeff k (ser M x y) = (M ^ k) x y := by simp [ser]

lemma mul_Es_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (M M' : Matrix ι ι (PowerSeries ℤ))
    (v x y : ι) : (M * Es v * M') x y = M x v * M' v y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single v]
  · simp [Es, Matrix.mul_diagonal]
  · intro b _ hb; simp [Es, Matrix.mul_diagonal, hb]
  · simp

lemma sum_Es_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι) : ∑ x, Es v x x = 1 := by
  simp [Es, Matrix.diagonal_apply]

lemma sum_Es_all {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι) :
    ∑ x, ∑ y, Es v x y = 1 := by
  simp [Es, Matrix.diagonal_apply]

def cc {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (k : ℕ) (v : ι) : ℤ := (A ^ k) v v
def ww {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (k : ℕ) (v : ι) : ℤ :=
  ∑ y, (A ^ k) v y
def tr {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (k : ℕ) : ℤ := ∑ x, (A ^ k) x x
def WW {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (k : ℕ) : ℤ :=
  ∑ x, ∑ y, (A ^ k) x y

lemma trace_id {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (v : ι) (k : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, cc A p.1 v * (tr A p.2 - tr (del A v) p.2 + if p.2 = 0 then 1 else 0)
      = ((k : ℤ) + 1) * cc A k v := by
  have h := congrArg (fun M => ∑ x, M x x) (alpha A v)
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, mul_Es_mul] at h
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_Es_diag] at h
  have h' := congrArg (coeff k) h
  rw [coeff_mul, map_sum] at h'
  simp only [coeff_mul, map_add, map_sub, map_sum, coeff_ser, coeff_one] at h'
  rw [Finset.sum_comm] at h'
  have e : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k, ∑ x, (A ^ p.1) x v * (A ^ p.2) v x = cc A k v := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [cc, ← hp, add_comm, pow_add, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul] at h'
  push_cast at h'
  exact h'

lemma sum_id {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (hA : A.IsSymm) (v : ι)
    (k : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        cc A p.1 v * (WW A p.2 - WW (del A v) p.2 + if p.2 = 0 then 1 else 0)
      = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ww A p.1 v * ww A p.2 v := by
  have h := congrArg (fun M => ∑ x, ∑ y, M x y) (alpha A v)
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, mul_Es_mul] at h
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_Es_all] at h
  rw [← Finset.sum_mul] at h
  have h' := congrArg (coeff k) h
  simp only [coeff_mul, map_add, map_sub, map_sum, coeff_ser, coeff_one] at h'
  have e : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      (∑ x, (A ^ p.1) x v) * (∑ y, (A ^ p.2) v y) = ww A p.1 v * ww A p.2 v := by
    intro p _
    simp only [ww]
    congr 1
    exact Finset.sum_congr rfl fun x _ => (hA.pow p.1).apply v x
  rw [Finset.sum_congr rfl e] at h'
  exact h'

lemma peel (f : ℕ → ℕ → ℤ) (k : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), f p.1 p.2
      = f 0 (k + 1) + ∑ i ∈ Finset.range k, f (i + 1) (k - i) + f (k + 1) 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ']
  simp only [Nat.sub_self, Nat.sub_zero, Nat.add_sub_add_right]
  ring

lemma sum_mul_all {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℤ) :
    ∑ x, ∑ y, (A * B) x y = ∑ z, (∑ x, A x z) * (∑ y, B z y) := by
  simp only [Matrix.mul_apply, Finset.sum_mul_sum]
  calc ∑ x, ∑ y, ∑ z, A x z * B z y = ∑ x, ∑ z, ∑ y, A x z * B z y :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, A x z * B z y := Finset.sum_comm

def Good {V : Type*} [Fintype V] (c w : ℕ → V → ℤ) (τ W : ℕ → ℤ) (τc Wc : ℕ → V → ℤ) : Prop :=
  (∀ v, c 0 v = 1) ∧ (∀ v, w 0 v = 1) ∧
  (∀ (k : ℕ) (v : V), ((k : ℤ) + 1) * c (k + 1) v = (τ (k + 1) - τc (k + 1) v)
      + ∑ i ∈ Finset.range k, c (i + 1) v * (τ (k - i) - τc (k - i) v)) ∧
  (∀ (k : ℕ) (v : V), 2 * w (k + 1) v + ∑ i ∈ Finset.range k, w (i + 1) v * w (k - i) v
      = (W (k + 1) - Wc (k + 1) v)
        + ∑ i ∈ Finset.range k, c (i + 1) v * (W (k - i) - Wc (k - i) v) + c (k + 1) v) ∧
  (∀ k, ∑ v, c k v = τ k) ∧ (∀ k, ∑ v, w k v = W k) ∧
  (∀ k, W (k + 2) = ∑ v, w 1 v * w (k + 1) v)

lemma good {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (hA : A.IsSymm) :
    Good (cc A) (ww A) (tr A) (WW A) (fun k v => tr (del A v) k) (fun k v => WW (del A v) k) := by
  have tr0 : ∀ M : Matrix ι ι ℤ, tr M 0 = Fintype.card ι := fun M => by simp [tr]
  have WW0 : ∀ M : Matrix ι ι ℤ, WW M 0 = Fintype.card ι := fun M => by
    simp [WW, Matrix.one_apply]
  have c0 : ∀ v, cc A 0 v = 1 := fun v => by simp [cc]
  have w0 : ∀ v, ww A 0 v = 1 := fun v => by simp [ww, Matrix.one_apply]
  refine ⟨c0, w0, ?_, ?_, fun k => rfl, fun k => rfl, ?_⟩
  · intro k v
    have h := trace_id A v (k + 1)
    rw [peel (fun i j => cc A i v * (tr A j - tr (del A v) j + if j = 0 then 1 else 0))] at h
    have e : ∑ i ∈ Finset.range k, cc A (i + 1) v * (tr A (k - i) - tr (del A v) (k - i) +
        if k - i = 0 then 1 else 0) = ∑ i ∈ Finset.range k, cc A (i + 1) v *
          (tr A (k - i) - tr (del A v) (k - i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have : k - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
      simp [this]
    simp only at h
    rw [e, tr0, tr0, c0] at h
    simp only [↓reduceIte, Nat.add_one_ne_zero] at h
    beta_reduce
    push_cast at h
    linarith
  · intro k v
    have h := sum_id A hA v (k + 1)
    rw [peel (fun i j => cc A i v * (WW A j - WW (del A v) j + if j = 0 then 1 else 0)),
      peel (fun i j => ww A i v * ww A j v)] at h
    have e : ∑ i ∈ Finset.range k, cc A (i + 1) v * (WW A (k - i) - WW (del A v) (k - i) +
        if k - i = 0 then 1 else 0) = ∑ i ∈ Finset.range k, cc A (i + 1) v *
          (WW A (k - i) - WW (del A v) (k - i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have : k - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
      simp [this]
    simp only at h
    rw [e, WW0, WW0, c0, w0] at h
    simp only [↓reduceIte, Nat.add_one_ne_zero] at h
    beta_reduce
    linarith
  · intro k
    rw [WW, pow_succ' A (k + 1), sum_mul_all]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [ww, pow_one]
    congr 1
    exact Finset.sum_congr rfl fun x _ => hA.apply z x

theorem hagos_induction {V : Type*} [Fintype V] (hn : 3 ≤ Fintype.card V)
    (c c' w w' : ℕ → V → ℤ) (τ τ' W W' : ℕ → ℤ) (τc Wc : ℕ → V → ℤ)
    (hG : Good c w τ W τc Wc) (hH : Good c' w' τ' W' τc Wc) :
    ∀ k, τ k = τ' k ∧ W k = W' k ∧ (∀ v, c k v = c' k v) ∧ (∀ v, w k v = w' k v) := by
  obtain ⟨hc0, hw0, hI, hII, hτ, hW, hsp⟩ := hG
  obtain ⟨hc0', hw0', hI', hII', hτ', hW', hsp'⟩ := hH
  have hnZ : (3 : ℤ) ≤ (Fintype.card V : ℤ) := by exact_mod_cast hn
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · refine ⟨?_, ?_, fun v => by rw [hc0, hc0'], fun v => by rw [hw0, hw0']⟩
      · rw [← hτ, ← hτ']; exact Finset.sum_congr rfl fun v _ => by rw [hc0, hc0']
      · rw [← hW, ← hW']; exact Finset.sum_congr rfl fun v _ => by rw [hw0, hw0']
    · -- step k + 1
      have ihτ : ∀ j, j ≤ k → τ j = τ' j := fun j hj => (ih j (by omega)).1
      have ihW : ∀ j, j ≤ k → W j = W' j := fun j hj => (ih j (by omega)).2.1
      have ihc : ∀ j, j ≤ k → ∀ v, c j v = c' j v := fun j hj => (ih j (by omega)).2.2.1
      have ihw : ∀ j, j ≤ k → ∀ v, w j v = w' j v := fun j hj => (ih j (by omega)).2.2.2
      -- (I): (k+1) δc = δτ
      have hc : ∀ v, ((k : ℤ) + 1) * (c (k + 1) v - c' (k + 1) v) = τ (k + 1) - τ' (k + 1) := by
        intro v
        have e : ∑ i ∈ Finset.range k, c (i + 1) v * (τ (k - i) - τc (k - i) v)
            = ∑ i ∈ Finset.range k, c' (i + 1) v * (τ' (k - i) - τc (k - i) v) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' := Finset.mem_range.mp hi
          rw [ihc (i + 1) (by omega) v, ihτ (k - i) (by omega)]
        have h1 := hI k v
        have h2 := hI' k v
        rw [e] at h1
        linarith
      -- (II): 2 δw = δW + δc
      have hw : ∀ v, 2 * (w (k + 1) v - w' (k + 1) v)
          = (W (k + 1) - W' (k + 1)) + (c (k + 1) v - c' (k + 1) v) := by
        intro v
        have e1 : ∑ i ∈ Finset.range k, w (i + 1) v * w (k - i) v
            = ∑ i ∈ Finset.range k, w' (i + 1) v * w' (k - i) v := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' := Finset.mem_range.mp hi
          rw [ihw (i + 1) (by omega) v, ihw (k - i) (by omega) v]
        have e2 : ∑ i ∈ Finset.range k, c (i + 1) v * (W (k - i) - Wc (k - i) v)
            = ∑ i ∈ Finset.range k, c' (i + 1) v * (W' (k - i) - Wc (k - i) v) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' := Finset.mem_range.mp hi
          rw [ihc (i + 1) (by omega) v, ihW (k - i) (by omega)]
        have h1 := hII k v
        have h2 := hII' k v
        rw [e1, e2] at h1
        linarith
      -- sums over v
      have sc : ((k : ℤ) + 1) * (τ (k + 1) - τ' (k + 1))
          = (Fintype.card V : ℤ) * (τ (k + 1) - τ' (k + 1)) := by
        have L : ∑ v : V, ((k : ℤ) + 1) * (c (k + 1) v - c' (k + 1) v)
            = ((k : ℤ) + 1) * (τ (k + 1) - τ' (k + 1)) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, hτ, hτ']
        have R : ∑ _v : V, (τ (k + 1) - τ' (k + 1))
            = (Fintype.card V : ℤ) * (τ (k + 1) - τ' (k + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← L, ← R]
        exact Finset.sum_congr rfl fun v _ => hc v
      have sw : 2 * (W (k + 1) - W' (k + 1))
          = (Fintype.card V : ℤ) * (W (k + 1) - W' (k + 1)) + (τ (k + 1) - τ' (k + 1)) := by
        have L : ∑ v : V, 2 * (w (k + 1) v - w' (k + 1) v) = 2 * (W (k + 1) - W' (k + 1)) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, hW, hW']
        have R : ∑ v : V, ((W (k + 1) - W' (k + 1)) + (c (k + 1) v - c' (k + 1) v))
            = (Fintype.card V : ℤ) * (W (k + 1) - W' (k + 1)) + (τ (k + 1) - τ' (k + 1)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, hτ, hτ']
          ring
        rw [← L, ← R]
        exact Finset.sum_congr rfl fun v _ => hw v
      -- the two global differences vanish
      have hWz : W (k + 1) - W' (k + 1) = 0 ∧ τ (k + 1) - τ' (k + 1) = 0 := by
        by_cases hk : k = 0
        · -- length 1: needs card ≠ 1 and card ≠ 2
          have hkZ : (k : ℤ) = 0 := by exact_mod_cast hk
          have h1 : ((Fintype.card V : ℤ) - 1) * (τ (k + 1) - τ' (k + 1)) = 0 := by
            have := sc; rw [hkZ] at this; linarith
          have hτ0 : τ (k + 1) - τ' (k + 1) = 0 := by
            rcases mul_eq_zero.mp h1 with h | h
            · omega
            · exact h
          have h2 : ((Fintype.card V : ℤ) - 2) * (W (k + 1) - W' (k + 1)) = 0 := by
            have := sw; linarith
          have hW0 : W (k + 1) - W' (k + 1) = 0 := by
            rcases mul_eq_zero.mp h2 with h | h
            · omega
            · exact h
          exact ⟨hW0, hτ0⟩
        · -- length ≥ 2: the split W (j + 2) = Σ w 1 * w (j + 1)
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          have hWeq : W (j + 1 + 1) = W' (j + 1 + 1) := by
            show W (j + 2) = W' (j + 2)
            rw [hsp j, hsp' j]
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [ihw 1 (by omega) v, ihw (j + 1) (by omega) v]
          have hW0 : W (j + 1 + 1) - W' (j + 1 + 1) = 0 := by linarith
          have hτ0 : τ (j + 1 + 1) - τ' (j + 1 + 1) = 0 := by
            have := sw; rw [hW0] at this; simp only [mul_zero, zero_add] at this; linarith
          exact ⟨hW0, hτ0⟩
      obtain ⟨hW0, hτ0⟩ := hWz
      have hcv : ∀ v, c (k + 1) v = c' (k + 1) v := by
        intro v
        have h := hc v
        rw [hτ0] at h
        have hk : ((k : ℤ) + 1) ≠ 0 := by positivity
        have := (mul_eq_zero.mp h).resolve_left hk
        linarith
      refine ⟨by linarith, by linarith, hcv, ?_⟩
      intro v
      have h := hw v
      rw [hW0, hcv v] at h
      linarith


lemma ww_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (k : ℕ) (u : ι) :
    ww A (k + 1) u = ∑ x, A u x * ww A k x := by
  simp only [ww, pow_succ', Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma submatrix_pow_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (φ : ι ≃ ι) (k : ℕ) : (M.submatrix φ φ) ^ k = (M ^ k).submatrix φ φ := by
  induction k with
  | zero => simp [Matrix.submatrix_one_equiv]
  | succ k ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, pow_succ]

lemma card_tr {n : ℕ} (G K : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel K.Adj]
    (v : Fin n) (e : G.induce ({v}ᶜ : Set (Fin n)) ≃g K.induce ({v}ᶜ : Set (Fin n))) (k : ℕ) :
    tr (del (K.adjMatrix ℤ) v) k = tr (del (G.adjMatrix ℤ) v) k ∧
      WW (del (K.adjMatrix ℤ) v) k = WW (del (G.adjMatrix ℤ) v) k := by
  set φ : Fin n ≃ Fin n := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.extE e with hφ
  have hφv : φ v = v := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.extE_a e
  have hφne : ∀ x, x ≠ v → φ x ≠ v := by
    intro x hx h
    apply hx
    apply φ.injective
    rw [h, hφv]
  have hsub : (del (K.adjMatrix ℤ) v).submatrix φ φ = del (G.adjMatrix ℤ) v := by
    ext x y
    rw [Matrix.submatrix_apply, del_apply, del_apply]
    by_cases hx : x = v
    · subst hx; simp [hφv]
    by_cases hy : y = v
    · subst hy; simp [hφv]
    have h := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.extE_adj e x y hx hy
    rw [← hφ] at h
    simp only [hx, hy, hφne x hx, hφne y hy, or_self, ite_false, SimpleGraph.adjMatrix_apply, h]
  have hp : (del (G.adjMatrix ℤ) v) ^ k = ((del (K.adjMatrix ℤ) v) ^ k).submatrix φ φ := by
    rw [← hsub, submatrix_pow_equiv]
  constructor
  · simp only [tr, hp, Matrix.submatrix_apply]
    exact (Equiv.sum_comp φ (fun x => ((del (K.adjMatrix ℤ) v) ^ k) x x)).symm
  · simp only [WW, hp, Matrix.submatrix_apply]
    rw [← Equiv.sum_comp φ (fun x => ∑ y, ((del (K.adjMatrix ℤ) v) ^ k) x y)]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact (Equiv.sum_comp φ (fun y => ((del (K.adjMatrix ℤ) v) ^ k) (φ x) y)).symm

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degree_corank_one

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degree_corank_one : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degree_corank_one := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degree_corank_one in
  intro n hn G hP H ⟨σ, hσ⟩
  classical
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
  have hH := hagos_induction hn' _ _ _ _ _ _ _ _ _ _ hgG hgK
  have hww : ∀ k v, ww AG k v = ww AK k v := fun k v => (hH k).2.2.2 v
  have hw0 : ∀ x : Fin n, ww AG 0 x = 1 := hgG.2.1
  have hws : ∀ k : ℕ, ∀ x : Fin n, ww AG (k + 1) x =
      ∑ y : Fin n, Set.indicator (G.neighborSet x) (ww AG k) y := by
    intro k x
    rw [ww_succ]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Set.indicator_apply, hAG, SimpleGraph.adjMatrix_apply]
    by_cases h : G.Adj x y
    · have h' : y ∈ G.neighborSet x := h
      simp [h, h']
    · have h' : y ∉ G.neighborSet x := h
      simp [h, h']
  let r : Fin n → Fin n → ℤ := fun u x => AK u x - AG u x
  have hr1 : ∀ u : Fin n, ∀ k : ℕ, ∑ x : Fin n, r u x * ww AG k x = 0 := by
    intro u k
    simp only [r, sub_mul, Finset.sum_sub_distrib]
    have q : ∑ x, AK u x * ww AG k x = ∑ x, AK u x * ww AK k x :=
      Finset.sum_congr rfl fun x _ => by rw [hww]
    rw [q, ← ww_succ, ← ww_succ, hww]
    ring
  have hr2 : ∀ u : Fin n, ∀ j : ℕ,
      ∑ x : Fin n, Set.indicator {x : Fin n | (G.neighborSet x).ncard = j} (r u) x = 0 := by
    intro u j
    have hb := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__aligned_switch_kelly4.nbr_bal hdeg u (g u) j
    rw [Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__aligned_switch_kelly4.ncard_eq_filter, Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__aligned_switch_kelly4.ncard_eq_filter] at hb
    have q : ∑ x : Fin n, Set.indicator {x : Fin n | (G.neighborSet x).ncard = j} (r u) x =
        ∑ x : Fin n, ((if K.Adj u x ∧ (G.neighborSet x).ncard = j then (1 : ℤ) else 0) -
          (if G.Adj u x ∧ (G.neighborSet x).ncard = j then (1 : ℤ) else 0)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Set.indicator_apply]
      simp only [r, hAG, hAK, SimpleGraph.adjMatrix_apply, Set.mem_ofPred_eq]
      by_cases h1 : (G.neighborSet x).ncard = j <;> by_cases h2 : K.Adj u x <;>
        by_cases h3 : G.Adj u x <;>
        simp only [h1, h2, h3, ite_true, ite_false, and_true, and_false, true_and, false_and] <;>
        norm_num
    rw [q, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hb]
    ring
  have hsym : ∀ u x, r u x = r x u := by
    intro u x
    simp only [r, hAG, hAK, SimpleGraph.adjMatrix_apply, G.adj_comm, K.adj_comm]
  have hdiag : ∀ u, r u u = 0 := by
    intro u
    simp [r, hAG, hAK, SimpleGraph.adjMatrix_apply]
  have hzero : ∀ u x, r u x = 0 := by
    intro u x
    by_contra hne
    obtain ⟨a, b, hab, hl⟩ := hP (ww AG) hw0 hws (r u) (r x) (hr1 u) (hr2 u) (hr1 x) (hr2 x)
    have h1 := hl x
    rw [hdiag x, mul_zero, add_zero] at h1
    have ha : a = 0 := (mul_eq_zero.mp h1).resolve_right hne
    have hb : b ≠ 0 := by rcases hab with h | h
                          · exact absurd ha h
                          · exact h
    have h2 := hl u
    rw [hdiag u, ha, zero_mul, zero_add] at h2
    have := (mul_eq_zero.mp h2).resolve_left hb
    exact hne (by rw [hsym]; exact this)
  have hadj : ∀ u x, K.Adj u x ↔ G.Adj u x := by
    intro u x
    have h := hzero u x
    simp only [r, hAG, hAK, SimpleGraph.adjMatrix_apply] at h
    by_cases h1 : K.Adj u x <;> by_cases h2 : G.Adj u x <;> simp_all
  have eGK : G ≃g K := { toEquiv := Equiv.refl _, map_rel_iff' := fun {a b} => hadj a b }
  exact ⟨eGK.trans eKH⟩
