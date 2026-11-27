import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__low_extension_pair
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__three_extensions
import Recon.Checked.L_found_hypomorphic_iso_invariant

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__low_extension_pair

open Classical

variable {n : ℕ}

noncomputable def zf (A B : SimpleGraph (Fin n)) (u y : Fin n) : ℤ :=
  (if A.Adj u y then 1 else 0) - (if B.Adj u y then 1 else 0)

noncomputable def Az (G : SimpleGraph (Fin n)) (g : Fin n → ℤ) (x : Fin n) : ℤ :=
  ∑ y, if G.Adj x y then g y else 0

noncomputable def kk (A B : SimpleGraph (Fin n)) (u : Fin n) : ℤ :=
  ∑ y, if (A.Adj u y ∧ ¬ B.Adj u y) then 1 else 0

def AG (A B : SimpleGraph (Fin n)) (u : Fin n) : Prop :=
  ∀ x y : Fin n, x ≠ u → y ≠ u → (A.Adj x y ↔ B.Adj x y)

noncomputable def dg (K : SimpleGraph (Fin n)) (x : Fin n) : ℕ := (K.neighborSet x).ncard

noncomputable def lam (d : ℕ) (G : SimpleGraph (Fin n)) (θ : ℤ) (u : Fin n) : ℤ :=
  θ - if dg G u = d + 1 then 1 else 0

def Ctx (n d : ℕ) (G : SimpleGraph (Fin n)) (θ : ℤ) : Prop :=
  (∀ K : SimpleGraph (Fin n), Recon.Hypomorphic G K → ∀ x, dg K x = d ∨ dg K x = d + 1) ∧
  (∀ K : SimpleGraph (Fin n), Recon.Hypomorphic G K → ∀ u : Fin n,
    ∃ K' : SimpleGraph (Fin n), Recon.Hypomorphic G K' ∧ AG K K' u ∧ K' ≠ K) ∧
  (∀ K₁ K₂ : SimpleGraph (Fin n), Recon.Hypomorphic G K₁ → Recon.Hypomorphic G K₂ →
    ∀ u : Fin n, AG K₁ K₂ u → ∀ x : Fin n,
      (dg K₁ x : ℤ) = dg K₂ x + zf K₁ K₂ u x ∧
      (x ≠ u → Az K₁ (zf K₁ K₂ u) x = (θ - if dg K₁ u = d + 1 then 1 else 0) * zf K₁ K₂ u x)) ∧
  (∀ K K₁ K₂ : SimpleGraph (Fin n), Recon.Hypomorphic G K → Recon.Hypomorphic G K₁ →
    Recon.Hypomorphic G K₂ → ∀ u : Fin n, AG K K₁ u → AG K K₂ u → K₁ ≠ K → K₂ ≠ K →
      kk K K₁ u = kk K K₂ u ∧ ∀ x : Fin n, dg K x = dg K u → (K₁.Adj u x ↔ K₂.Adj u x))

lemma ncard_sum (P : Fin n → Prop) [DecidablePred P] :
    ((Set.ncard {y | P y} : ℕ) : ℤ) = ∑ y, if P y then (1 : ℤ) else 0 := by
  rw [Set.ncard_eq_toFinset_card', Finset.sum_boole]
  simp

lemma dg_sum (K : SimpleGraph (Fin n)) (x : Fin n) :
    ((dg K x : ℕ) : ℤ) = ∑ y, if K.Adj x y then (1 : ℤ) else 0 :=
  ncard_sum (fun y => K.Adj x y)

lemma zf_one {A B : SimpleGraph (Fin n)} {u y : Fin n} :
    zf A B u y = 1 ↔ A.Adj u y ∧ ¬ B.Adj u y := by
  unfold zf; split_ifs <;> simp_all

lemma zf_neg {A B : SimpleGraph (Fin n)} {u y : Fin n} :
    zf A B u y = -1 ↔ ¬ A.Adj u y ∧ B.Adj u y := by
  unfold zf; split_ifs <;> simp_all

lemma zf_range (A B : SimpleGraph (Fin n)) (u y : Fin n) :
    zf A B u y = 1 ∨ zf A B u y = 0 ∨ zf A B u y = -1 := by
  unfold zf; split_ifs <;> simp

lemma zf_self (A B : SimpleGraph (Fin n)) (u : Fin n) : zf A B u u = 0 := by
  simp [zf]

lemma sum_zf (A B : SimpleGraph (Fin n)) (u : Fin n) :
    ∑ y, zf A B u y = (dg A u : ℤ) - dg B u := by
  rw [dg_sum, dg_sum, ← Finset.sum_sub_distrib]
  rfl

lemma kk_sub (A B : SimpleGraph (Fin n)) (u : Fin n) :
    kk A B u - kk B A u = ∑ y, zf A B u y := by
  unfold kk zf
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs <;> simp_all

lemma kk_one (A B : SimpleGraph (Fin n)) (u : Fin n) :
    kk A B u = ∑ y, if zf A B u y = 1 then (1 : ℤ) else 0 := by
  unfold kk
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have := @zf_one _ A B u y
  split_ifs <;> first | rfl | (exfalso; tauto)

lemma kk_neg (A B : SimpleGraph (Fin n)) (u : Fin n) :
    kk B A u = ∑ y, if zf A B u y = -1 then (1 : ℤ) else 0 := by
  unfold kk
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have := @zf_neg _ A B u y
  split_ifs <;> first | rfl | (exfalso; tauto)

lemma exists_of_pos (P : Fin n → Prop) [DecidablePred P] (h : 1 ≤ ∑ y, if P y then (1 : ℤ) else 0) :
    ∃ y, P y := by
  by_contra hc
  push Not at hc
  simp [hc] at h

lemma one_le_of (P : Fin n → Prop) (y : Fin n) (hy : P y) :
    1 ≤ ∑ y, if P y then (1 : ℤ) else 0 := by
  have := Finset.single_le_sum (f := fun y => if P y then (1 : ℤ) else 0)
    (fun i _ => by positivity) (Finset.mem_univ y)
  simpa [hy] using this

lemma eq_of_ag {A B : SimpleGraph (Fin n)} {v : Fin n} (h : AG A B v)
    (hv : ∀ y, A.Adj v y ↔ B.Adj v y) : A = B := by
  ext a b
  by_cases ha : a = v
  · subst ha; exact hv b
  · by_cases hb : b = v
    · subst hb; rw [A.adj_comm, B.adj_comm]; exact hv a
    · exact h a b ha hb

lemma pair (G : SimpleGraph (Fin n)) (f g : Fin n → ℤ) :
    ∑ x, g x * Az G f x = ∑ x, f x * Az G g x := by
  unfold Az
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [G.adj_comm y x]
  split_ifs <;> ring

lemma Az_sub (G : SimpleGraph (Fin n)) (f g : Fin n → ℤ) (x : Fin n) :
    Az G (fun y => f y - g y) x = Az G f x - Az G g x := by
  unfold Az
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs <;> ring


variable {d : ℕ} {G : SimpleGraph (Fin n)} {θ : ℤ}

lemma hrefl (G : SimpleGraph (Fin n)) : Recon.Hypomorphic G G := Recon.anchor_hypomorphic_refl G

lemma deg_eq (h : Ctx n d G θ) {X Y : SimpleGraph (Fin n)} {v : Fin n}
    (hX : Recon.Hypomorphic G X) (hY : Recon.Hypomorphic G Y) (hXY : AG X Y v) :
    dg X v = dg Y v := by
  have := (h.2.2.1 X Y hX hY v hXY v).1
  rw [zf_self] at this
  omega

lemma kk_symm (h : Ctx n d G θ) {X Y : SimpleGraph (Fin n)} {v : Fin n}
    (hX : Recon.Hypomorphic G X) (hY : Recon.Hypomorphic G Y) (hXY : AG X Y v) :
    kk X Y v = kk Y X v := by
  have := kk_sub X Y v
  rw [sum_zf, deg_eq h hX hY hXY] at this
  linarith

lemma z_one (h : Ctx n d G θ) {X : SimpleGraph (Fin n)} {v : Fin n}
    (hX : Recon.Hypomorphic G X) (hag : AG G X v) (y : Fin n) (hy : zf G X v y = 1) :
    dg G y = d + 1 := by
  have e := (h.2.2.1 G X (hrefl G) hX v hag y).1
  rw [hy] at e
  rcases h.1 X hX y with h1 | h1 <;> rcases h.1 G (hrefl G) y with h2 | h2 <;> omega

lemma z_neg (h : Ctx n d G θ) {X : SimpleGraph (Fin n)} {v : Fin n}
    (hX : Recon.Hypomorphic G X) (hag : AG G X v) (y : Fin n) (hy : zf G X v y = -1) :
    dg G y = d := by
  have e := (h.2.2.1 G X (hrefl G) hX v hag y).1
  rw [hy] at e
  rcases h.1 X hX y with h1 | h1 <;> rcases h.1 G (hrefl G) y with h2 | h2 <;> omega

lemma AZ (h : Ctx n d G θ) {X : SimpleGraph (Fin n)} {v : Fin n}
    (hX : Recon.Hypomorphic G X) (hag : AG G X v) (y : Fin n) :
    Az G (zf G X v) y = lam d G θ v * zf G X v y + if y = v then kk G X v else 0 := by
  by_cases hy : y = v
  · subst hy
    rw [zf_self, if_pos rfl, mul_zero, zero_add]
    unfold Az kk zf
    refine Finset.sum_congr rfl (fun w _ => ?_)
    split_ifs <;> simp_all
  · rw [if_neg hy, add_zero]
    exact (h.2.2.1 G X (hrefl G) hX v hag y).2 hy

lemma AZ' (h : Ctx n d G θ) {X : SimpleGraph (Fin n)} {v : Fin n}
    (hX : Recon.Hypomorphic G X) (hag : AG G X v) (g : Fin n → ℤ) :
    ∑ x, g x * Az G (zf G X v) x = lam d G θ v * (∑ x, zf G X v x * g x) + kk G X v * g v := by
  have e : ∀ x, g x * Az G (zf G X v) x =
      lam d G θ v * (zf G X v x * g x) + if x = v then kk G X v * g x else 0 := by
    intro x
    rw [AZ h hX hag x]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq']
  simp

lemma kk_pos (h : Ctx n d G θ) {X : SimpleGraph (Fin n)} {v : Fin n}
    (hX : Recon.Hypomorphic G X) (hag : AG G X v) (hne : X ≠ G) : 1 ≤ kk G X v := by
  have : ∃ y, ¬ (G.Adj v y ↔ X.Adj v y) := by
    by_contra hc
    push Not at hc
    exact hne (eq_of_ag hag hc).symm
  obtain ⟨y, hy⟩ := this
  by_cases hg : G.Adj v y
  · have hx : ¬ X.Adj v y := fun hx => hy ⟨fun _ => hx, fun _ => hg⟩
    have := one_le_of (fun y => G.Adj v y ∧ ¬ X.Adj v y) y ⟨hg, hx⟩
    unfold kk; refine le_of_le_of_eq this ?_; congr 1; ext z; congr
  · have hx : X.Adj v y := by by_contra hx; exact hy ⟨fun g => absurd g hg, fun x => absurd x hx⟩
    rw [kk_symm h (hrefl G) hX hag]
    have := one_le_of (fun y => X.Adj v y ∧ ¬ G.Adj v y) y ⟨hx, hg⟩
    unfold kk; refine le_of_le_of_eq this ?_; congr 1; ext z; congr

lemma lam_low {v : Fin n} (hv : dg G v = d) : lam d G θ v = θ := by
  unfold lam; rw [if_neg (by omega)]; ring

lemma lam_high {v : Fin n} (hv : dg G v = d + 1) : lam d G θ v = θ - 1 := by
  unfold lam; rw [if_pos hv]

/-- Step 1 lemma. -/
lemma S1 (h : Ctx n d G θ) (f : Fin n → ℤ) (hf : ∀ x, Az G f x = θ * f x)
    (hf0 : ∀ x, dg G x = d → f x = 0) (hf1 : ∀ x, f x ≤ 1) (w : Fin n) (hw : dg G w = d + 1)
    (K' : SimpleGraph (Fin n)) (hK : Recon.Hypomorphic G K') (hag : AG G K' w) (hfw : f w = 1) :
    ∀ x, zf G K' w x = 1 → f x = 1 := by
  have e := pair G f (zf G K' w)
  rw [AZ' h hK hag f, lam_high hw, hfw] at e
  simp only [hf] at e
  have e2 : ∑ x, zf G K' w x * (θ * f x) = θ * ∑ x, zf G K' w x * f x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => by ring)
  rw [e2] at e
  have hS : ∑ x, zf G K' w x * f x = kk G K' w := by linarith
  rw [kk_one] at hS
  have hnn : ∀ x ∈ Finset.univ, 0 ≤ (if zf G K' w x = 1 then (1 : ℤ) else 0) - zf G K' w x * f x := by
    intro x _
    rcases zf_range G K' w x with hz | hz | hz
    · rw [if_pos hz, hz]; linarith [hf1 x]
    · rw [hz]; simp
    · rw [hz, hf0 x (z_neg h hK hag x hz)]; simp
  have hsum : ∑ x, ((if zf G K' w x = 1 then (1 : ℤ) else 0) - zf G K' w x * f x) = 0 := by
    rw [Finset.sum_sub_distrib]; linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
  intro x hx
  have hx' := this x (Finset.mem_univ x)
  rw [if_pos hx, hx] at hx'
  linarith


lemma ag_symm {A B : SimpleGraph (Fin n)} {v : Fin n} (h : AG A B v) : AG B A v :=
  fun x y hx hy => (h x y hx hy).symm

lemma ag_trans {A B C : SimpleGraph (Fin n)} {v : Fin n} (h1 : AG A B v) (h2 : AG B C v) :
    AG A C v :=
  fun x y hx hy => (h1 x y hx hy).trans (h2 x y hx hy)

lemma PairF (h : Ctx n d G θ) {v : Fin n} (hv : dg G v = d) {A B : SimpleGraph (Fin n)}
    (hA : Recon.Hypomorphic G A) (hagA : AG G A v) (hB : Recon.Hypomorphic G B) (hagB : AG G B v)
    (hAG : A ≠ G) (hBG : B ≠ G) (hAB : A ≠ B) :
    (∀ x, Az G (fun y => zf G A v y - zf G B v y) x = θ * (zf G A v x - zf G B v x)) ∧
    (∀ x, dg G x = d → zf G A v x - zf G B v x = 0) ∧
    (∀ x, zf G A v x - zf G B v x ≤ 1) ∧
    (∀ x, zf G A v x = 1 → zf G A v x - zf G B v x = 1) := by
  obtain ⟨hkAB, hlow⟩ := h.2.2.2 G A B (hrefl G) hA hB v hagA hagB hAG hBG
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [Az_sub, AZ h hA hagA, AZ h hB hagB, lam_low hv, hkAB]
    ring
  · intro x hx
    have e := hlow x (by rw [hx, hv])
    unfold zf
    by_cases ha : A.Adj v x
    · have hb := e.1 ha
      simp [ha, hb]
    · have hb : ¬ B.Adj v x := fun hb => ha (e.2 hb)
      simp [ha, hb]
  · intro x
    rcases zf_range G A v x with ha | ha | ha
    · have hxh := z_one h hA hagA x ha
      rcases zf_range G B v x with hb | hb | hb
      · rw [ha, hb]; norm_num
      · rw [ha, hb]; norm_num
      · have := z_neg h hB hagB x hb; omega
    · rcases zf_range G B v x with hb | hb | hb <;> rw [ha, hb] <;> norm_num
    · rcases zf_range G B v x with hb | hb | hb <;> rw [ha, hb] <;> norm_num
  · intro x hx
    have hxh := z_one h hA hagA x hx
    obtain ⟨hGx, hAx⟩ := zf_one.1 hx
    have e := (h.2.2.1 G A (hrefl G) hA v hagA x).1
    rw [hx] at e
    have hdA : dg A x = d := by omega
    have hdAv : dg A v = d := by rw [deg_eq h hA (hrefl G) (ag_symm hagA)]; exact hv
    have hB3 := (h.2.2.2 A G B hA (hrefl G) hB v (ag_symm hagA) (ag_trans (ag_symm hagA) hagB)
      (Ne.symm hAG) (fun e => hAB e.symm)).2 x (by rw [hdA, hdAv])
    have hBx := hB3.1 hGx
    have : zf G B v x = 0 := by unfold zf; simp [hGx, hBx]
    rw [hx, this]; norm_num

lemma core (h : Ctx n d G θ)
    (hP : ∀ v, dg G v = d → ∃ A B : SimpleGraph (Fin n), Recon.Hypomorphic G A ∧ AG G A v ∧
      Recon.Hypomorphic G B ∧ AG G B v ∧ A ≠ G ∧ B ≠ G ∧ A ≠ B) :
    ∀ m : ℕ, ∀ v, dg G v = d → ∀ A B : SimpleGraph (Fin n), Recon.Hypomorphic G A → AG G A v →
      Recon.Hypomorphic G B → AG G B v → A ≠ G → B ≠ G → A ≠ B → kk G A v ≤ m → False := by
  intro m
  induction m with
  | zero =>
    intro v hv A B hA hagA hB hagB hAG hBG hAB hk
    have := kk_pos h hA hagA hAG
    push_cast at hk
    omega
  | succ m ih =>
    intro v hv A B hA hagA hB hagB hAG hBG hAB hk
    obtain ⟨hf, hf0, hf1, hf4⟩ := PairF h hv hA hagA hB hagB hAG hBG hAB
    obtain ⟨w, hzw⟩ : ∃ w, zf G A v w = 1 :=
      exists_of_pos _ (by rw [← kk_one]; exact kk_pos h hA hagA hAG)
    have hwh := z_one h hA hagA w hzw
    obtain ⟨K', hK', hagK, hK'G⟩ := h.2.1 G (hrefl G) w
    have hS1 := S1 h (fun y => zf G A v y - zf G B v y) hf hf0 hf1 w hwh K' hK' hagK (hf4 w hzw)
    have hR : ∀ x, zf G K' w x = 1 → zf G A v x = 1 := by
      intro x hx
      have h1 : zf G A v x - zf G B v x = 1 := hS1 x hx
      have hxh := z_one h hK' hagK x hx
      have hb' : zf G B v x ≠ -1 := fun hb => by have := z_neg h hB hagB x hb; omega
      rcases zf_range G A v x with ha | ha | ha <;> rcases zf_range G B v x with hb | hb | hb <;>
        omega
    have hk' : kk G K' w ≤ kk G A v - 1 := by
      rw [kk_one G K' w, kk_one G A v]
      have : ∑ x, (if zf G K' w x = 1 then (1:ℤ) else 0) ≤
          ∑ x, ((if zf G A v x = 1 then (1:ℤ) else 0) - if x = w then 1 else 0) := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hxw : x = w
        · subst hxw; simp [zf_self, hzw]
        · simp only [hxw, if_false, sub_zero]
          by_cases hx : zf G K' w x = 1
          · simp [hx, hR x hx]
          · simp only [hx, if_false]; split_ifs <;> norm_num
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq'] at this
      simpa using this
    have hk'pos := kk_pos h hK' hagK hK'G
    obtain ⟨v', hv'⟩ : ∃ v', zf G K' w v' = -1 :=
      exists_of_pos _ (by rw [← kk_neg, ← kk_symm h (hrefl G) hK' hagK]; exact hk'pos)
    have hv'l := z_neg h hK' hagK v' hv'
    have hnadj : ¬ G.Adj w v' := (zf_neg.1 hv').1
    obtain ⟨M1, M2, hM1, hagM1, hM2, hagM2, hM1G, hM2G, hM12⟩ := hP v' hv'l
    obtain ⟨g1, g0, g1', g4⟩ := PairF h hv'l hM1 hagM1 hM2 hagM2 hM1G hM2G hM12
    have hzw0 : ∀ M, Recon.Hypomorphic G M → AG G M v' → zf G M v' w = 0 := by
      intro M hM hag
      rcases zf_range G M v' w with hz | hz | hz
      · exact absurd (zf_one.1 hz).1.symm hnadj
      · exact hz
      · have := z_neg h hM hag w hz; omega
    have hclaim : ∀ x, zf G K' w x = 1 → zf G M1 v' x ≠ 1 := by
      intro x hx hm
      have hxh := z_one h hK' hagK x hx
      obtain ⟨K'', hK'', hagK'', hK''G⟩ := h.2.1 G (hrefl G) x
      have e1 := AZ' h hK' hagK (zf G K'' x)
      have e2 := AZ' h hK'' hagK'' (zf G K' w)
      have e3 := pair G (zf G K' w) (zf G K'' x)
      rw [lam_high hwh] at e1
      rw [lam_high hxh, hx] at e2
      have hc : ∑ y, zf G K' w y * zf G K'' x y = ∑ y, zf G K'' x y * zf G K' w y :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      rw [hc] at e1
      have hkk'' := kk_pos h hK'' hagK'' hK''G
      have hzw : zf G K'' x w = 1 := by
        rcases zf_range G K'' x w with hz | hz | hz
        · exact hz
        · rw [hz] at e1; linarith
        · have := z_neg h hK'' hagK'' w hz; omega
      have := S1 h (fun y => zf G M1 v' y - zf G M2 v' y) g1 g0 g1' x hxh K'' hK'' hagK''
        (g4 x hm) w hzw
      rw [hzw0 M1 hM1 hagM1, hzw0 M2 hM2 hagM2] at this
      norm_num at this
    have e1 := AZ' h hM1 hagM1 (zf G K' w)
    have e2 := AZ' h hK' hagK (zf G M1 v')
    have e3 := pair G (zf G M1 v') (zf G K' w)
    rw [lam_low hv'l, hv'] at e1
    rw [lam_high hwh, hzw0 M1 hM1 hagM1] at e2
    have hc : ∑ y, zf G K' w y * zf G M1 v' y = ∑ y, zf G M1 v' y * zf G K' w y :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [hc] at e2
    have hP1 : ∑ y, zf G M1 v' y * zf G K' w y = kk G M1 v' := by linarith
    have hle : ∑ y, zf G M1 v' y * zf G K' w y ≤ kk G K' w - 1 := by
      rw [kk_symm h (hrefl G) hK' hagK, kk_neg G K' w]
      have : ∑ y, zf G M1 v' y * zf G K' w y ≤
          ∑ y, ((if zf G K' w y = -1 then (1:ℤ) else 0) - if y = v' then 1 else 0) := by
        apply Finset.sum_le_sum
        intro y _
        by_cases hyv : y = v'
        · subst hyv; simp [zf_self, hv']
        · simp only [hyv, if_false, sub_zero]
          rcases zf_range G K' w y with hz | hz | hz
          · have hm0 : zf G M1 v' y = 0 := by
              rcases zf_range G M1 v' y with hm | hm | hm
              · exact absurd hm (hclaim y hz)
              · exact hm
              · have := z_neg h hM1 hagM1 y hm; have := z_one h hK' hagK y hz; omega
            rw [hm0, hz]; norm_num
          · rw [hz]; norm_num
          · rw [hz]; rcases zf_range G M1 v' y with hm | hm | hm <;> rw [hm] <;> norm_num
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq'] at this
      simpa using this
    have hmk : kk G M1 v' ≤ m := by push_cast at hk; linarith
    exact ih v' hv'l M1 M2 hM1 hagM1 hM2 hagM2 hM1G hM2G hM12 hmk


open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__three_extensions

noncomputable def Tr (G : SimpleGraph (Fin n)) (u v : Fin n)
    (α : G.induce ({u}ᶜ : Set (Fin n)) ≃g G.induce ({v}ᶜ : Set (Fin n)))
    (X : SimpleGraph (Fin n)) : SimpleGraph (Fin n) :=
  reattach G v (fun y => ∃ hy : y ≠ v, X.Adj u (α.symm ⟨y, hy⟩).1)

lemma Tr_ag (G : SimpleGraph (Fin n)) (u v : Fin n)
    (α : G.induce ({u}ᶜ : Set (Fin n)) ≃g G.induce ({v}ᶜ : Set (Fin n)))
    (X : SimpleGraph (Fin n)) : AG G (Tr G u v α X) v :=
  fun x y hx hy => reattach_off G v _ x y hx hy

lemma Tr_adj (G : SimpleGraph (Fin n)) (u v : Fin n)
    (α : G.induce ({u}ᶜ : Set (Fin n)) ≃g G.induce ({v}ᶜ : Set (Fin n)))
    (X : SimpleGraph (Fin n)) (y : Fin n) (hy : y ≠ u) :
    (Tr G u v α X).Adj v (α ⟨y, hy⟩).1 ↔ X.Adj u y := by
  have hne : (α ⟨y, hy⟩).1 ≠ v := (α ⟨y, hy⟩).2
  rw [Tr, reattach_at G v _ _ hne]
  have he : α.symm ⟨(α ⟨y, hy⟩).1, hne⟩ = ⟨y, hy⟩ := α.symm_apply_apply _
  constructor
  · rintro ⟨_, h⟩
    rw [he] at h
    exact h
  · intro h
    exact ⟨hne, by rw [he]; exact h⟩

lemma Tr_hyp (G : SimpleGraph (Fin n)) (u v : Fin n)
    (α : G.induce ({u}ᶜ : Set (Fin n)) ≃g G.induce ({v}ᶜ : Set (Fin n)))
    (X : SimpleGraph (Fin n)) (hX : Recon.Hypomorphic G X) (hag : AG G X u) :
    Recon.Hypomorphic G (Tr G u v α X) := by
  obtain ⟨i⟩ : Nonempty (Tr G u v α X ≃g X) := by
    refine extend_iso (Tr G u v α X) X v u
      ((agreeIso (Tr G u v α X) G v (fun a b ha hb => (Tr_ag G u v α X a b ha hb).symm)).trans
        (α.symm.trans (agreeIso G X u hag))) ?_
    intro w hw
    refine (reattach_at G v _ w hw).trans ?_
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨hw, h⟩
  exact Recon.Checked.L_found_hypomorphic_iso_invariant n G G X (Tr G u v α X)
    ⟨SimpleGraph.Iso.refl⟩ ⟨i.symm⟩ hX

lemma Tr_inj (G : SimpleGraph (Fin n)) (u v : Fin n)
    (α : G.induce ({u}ᶜ : Set (Fin n)) ≃g G.induce ({v}ᶜ : Set (Fin n)))
    {X Y : SimpleGraph (Fin n)} (hX : AG G X u) (hY : AG G Y u)
    (he : Tr G u v α X = Tr G u v α Y) : X = Y := by
  apply eq_of_ag (ag_trans (ag_symm hX) hY)
  intro y
  by_cases hy : y = u
  · subst hy; simp
  · rw [← Tr_adj G u v α X y hy, ← Tr_adj G u v α Y y hy, he]

lemma conv_z (A B : SimpleGraph (Fin n)) (u y : Fin n) :
    ((Set.indicator {w : Fin n | A.Adj u w} 1 y : ℤ) - Set.indicator {w : Fin n | B.Adj u w} 1 y)
      = zf A B u y := by
  simp [Set.indicator_apply, zf]

lemma conv_fun (A B : SimpleGraph (Fin n)) (u : Fin n) :
    (fun y => (Set.indicator {w : Fin n | A.Adj u w} 1 y : ℤ) -
      Set.indicator {w : Fin n | B.Adj u w} 1 y) = zf A B u :=
  funext (conv_z A B u)

lemma conv_sum (K : SimpleGraph (Fin n)) (x : Fin n) (g : Fin n → ℤ) :
    ∑ y, Set.indicator {w : Fin n | K.Adj x w} g y = Az K g x := by
  unfold Az
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp [Set.indicator_apply]

lemma kk_ncard (A B : SimpleGraph (Fin n)) (u : Fin n) :
    kk A B u = ((Set.ncard {y | A.Adj u y ∧ ¬ B.Adj u y} : ℕ) : ℤ) := by
  rw [ncard_sum]
  rfl

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__low_extension_pair

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__low_extension_pair : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__low_extension_pair := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__low_extension_pair in
  intro n _hn d G H _hdeg hNF _hGH _hni hS u hu K₁ K₂ K₃ h1 h2 h3 ha1 ha2 ha3
  dsimp only at hS
  obtain ⟨hSa, hSb, θ, hSc, hSd⟩ := hS
  have h : Ctx n d G θ := by
    refine ⟨hSa, hSb, ?_, ?_⟩
    · intro A B hA hB v hag x
      obtain ⟨e1, e2⟩ := hSc A B hA hB v hag x
      refine ⟨?_, ?_⟩
      · rw [← conv_z]; exact e1
      · intro hx
        have e := e2 hx
        rw [conv_sum, conv_fun, conv_z] at e
        exact e
    · intro K A B hK hA hB v hagA hagB hAK hBK
      obtain ⟨e1, e2⟩ := hSd K A B hK hA hB v hagA hagB hAK hBK
      refine ⟨?_, e2⟩
      rw [kk_ncard, kk_ncard, e1]
  by_contra hcon
  push Not at hcon
  obtain ⟨n12, n13, n23⟩ := hcon
  have hP : ∀ v, dg G v = d → ∃ A B : SimpleGraph (Fin n), Recon.Hypomorphic G A ∧ AG G A v ∧
      Recon.Hypomorphic G B ∧ AG G B v ∧ A ≠ G ∧ B ≠ G ∧ A ≠ B := by
    intro v hv
    obtain ⟨α⟩ := hNF u v (by unfold dg at hv; omega)
    have t12 : Tr G u v α K₁ ≠ Tr G u v α K₂ := fun e => n12 (Tr_inj G u v α ha1 ha2 e)
    have t13 : Tr G u v α K₁ ≠ Tr G u v α K₃ := fun e => n13 (Tr_inj G u v α ha1 ha3 e)
    have t23 : Tr G u v α K₂ ≠ Tr G u v α K₃ := fun e => n23 (Tr_inj G u v α ha2 ha3 e)
    have y1 := Tr_hyp G u v α K₁ h1 ha1
    have y2 := Tr_hyp G u v α K₂ h2 ha2
    have y3 := Tr_hyp G u v α K₃ h3 ha3
    have g1 := Tr_ag G u v α K₁
    have g2 := Tr_ag G u v α K₂
    have g3 := Tr_ag G u v α K₃
    by_cases e1 : Tr G u v α K₁ = G
    · exact ⟨_, _, y2, g2, y3, g3, fun e => t12 (e1.trans e.symm),
        fun e => t13 (e1.trans e.symm), t23⟩
    · by_cases e2 : Tr G u v α K₂ = G
      · exact ⟨_, _, y1, g1, y3, g3, e1, fun e => t23 (e2.trans e.symm), t13⟩
      · exact ⟨_, _, y1, g1, y2, g2, e1, e2, t12⟩
  obtain ⟨A, B, hA, hagA, hB, hagB, hAG, hBG, hAB⟩ := hP u hu
  exact core h hP (kk G A u).toNat u hu A B hA hagA hB hagB hAG hBG hAB (Int.self_le_toNat _)
