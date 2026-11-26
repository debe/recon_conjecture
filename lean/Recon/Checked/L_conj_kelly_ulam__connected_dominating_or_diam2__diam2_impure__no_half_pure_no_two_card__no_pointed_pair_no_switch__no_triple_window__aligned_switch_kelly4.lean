import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__aligned_switch_kelly4
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class
import Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__aligned_switch_kelly4

open SimpleGraph

lemma deg_le {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) : (G.neighborSet x).ncard ≤ n := by
  have h := Set.ncard_le_ncard (Set.subset_univ (G.neighborSet x))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

lemma ncard_eq_filter {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    {y : Fin n | P y}.ncard = (Finset.univ.filter P).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- one half of Lemma Sw -/
lemma half {n : ℕ} {G K : SimpleGraph (Fin n)}
    (hdeg : ∀ x, (K.neighborSet x).ncard = (G.neighborSet x).ncard)
    (w y : Fin n) (e : G.induce ({w}ᶜ : Set (Fin n)) ≃g K.induce ({w}ᶜ : Set (Fin n))) (hy : y ≠ w)
    (hD : (G.Adj w y ∧ ¬ K.Adj w y) ∨ (K.Adj w y ∧ ¬ G.Adj w y)) :
    ∃ y₁ : Fin n, y₁ ≠ w ∧ y₁ ≠ y ∧
      (G.Adj w y → (G.Adj w y₁ → (G.neighborSet y₁).ncard = (G.neighborSet y).ncard + 1) ∧
        (¬ G.Adj w y₁ → (G.neighborSet y₁).ncard = (G.neighborSet y).ncard)) ∧
      (¬ G.Adj w y → (G.Adj w y₁ → (G.neighborSet y₁).ncard = (G.neighborSet y).ncard) ∧
        (¬ G.Adj w y₁ → (G.neighborSet y₁).ncard + 1 = (G.neighborSet y).ncard)) ∧
      Nonempty (G.induce ({w, y₁}ᶜ : Set (Fin n)) ≃g K.induce ({w, y}ᶜ : Set (Fin n))) := by
  classical
  set z := e.symm ⟨y, hy⟩ with hz
  have hez : e z = ⟨y, hy⟩ := by rw [hz]; exact e.apply_symm_apply _
  have hz' : (⟨z.1, z.2⟩ : ({w}ᶜ : Set (Fin n))) = z := rfl
  have h1 := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class.deg_in_card G w z.1 z.2
  have h2 := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class.deg_in_card K w y hy
  have h3 := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure.ncard_nbr_iso e z
  rw [hez] at h3
  rw [hz'] at h1
  have h4 := hdeg y
  have hzy : z.1 ≠ y := by
    intro hc
    have q1 : (G.Adj w z.1 ↔ G.Adj w y) := by rw [hc]
    have q2 : (G.neighborSet z.1).ncard = (G.neighborSet y).ncard := by rw [hc]
    rcases hD with ⟨a, b⟩ | ⟨a, b⟩
    · have a' := q1.2 a
      simp only [a', b, ite_true, ite_false] at h1 h2; omega
    · have a' : ¬ G.Adj w z.1 := fun h => b (q1.1 h)
      simp only [a, a', ite_true, ite_false] at h1 h2; omega
  refine ⟨z.1, z.2, hzy, ?_, ?_, ?_⟩
  · intro hwy
    have hk : ¬ K.Adj w y := by tauto
    simp only [hk, ite_false] at h2
    constructor
    · intro hh; simp only [hh, ite_true] at h1; omega
    · intro hh; simp only [hh, ite_false] at h1; omega
  · intro hwy
    have hk : K.Adj w y := by tauto
    simp only [hk, ite_true] at h2
    constructor
    · intro hh; simp only [hh, ite_true] at h1; omega
    · intro hh; simp only [hh, ite_false] at h1; omega
  · have r := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class.restrictIso e z.1 z.2
    rw [hz', hez] at r
    exact ⟨r⟩

lemma nbr_bal {n : ℕ} {G K : SimpleGraph (Fin n)}
    (hdeg : ∀ x, (K.neighborSet x).ncard = (G.neighborSet x).ncard)
    (v : Fin n) (e : G.induce ({v}ᶜ : Set (Fin n)) ≃g K.induce ({v}ᶜ : Set (Fin n))) (k : ℕ) :
    {y : Fin n | G.Adj v y ∧ (G.neighborSet y).ncard = k}.ncard =
      {y : Fin n | K.Adj v y ∧ (G.neighborSet y).ncard = k}.ncard := by
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin n ≃ Fin n, φ = Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.extE e := ⟨_, rfl⟩
  let J : Fin n → ℕ := fun x => n - (G.neighborSet x).ncard
  have hpt : ∀ x, J x + (if G.Adj v x then 1 else 0) =
      J (φ x) + (if K.Adj v (φ x) then 1 else 0) := by
    intro x
    by_cases hx : x = v
    · subst hx
      have : φ x = x := hφ ▸ Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.extE_a e
      rw [this]
      simp
    · have h1 := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__pointed_pair_symmetric.deg_extE e x hx
      rw [← hφ] at h1
      have h2 := hdeg (φ x)
      have h3 := deg_le G x
      have h4 := deg_le G (φ x)
      simp only [J]
      have hd1 : (if G.Adj v x then 1 else 0) ≤ (G.neighborSet x).ncard := by
        split_ifs with hh
        · exact (Set.ncard_pos).mpr ⟨v, hh.symm⟩
        · exact Nat.zero_le _
      have hd2 : (if K.Adj v (φ x) then 1 else 0) ≤ (G.neighborSet (φ x)).ncard := by
        split_ifs with hh
        · rw [← h2]; exact (Set.ncard_pos).mpr ⟨v, hh.symm⟩
        · exact Nat.zero_le _
      split_ifs at h1 hd1 hd2 ⊢ <;> omega
  have hcount : ∀ k, (Finset.univ.filter (fun x => J x + (if G.Adj v x then 1 else 0) = k)).card =
      (Finset.univ.filter (fun x => J x + (if K.Adj v x then 1 else 0) = k)).card := by
    intro k
    rw [← Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure.card_comp φ (fun a => J a + (if K.Adj v a then 1 else 0) = k)]
    congr 1
    exact Finset.filter_congr (fun x _ => by rw [hpt x])
  have hlev := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure.level_bal J _ _ hcount
  rw [ncard_eq_filter, ncard_eq_filter]
  by_cases hk : k ≤ n
  · have e1 : Finset.univ.filter (fun y => G.Adj v y ∧ (G.neighborSet y).ncard = k) =
        Finset.univ.filter (fun y => J y = n - k ∧ G.Adj v y) :=
      Finset.filter_congr (fun y _ => by have := deg_le G y; simp only [J]; constructor <;> (rintro ⟨a, b⟩; exact ⟨by omega, by omega⟩) )
    have e2 : Finset.univ.filter (fun y => K.Adj v y ∧ (G.neighborSet y).ncard = k) =
        Finset.univ.filter (fun y => J y = n - k ∧ K.Adj v y) :=
      Finset.filter_congr (fun y _ => by have := deg_le G y; simp only [J]; constructor <;> (rintro ⟨a, b⟩; exact ⟨by omega, by omega⟩) )
    rw [e1, e2]
    exact hlev (n - k)
  · have e : ∀ (R : Fin n → Prop) [DecidablePred R],
        Finset.univ.filter (fun y => R y ∧ (G.neighborSet y).ncard = k) = ∅ := fun R _ =>
      Finset.filter_eq_empty_iff.2 (fun y _ h => by have := deg_le G y; omega)
    rw [e, e]

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__aligned_switch_kelly4

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__aligned_switch_kelly4 : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__aligned_switch_kelly4 := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__aligned_switch_kelly4 in
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
  have hcancel : symmDiff G (symmDiff G K) = K := symmDiff_symmDiff_cancel_left G K
  have hDadj : ∀ a b, (symmDiff G K).Adj a b ↔ (G.Adj a b ∧ ¬ K.Adj a b) ∨ (K.Adj a b ∧ ¬ G.Adj a b) := by
    intro a b
    simp only [symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
  have hsw : ∀ w y : Fin n, (symmDiff G K).Adj w y → (∃ y₁ w₁ : Fin n, y₁ ≠ w ∧ y₁ ≠ y ∧ w₁ ≠ w ∧ w₁ ≠ y ∧ (G.Adj w y → (G.Adj w y₁ → (G.neighborSet y₁).ncard = (G.neighborSet y).ncard + 1) ∧ (¬ G.Adj w y₁ → (G.neighborSet y₁).ncard = (G.neighborSet y).ncard) ∧ (G.Adj y w₁ → (G.neighborSet w₁).ncard = (G.neighborSet w).ncard + 1) ∧ (¬ G.Adj y w₁ → (G.neighborSet w₁).ncard = (G.neighborSet w).ncard)) ∧ (¬ G.Adj w y → (G.Adj w y₁ → (G.neighborSet y₁).ncard = (G.neighborSet y).ncard) ∧ (¬ G.Adj w y₁ → (G.neighborSet y₁).ncard + 1 = (G.neighborSet y).ncard) ∧ (G.Adj y w₁ → (G.neighborSet w₁).ncard = (G.neighborSet w).ncard) ∧ (¬ G.Adj y w₁ → (G.neighborSet w₁).ncard + 1 = (G.neighborSet w).ncard)) ∧ Nonempty (G.induce ({w, y₁}ᶜ : Set (Fin n)) ≃g G.induce ({y, w₁}ᶜ : Set (Fin n)))) := by
    intro w y hD
    have hwy : w ≠ y := (symmDiff G K).ne_of_adj hD
    have hD1 := (hDadj w y).1 hD
    have hD2 : (G.Adj y w ∧ ¬ K.Adj y w) ∨ (K.Adj y w ∧ ¬ G.Adj y w) := by
      rw [G.adj_comm, K.adj_comm]; exact hD1
    obtain ⟨y₁, a1, a2, a3, a4, a5⟩ := half hdeg w y (g w) hwy.symm hD1
    obtain ⟨w₁, b1, b2, b3, b4, b5⟩ := half hdeg y w (g y) hwy hD2
    refine ⟨y₁, w₁, a1, a2, b2, b1, ?_, ?_, ?_⟩
    · intro h
      have h' : G.Adj y w := h.symm
      exact ⟨(a3 h).1, (a3 h).2, (b3 h').1, (b3 h').2⟩
    · intro h
      have h' : ¬ G.Adj y w := fun hh => h hh.symm
      exact ⟨(a4 h).1, (a4 h).2, (b4 h').1, (b4 h').2⟩
    · obtain ⟨i1⟩ := a5
      obtain ⟨i2⟩ := b5
      rw [Set.pair_comm y w] at i2
      exact ⟨i1.trans i2.symm⟩
  have hbal : ∀ v : Fin n, ∀ k : ℕ, {y : Fin n | (symmDiff G K).Adj v y ∧ G.Adj v y ∧ (G.neighborSet y).ncard = k}.ncard = {y : Fin n | (symmDiff G K).Adj v y ∧ ¬ G.Adj v y ∧ (G.neighborSet y).ncard = k}.ncard := by
    intro v k
    have hb := nbr_bal hdeg v (g v) k
    have s1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard {y : Fin n | G.Adj v y ∧ (G.neighborSet y).ncard = k} {y : Fin n | K.Adj v y}
    have s2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard {y : Fin n | K.Adj v y ∧ (G.neighborSet y).ncard = k} {y : Fin n | G.Adj v y}
    have q1 : {y : Fin n | (symmDiff G K).Adj v y ∧ G.Adj v y ∧ (G.neighborSet y).ncard = k} =
        {y : Fin n | G.Adj v y ∧ (G.neighborSet y).ncard = k} \ {y : Fin n | K.Adj v y} := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_sdiff, hDadj]; tauto
    have q2 : {y : Fin n | (symmDiff G K).Adj v y ∧ ¬ G.Adj v y ∧ (G.neighborSet y).ncard = k} =
        {y : Fin n | K.Adj v y ∧ (G.neighborSet y).ncard = k} \ {y : Fin n | G.Adj v y} := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_sdiff, hDadj]; tauto
    have q3 : {y : Fin n | G.Adj v y ∧ (G.neighborSet y).ncard = k} ∩ {y : Fin n | K.Adj v y} =
        {y : Fin n | K.Adj v y ∧ (G.neighborSet y).ncard = k} ∩ {y : Fin n | G.Adj v y} := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
    rw [q1, q2]
    rw [q3] at s1
    omega
  have hkel : ∀ k : ℕ, k ≤ 4 → k < n → ∀ F : SimpleGraph (Fin k), {S : Finset (Fin n) | Nonempty ((symmDiff G (symmDiff G K)).induce (S : Set (Fin n)) ≃g F)}.ncard = {S : Finset (Fin n) | Nonempty (G.induce (S : Set (Fin n)) ≃g F)}.ncard := by
    intro k _ hkn F
    rw [hcancel]
    exact (Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count n G K hGK k hkn F).symm
  obtain ⟨φ⟩ := hP (symmDiff G K) hsw hbal hkel
  rw [hcancel] at φ
  exact ⟨φ.trans eKH⟩
