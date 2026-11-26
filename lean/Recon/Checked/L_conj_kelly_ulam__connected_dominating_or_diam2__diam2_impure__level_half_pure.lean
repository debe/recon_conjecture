import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure

open SimpleGraph
open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class

lemma forced_key {n : ℕ} (G H : SimpleGraph (Fin n)) (σ : Fin n ≃ Fin n)
    (f : ∀ x, G.induce ({x}ᶜ : Set (Fin n)) ≃g H.induce ({σ x}ᶜ : Set (Fin n)))
    (hE : G.edgeSet.ncard = H.edgeSet.ncard)
    (hdeg : ∀ x, (G.neighborSet x).ncard = (H.neighborSet (σ x)).ncard)
    (u y : Fin n) (hy : y ≠ u)
    (hforced : ∀ x' y' : Fin n, (G.neighborSet x').ncard = (G.neighborSet u).ncard → x' ≠ y' →
      Nonempty (G.induce ({u, y}ᶜ : Set (Fin n)) ≃g G.induce ({x', y'}ᶜ : Set (Fin n))) →
      (G.Adj u y ↔ G.Adj x' y')) :
    G.Adj u y ↔ H.Adj (σ u) (f u ⟨y, hy⟩).1 := by
  classical
  have hb := bit_law G u y hy
  have hcE : (G.induce ({u, y}ᶜ : Set (Fin n))).edgeSet.ncard ≤ G.edgeSet.ncard := by
    by_cases h : G.Adj u y
    · rw [ite_eq_left h] at hb
      have : 0 < (G.neighborSet u).ncard := (Set.ncard_pos).mpr ⟨y, h⟩
      omega
    · rw [ite_eq_right h] at hb
      omega
  obtain ⟨s, hs⟩ : ∃ s, G.edgeSet.ncard = s + (G.induce ({u, y}ᶜ : Set (Fin n))).edgeSet.ncard :=
    ⟨_, (Nat.sub_add_cancel hcE).symm⟩
  have hsH : H.edgeSet.ncard = s + (G.induce ({u, y}ᶜ : Set (Fin n))).edgeSet.ncard := by
    rw [← hE]; exact hs
  obtain ⟨heG, hmG, hm0G⟩ := sym_facts G (G.induce ({u, y}ᶜ : Set (Fin n))) s
    (fun x z hne hiso => (hbit G _ s hs x z hne hiso).1)
    (fun x z hne hiso => (hbit G _ s hs x z hne hiso).2)
  obtain ⟨heH, hmH, hm0H⟩ := sym_facts H (G.induce ({u, y}ᶜ : Set (Fin n))) s
    (fun x z hne hiso => (hbit H _ s hsH x z hne hiso).1)
    (fun x z hne hiso => (hbit H _ s hsH x z hne hiso).2)
  have hEq := arith s _ _ _ _ _ _ (pi_eq G H σ f hdeg (G.induce ({u, y}ᶜ : Set (Fin n))))
    (p_eq_e_add_m G _) (p_eq_e_add_m H _) heG heH hmG hmH hm0G hm0H
  have hP := pi_eq G H σ f hdeg (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard
  have hPG := p_eq_e_add_m G (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard
  have hPH := p_eq_e_add_m H (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard
  have hE' := hEq (G.neighborSet u).ncard
  have hmem : (σ u, (f u ⟨y, hy⟩).1) ∈
      Pset H (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard :=
    ⟨fun h => (f u ⟨y, hy⟩).2 h.symm, ⟨(restrictIso (f u) y hy).symm⟩, (hdeg u).symm⟩
  by_cases hadj : G.Adj u y
  · have hM0 : (Mset G (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard).ncard = 0 := by
      rw [Set.ncard_eq_zero]
      apply Set.eq_empty_of_forall_notMem
      rintro ⟨x, z⟩ ⟨⟨hne, ⟨hiso⟩, hd⟩, hnadj⟩
      exact hnadj ((hforced x z hd hne ⟨hiso.symm⟩).1 hadj)
    have hMH : (Mset H (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard).ncard = 0 := by
      omega
    refine ⟨fun _ => ?_, fun _ => hadj⟩
    by_contra hn
    rw [Set.ncard_eq_zero] at hMH
    have : (σ u, (f u ⟨y, hy⟩).1) ∈
        Mset H (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard := ⟨hmem, hn⟩
    rw [hMH] at this
    exact this
  · have hE0 : (Eset G (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard).ncard = 0 := by
      rw [Set.ncard_eq_zero]
      apply Set.eq_empty_of_forall_notMem
      rintro ⟨x, z⟩ ⟨⟨hne, ⟨hiso⟩, hd⟩, hxz⟩
      exact hadj ((hforced x z hd hne ⟨hiso.symm⟩).2 hxz)
    have hEH : (Eset H (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard).ncard = 0 := by
      omega
    refine ⟨fun h => (hadj h).elim, fun h => ?_⟩
    rw [Set.ncard_eq_zero] at hEH
    have : (σ u, (f u ⟨y, hy⟩).1) ∈
        Eset H (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard := ⟨hmem, h⟩
    rw [hEH] at this
    exact this.elim

lemma split_count {α : Type*} [Fintype α] (J : α → ℕ) (R : α → Prop) [DecidablePred R]
    (k : ℕ) :
    (Finset.univ.filter (fun a => J a + (if R a then 1 else 0) = k)).card +
      (Finset.univ.filter (fun a => J a = k ∧ R a)).card =
    (Finset.univ.filter (fun a => J a = k)).card +
      (Finset.univ.filter (fun a => J a + 1 = k ∧ R a)).card := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun a => J a + (if R a then 1 else 0) = k)) R
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun a => J a = k)) R
  rw [Finset.filter_filter, Finset.filter_filter] at h1 h2
  have e1 : Finset.univ.filter (fun a => J a + (if R a then 1 else 0) = k ∧ R a) =
      Finset.univ.filter (fun a => J a + 1 = k ∧ R a) :=
    Finset.filter_congr (fun a _ => by by_cases h : R a <;> simp [h])
  have e2 : Finset.univ.filter (fun a => J a + (if R a then 1 else 0) = k ∧ ¬ R a) =
      Finset.univ.filter (fun a => J a = k ∧ ¬ R a) :=
    Finset.filter_congr (fun a _ => by by_cases h : R a <;> simp [h])
  rw [e1, e2] at h1
  omega

lemma level_bal {α : Type*} [Fintype α] (J : α → ℕ) (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q]
    (h : ∀ k, (Finset.univ.filter (fun a => J a + (if P a then 1 else 0) = k)).card =
      (Finset.univ.filter (fun a => J a + (if Q a then 1 else 0) = k)).card) :
    ∀ k, (Finset.univ.filter (fun a => J a = k ∧ P a)).card =
      (Finset.univ.filter (fun a => J a = k ∧ Q a)).card := by
  have step : ∀ k, (Finset.univ.filter (fun a => J a + 1 = k ∧ P a)).card =
      (Finset.univ.filter (fun a => J a + 1 = k ∧ Q a)).card →
      (Finset.univ.filter (fun a => J a = k ∧ P a)).card =
      (Finset.univ.filter (fun a => J a = k ∧ Q a)).card := by
    intro k hk
    have := split_count J P k
    have := split_count J Q k
    have := h k
    omega
  have shift : ∀ (R : α → Prop) [DecidablePred R] (k : ℕ),
      Finset.univ.filter (fun a => J a + 1 = k + 1 ∧ R a) =
        Finset.univ.filter (fun a => J a = k ∧ R a) := fun R _ k =>
    Finset.filter_congr (fun a _ => by
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩)
  intro k
  induction k with
  | zero =>
    apply step
    have e : ∀ (R : α → Prop) [DecidablePred R],
        Finset.univ.filter (fun a => J a + 1 = 0 ∧ R a) = ∅ := fun R _ =>
      Finset.filter_eq_empty_iff.2 (fun a _ h => by omega)
    rw [e P, e Q]
  | succ k ih =>
    apply step
    rw [shift P k, shift Q k]
    exact ih

lemma card_comp {α : Type*} [Fintype α] (g : α ≃ α) (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x => P (g x))).card = (Finset.univ.filter P).card := by
  refine Finset.card_bij (fun a _ => g a) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a _ b _ h
    exact g.injective h
  · intro b hb
    refine ⟨g.symm b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    simpa using hb

lemma ncard_nbr_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (v : V) :
    (G.neighborSet v).ncard = (H.neighborSet (e v)).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (e.mapNeighborSet v)

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class in
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure in
  intro n hn G ⟨u, hu⟩ H ⟨σ, hσ⟩
  classical
  have hE := Recon.Checked.L_kelly_edge_count n hn G H ⟨σ, hσ⟩
  let f : ∀ x, G.induce ({x}ᶜ : Set (Fin n)) ≃g H.induce ({σ x}ᶜ : Set (Fin n)) :=
    fun x => (hσ x).some
  have hdeg : ∀ x, (G.neighborSet x).ncard = (H.neighborSet (σ x)).ncard := fun x => by
    have h1 := card_add_deg G x
    have h2 := card_add_deg H (σ x)
    have h3 := ncard_iso (f x)
    omega
  let φ : Fin n → Fin n := fun x => if h : x = u then σ u else (f u ⟨x, h⟩).1
  have hφu : φ u = σ u := dite_eq_left rfl
  have hφ : ∀ x (h : x ≠ u), φ x = (f u ⟨x, h⟩).1 := fun x h => dite_eq_right h
  have hφinj : Function.Injective φ := by
    intro a b hab
    by_cases ha : a = u
    · by_cases hb : b = u
      · rw [ha, hb]
      · rw [ha, hφu, hφ b hb] at hab
        exact ((f u ⟨b, hb⟩).2 hab.symm).elim
    · by_cases hb : b = u
      · rw [hb, hφu, hφ a ha] at hab
        exact ((f u ⟨a, ha⟩).2 hab).elim
      · rw [hφ a ha, hφ b hb] at hab
        exact congrArg Subtype.val ((f u).injective (Subtype.ext hab))
  let φe : Fin n ≃ Fin n := Equiv.ofBijective φ (Finite.injective_iff_bijective.mp hφinj)
  let J : Fin n → ℕ := fun x => (G.neighborSet x).ncard - (if G.Adj u x then 1 else 0)
  have hJG : ∀ x, (G.neighborSet x).ncard = J x + (if G.Adj u x then 1 else 0) := by
    intro x
    by_cases h : G.Adj u x
    · have : 0 < (G.neighborSet x).ncard := (Set.ncard_pos).mpr ⟨u, h.symm⟩
      simp only [J, h, ite_true]
      omega
    · simp only [J, h, ite_false]
      omega
  have hJH : ∀ x, (H.neighborSet (φ x)).ncard =
      J x + (if H.Adj (σ u) (φ x) then 1 else 0) := by
    intro x
    by_cases hx : x = u
    · subst hx
      rw [hφu, ← hdeg x]
      simp [J]
    · have h1 := deg_in_card G u x hx
      have hne : φ x ≠ σ u := by rw [hφ x hx]; exact (f u ⟨x, hx⟩).2
      have h2 := deg_in_card H (σ u) (φ x) hne
      have h3 := ncard_nbr_iso (f u) ⟨x, hx⟩
      have h4 : (⟨φ x, hne⟩ : ({σ u}ᶜ : Set (Fin n))) = f u ⟨x, hx⟩ := Subtype.ext (hφ x hx)
      rw [h4] at h2
      have := hJG x
      omega
  have hcount : ∀ k, (Finset.univ.filter
      (fun x => J x + (if G.Adj u x then 1 else 0) = k)).card =
      (Finset.univ.filter (fun x => J x + (if H.Adj (σ u) (φ x) then 1 else 0) = k)).card := by
    intro k
    have e1 : Finset.univ.filter (fun x => J x + (if G.Adj u x then 1 else 0) = k) =
        Finset.univ.filter (fun x => (H.neighborSet (σ x)).ncard = k) :=
      Finset.filter_congr (fun x _ => by rw [← hJG x, hdeg x])
    have e2 : Finset.univ.filter (fun x => J x + (if H.Adj (σ u) (φ x) then 1 else 0) = k) =
        Finset.univ.filter (fun x => (H.neighborSet (φe x)).ncard = k) :=
      Finset.filter_congr (fun x _ => by rw [← hJH x]; rfl)
    rw [e1, e2, card_comp σ (fun w => (H.neighborSet w).ncard = k),
      card_comp φe (fun w => (H.neighborSet w).ncard = k)]
  have hlev := level_bal J _ _ hcount
  have key : ∀ y (hy : y ≠ u), G.Adj u y ↔ H.Adj (σ u) (f u ⟨y, hy⟩).1 := by
    intro y hy
    rw [← hφ y hy]
    have hl := hlev (J y)
    rcases hu (J y) with hA | hB
    · have hsub : Finset.univ.filter (fun x => J x = J y ∧ G.Adj u x) ⊆
          Finset.univ.filter (fun x => J x = J y ∧ H.Adj (σ u) (φ x)) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨h1, h2⟩ := hx
        refine ⟨h1, ?_⟩
        have hxu : x ≠ u := fun h => G.loopless.irrefl u (h ▸ h2)
        have hdx : (G.neighborSet x).ncard = J y + 1 := by
          have := hJG x; simp only [h2, ite_true] at this; omega
        rw [hφ x hxu]
        exact (forced_key G H σ f hE hdeg u x hxu (fun x' y' hd hne hiso =>
          ⟨fun _ => hA x h2 hdx x' y' hd hne hiso, fun _ => h2⟩)).1 h2
      have heq := Finset.eq_of_subset_of_card_le hsub hl.ge
      constructor
      · intro h
        have hm : y ∈ Finset.univ.filter (fun x => J x = J y ∧ G.Adj u x) := by simp [h]
        rw [heq] at hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
        exact hm
      · intro h
        have hm : y ∈ Finset.univ.filter (fun x => J x = J y ∧ H.Adj (σ u) (φ x)) := by simp [h]
        rw [← heq] at hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
        exact hm
    · have hsub : Finset.univ.filter (fun x => J x = J y ∧ H.Adj (σ u) (φ x)) ⊆
          Finset.univ.filter (fun x => J x = J y ∧ G.Adj u x) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨h1, h2⟩ := hx
        refine ⟨h1, ?_⟩
        have hxu : x ≠ u := by
          intro h
          rw [h, hφu] at h2
          exact H.loopless.irrefl _ h2
        by_contra h3
        have hdx : (G.neighborSet x).ncard = J y := by
          have := hJG x; simp only [h3, ite_false] at this; omega
        rw [hφ x hxu] at h2
        exact h3 ((forced_key G H σ f hE hdeg u x hxu (fun x' y' hd hne hiso =>
          ⟨fun h => (h3 h).elim, fun h => (hB x hxu h3 hdx x' y' hd hne hiso h).elim⟩)).2 h2)
      have heq := Finset.eq_of_subset_of_card_le hsub hl.le
      constructor
      · intro h
        have hm : y ∈ Finset.univ.filter (fun x => J x = J y ∧ G.Adj u x) := by simp [h]
        rw [← heq] at hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
        exact hm
      · intro h
        have hm : y ∈ Finset.univ.filter (fun x => J x = J y ∧ H.Adj (σ u) (φ x)) := by simp [h]
        rw [heq] at hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
        exact hm
  exact iso_of_nbhd (f u) key
