import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__three_extensions
import Recon.Checked.L_found_hypomorphic_iso_invariant

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__three_extensions

/-- Re-attach vertex `c` of `G` along the predicate `P`. -/
def reattach {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n) (P : Fin n → Prop) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b => (a ≠ c ∧ b ≠ c ∧ G.Adj a b) ∨ (a = c ∧ P b))

lemma reattach_off {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n) (P : Fin n → Prop)
    (x y : Fin n) (hx : x ≠ c) (hy : y ≠ c) : G.Adj x y ↔ (reattach G c P).Adj x y := by
  simp only [reattach, SimpleGraph.fromRel_adj]
  constructor
  · intro h
    exact ⟨G.ne_of_adj h, Or.inl (Or.inl ⟨hx, hy, h⟩)⟩
  · rintro ⟨_, h | h⟩
    · rcases h with h | h
      · exact h.2.2
      · exact absurd h.1 hx
    · rcases h with h | h
      · exact h.2.2.symm
      · exact absurd h.1 hy

lemma reattach_at {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n) (P : Fin n → Prop)
    (y : Fin n) (hy : y ≠ c) : (reattach G c P).Adj c y ↔ P y := by
  simp only [reattach, SimpleGraph.fromRel_adj]
  have hc : c ≠ y := hy.symm
  tauto

/-- Graphs agreeing off `c` have identical cards at `c`. -/
def agreeIso {n : ℕ} (A B : SimpleGraph (Fin n)) (c : Fin n)
    (h : ∀ x y : Fin n, x ≠ c → y ≠ c → (A.Adj x y ↔ B.Adj x y)) :
    A.induce ({c}ᶜ : Set (Fin n)) ≃g B.induce ({c}ᶜ : Set (Fin n)) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro x y
    simp only [Equiv.refl_apply, SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
    exact (h x.1 y.1 x.2 y.2).symm

/-- Extend a card isomorphism to a graph isomorphism. -/
lemma extend_iso {n : ℕ} (A B : SimpleGraph (Fin n)) (a b : Fin n)
    (β : A.induce ({a}ᶜ : Set (Fin n)) ≃g B.induce ({b}ᶜ : Set (Fin n)))
    (hβ : ∀ v (hv : v ≠ a), A.Adj a v ↔ B.Adj b (β ⟨v, hv⟩).1) : Nonempty (A ≃g B) := by
  classical
  let e : Fin n → Fin n := fun v => if h : v = a then b else (β ⟨v, h⟩).1
  let f : Fin n → Fin n := fun w => if h : w = b then a else (β.symm ⟨w, h⟩).1
  have hβne : ∀ v (hv : v ≠ a), (β ⟨v, hv⟩).1 ≠ b := fun v hv => (β ⟨v, hv⟩).2
  have hβsne : ∀ w (hw : w ≠ b), (β.symm ⟨w, hw⟩).1 ≠ a := fun w hw => (β.symm ⟨w, hw⟩).2
  have hfe : ∀ v, f (e v) = v := by
    intro v
    by_cases hv : v = a
    · simp [e, f, hv]
    · have h1 : e v = (β ⟨v, hv⟩).1 := dif_neg hv
      rw [h1]
      show (if h : _ = b then a else _) = v
      rw [dif_neg (hβne v hv)]
      exact congrArg Subtype.val (β.symm_apply_apply _)
  have hef : ∀ w, e (f w) = w := by
    intro w
    by_cases hw : w = b
    · simp [e, f, hw]
    · have h1 : f w = (β.symm ⟨w, hw⟩).1 := dif_neg hw
      rw [h1]
      show (if h : _ = a then b else _) = w
      rw [dif_neg (hβsne w hw)]
      exact congrArg Subtype.val (β.apply_symm_apply _)
  refine ⟨{ toEquiv := ⟨e, f, hfe, hef⟩, map_rel_iff' := ?_ }⟩
  intro v w
  simp only [Equiv.coe_fn_mk]
  by_cases hv : v = a <;> by_cases hw : w = a
  · subst hv; subst hw
    simp [e]
  · subst hv
    simp only [e, dif_pos, dif_neg hw]
    exact (hβ w hw).symm
  · subst hw
    simp only [e, dif_pos, dif_neg hv]
    rw [B.adj_comm, A.adj_comm]
    exact (hβ v hv).symm
  · simp only [e, dif_neg hv, dif_neg hw]
    have := β.map_rel_iff (a := ⟨v, hv⟩) (b := ⟨w, hw⟩)
    simpa using this

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__three_extensions

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__three_extensions : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__three_extensions := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__three_extensions in
  intro n _hn G H u u' α x hux hnx hGH hni
  obtain ⟨σ, hσ⟩ := hGH
  obtain ⟨γ⟩ := hσ u'
  let P2 : Fin n → Prop := fun y => ∃ hy : y ≠ u', G.Adj u (α.symm ⟨y, hy⟩).1
  let P3 : Fin n → Prop := fun y => ∃ hy : y ≠ u', H.Adj (σ u') (γ ⟨y, hy⟩).1
  let K2 := reattach G u' P2
  let K3 := reattach G u' P3
  have ag2 := reattach_off G u' P2
  have ag3 := reattach_off G u' P3
  have iso2 : Nonempty (K2 ≃g G) := by
    refine extend_iso K2 G u' u
      ((agreeIso K2 G u' (fun a b ha hb => (ag2 a b ha hb).symm)).trans α.symm) ?_
    intro v hv
    rw [reattach_at G u' P2 v hv]
    simp only [P2]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨hv, h⟩
  have iso3 : Nonempty (K3 ≃g H) := by
    refine extend_iso K3 H u' (σ u')
      ((agreeIso K3 G u' (fun a b ha hb => (ag3 a b ha hb).symm)).trans γ) ?_
    intro v hv
    rw [reattach_at G u' P3 v hv]
    simp only [P3]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨hv, h⟩
  have hGH' : Recon.Hypomorphic G H := ⟨σ, hσ⟩
  obtain ⟨i2⟩ := iso2
  obtain ⟨i3⟩ := iso3
  refine ⟨G, K2, K3, Recon.anchor_hypomorphic_refl G, ?_, ?_, fun _ _ _ _ => Iff.rfl,
    ag2, ag3, ?_, ?_, ?_⟩
  · exact Recon.Checked.L_found_hypomorphic_iso_invariant n G G G K2 ⟨SimpleGraph.Iso.refl⟩
      ⟨i2.symm⟩ (Recon.anchor_hypomorphic_refl G)
  · exact Recon.Checked.L_found_hypomorphic_iso_invariant n G G H K3 ⟨SimpleGraph.Iso.refl⟩
      ⟨i3.symm⟩ hGH'
  · intro h
    have hx' : (α x).1 ≠ u' := (α x).2
    have : K2.Adj u' (α x).1 := by
      rw [reattach_at G u' P2 _ hx']
      have he : α.symm ⟨(α x).1, hx'⟩ = x := by
        exact α.symm_apply_apply x
      exact ⟨hx', by rw [he]; exact hux⟩
    rw [← h] at this
    exact hnx this
  · intro h
    exact hni ⟨h ▸ i3⟩
  · intro h
    exact hni ⟨i2.symm.trans (h ▸ i3)⟩
