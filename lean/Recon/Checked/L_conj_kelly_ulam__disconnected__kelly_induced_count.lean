import Mathlib
import Recon.Statements.S_conj_kelly_ulam__disconnected__kelly_induced_count

namespace Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count

open SimpleGraph Classical

noncomputable def ind {W : Type*} [Fintype W] (A : SimpleGraph W) {k : ℕ}
    (F : SimpleGraph (Fin k)) : ℕ :=
  Finset.card (Finset.univ.filter (fun S : Finset W => Nonempty (A.induce (S : Set W) ≃g F)))

def isoInduce {W W' : Type*} {A : SimpleGraph W} {B : SimpleGraph W'} (e : A ≃g B)
    (s : Set W) (t : Set W') (h : ∀ x, x ∈ s ↔ e x ∈ t) : A.induce s ≃g B.induce t where
  toEquiv := e.toEquiv.subtypeEquiv h
  map_rel_iff' := by
    intro a b
    simp [e.map_rel_iff]

lemma ind_iso {W W' : Type*} [Fintype W] [Fintype W'] {A : SimpleGraph W} {B : SimpleGraph W'}
    (e : A ≃g B) {k : ℕ} (F : SimpleGraph (Fin k)) : ind A F = ind B F := by
  unfold ind
  refine Finset.card_equiv (e.toEquiv.finsetCongr) ?_
  intro S
  have h : ∀ x, x ∈ (S : Set W) ↔ e x ∈ ((e.toEquiv.finsetCongr S : Finset W') : Set W') := by
    intro x
    simp [Equiv.finsetCongr_apply]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f⟩
    exact ⟨(isoInduce e _ _ h).symm.trans f⟩
  · rintro ⟨f⟩
    exact ⟨(isoInduce e _ _ h).trans f⟩

def cardIso {V : Type*} (G : SimpleGraph V) (x : V) (T : Finset ({x}ᶜ : Set V)) :
    (Recon.card G x).induce (T : Set ({x}ᶜ : Set V)) ≃g
      G.induce ((T.map (Function.Embedding.subtype _) : Finset V) : Set V) where
  toFun a := ⟨a.1.1, by
    simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe]
    exact ⟨a.1, a.2, rfl⟩⟩
  invFun b := ⟨⟨b.1, by
    have hb := b.2
    simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at hb
    obtain ⟨c, _, hc⟩ := hb
    rw [← hc]; exact c.2⟩, by
    have hb := b.2
    simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at hb
    obtain ⟨c, hcT, hc⟩ := hb
    have : c = ⟨b.1, by rw [← hc]; exact c.2⟩ := Subtype.ext hc
    rw [← this]; exact hcT⟩
  left_inv a := rfl
  right_inv b := rfl
  map_rel_iff' := by
    intro a b
    simp

lemma vertex_count {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V) {k : ℕ}
    (F : SimpleGraph (Fin k)) :
    Finset.card (Finset.univ.filter
      (fun S : Finset V => x ∉ S ∧ Nonempty (G.induce (S : Set V) ≃g F))) =
      ind (Recon.card G x) F := by
  unfold ind
  symm
  refine Finset.card_nbij' (fun T => T.map (Function.Embedding.subtype _))
    (fun S => S.subtype (· ∈ ({x}ᶜ : Set V))) ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hT ⊢
    obtain ⟨f⟩ := hT
    refine ⟨?_, ⟨(cardIso G x T).symm.trans f⟩⟩
    simp only [Finset.mem_map, Function.Embedding.coe_subtype, not_exists, not_and]
    intro c _ hc
    exact c.2 hc
  · intro S hS
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
    obtain ⟨hx, ⟨f⟩⟩ := hS
    have hmap : (S.subtype (· ∈ ({x}ᶜ : Set V))).map (Function.Embedding.subtype _) = S := by
      apply Finset.subtype_map_of_mem
      intro y hy hyx
      exact hx (by rw [Set.mem_singleton_iff] at hyx; rw [← hyx]; exact hy)
    refine ⟨(cardIso G x _).trans ?_⟩
    rw [hmap]; exact f
  · intro T _
    ext y
    simp only [Finset.mem_subtype, Finset.mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨c, hc, hcy⟩
      have : c = y := Subtype.ext hcy
      rw [← this]; exact hc
    · intro hy
      exact ⟨y, hy, rfl⟩
  · intro S hS
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hS
    apply Finset.subtype_map_of_mem
    intro y hy hyx
    exact hS.1 (by rw [Set.mem_singleton_iff] at hyx; rw [← hyx]; exact hy)

lemma double_count {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (F : SimpleGraph (Fin k)) :
    ∑ x : V, Finset.card (Finset.univ.filter
      (fun S : Finset V => x ∉ S ∧ Nonempty (G.induce (S : Set V) ≃g F))) =
      (Fintype.card V - k) * ind G F := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := fun x (S : Finset V) => x ∉ S)
    (s := (Finset.univ : Finset V))
    (t := (Finset.univ.filter (fun S : Finset V => Nonempty (G.induce (S : Set V) ≃g F))))
  have e1 : ∀ x : V, Finset.card (Finset.univ.filter
      (fun S : Finset V => x ∉ S ∧ Nonempty (G.induce (S : Set V) ≃g F))) =
      Finset.card ((Finset.univ.filter (fun S : Finset V => Nonempty (G.induce (S : Set V) ≃g F))).bipartiteAbove (fun x (S : Finset V) => x ∉ S) x) := by
    intro x
    congr 1
    ext S
    simp [Finset.mem_bipartiteAbove, and_comm]
  simp_rw [e1]
  rw [h]
  unfold ind
  rw [Finset.card_eq_sum_ones, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  obtain ⟨f⟩ := hS
  have hc : S.card = k := by
    have := Fintype.card_congr f.toEquiv
    simpa using this
  have : (Finset.univ : Finset V).bipartiteBelow (fun x (S : Finset V) => x ∉ S) S = Sᶜ := by
    ext y; simp
  rw [this, Finset.card_compl, hc, mul_one]

end Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count

open Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count in
theorem Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count : Recon.Statements.S_conj_kelly_ulam__disconnected__kelly_induced_count := by
  intro n G H hGH k hk F
  classical
  have hset : ∀ A : SimpleGraph (Fin n),
      {S : Finset (Fin n) | Nonempty (A.induce (S : Set (Fin n)) ≃g F)}.ncard = ind A F := by
    intro A
    unfold ind
    rw [← Set.ncard_coe_finset]
    congr 1
    ext S
    simp
  rw [hset G, hset H]
  obtain ⟨σ, hσ⟩ := hGH
  have hG := double_count G F
  have hH := double_count H F
  simp_rw [vertex_count] at hG hH
  have hsum : ∑ x : Fin n, ind (Recon.card G x) F = ∑ y : Fin n, ind (Recon.card H y) F := by
    rw [← Equiv.sum_comp σ (fun y => ind (Recon.card H y) F)]
    apply Finset.sum_congr rfl
    intro x _
    obtain ⟨e⟩ := hσ x
    exact ind_iso e F
  have h2 : (Fintype.card (Fin n) - k) * ind G F = (Fintype.card (Fin n) - k) * ind H F := by
    rw [← hG, ← hH]
    convert hsum
  rw [Fintype.card_fin] at h2
  have hsum := h2
  have hpos : 0 < n - k := by omega
  exact Nat.eq_of_mul_eq_mul_left hpos hsum
