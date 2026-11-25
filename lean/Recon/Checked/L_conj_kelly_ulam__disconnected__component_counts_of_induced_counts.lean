import Mathlib
import Recon.Statements.S_conj_kelly_ulam__disconnected__component_counts_of_induced_counts
import Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count
import Recon.Checked.L_conj_kelly_ulam__disconnected__iso_of_component_counts

namespace Recon.Checked.L_conj_kelly_ulam__disconnected__component_counts_of_induced_counts

open SimpleGraph Classical
open Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count

def subIso {V : Type*} (A : SimpleGraph V) (X : Set V) (T : Finset X) :
    (A.induce X).induce (T : Set X) ≃g
      A.induce ((T.map (Function.Embedding.subtype _) : Finset V) : Set V) where
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

noncomputable def indIn {V : Type*} [Fintype V] (A : SimpleGraph V) (X : Set V) {k : ℕ}
    (F : SimpleGraph (Fin k)) : ℕ :=
  Finset.card (Finset.univ.filter
      (fun S : Finset V => ((S : Set V) ⊆ X) ∧ Nonempty (A.induce (S : Set V) ≃g F)))

lemma indIn_eq {V : Type*} [Fintype V] (A : SimpleGraph V) (X : Set V) [Fintype X] {k : ℕ}
    (F : SimpleGraph (Fin k)) : indIn A X F = ind (A.induce X) F := by
  unfold indIn ind
  symm
  refine Finset.card_nbij' (fun T => T.map (Function.Embedding.subtype _))
    (fun S => S.subtype (· ∈ X)) ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hT ⊢
    obtain ⟨f⟩ := hT
    refine ⟨?_, ⟨(subIso A X T).symm.trans f⟩⟩
    intro y hy
    simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at hy
    obtain ⟨c, _, rfl⟩ := hy
    exact c.2
  · intro S hS
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
    obtain ⟨hx, ⟨f⟩⟩ := hS
    have hmap : (S.subtype (· ∈ X)).map (Function.Embedding.subtype _) = S := by
      apply Finset.subtype_map_of_mem
      intro y hy
      exact hx hy
    refine ⟨(subIso A X _).trans ?_⟩
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
    intro y hy
    exact hS.1 hy

lemma decomp {V : Type*} [Fintype V] [DecidableEq V] (A : SimpleGraph V) {k : ℕ} (F : SimpleGraph (Fin k))
    [DecidableRel A.Adj] (hF : F.Connected) : ind A F = ∑ c : A.ConnectedComponent, indIn A c.supp F := by
  unfold ind indIn
  rw [← Finset.card_biUnion]
  · congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨f⟩
      have hS : (A.induce (S : Set V)).Connected := f.connected_iff.mpr hF
      obtain ⟨v⟩ := hS.nonempty
      refine ⟨A.connectedComponentMk v.1, ?_, ⟨f⟩⟩
      intro w hw
      have hr : (A.induce (S : Set V)).Reachable v ⟨w, hw⟩ := hS.preconnected _ _
      have hr' := hr.map (Embedding.induce (S : Set V)).toHom
      rw [ConnectedComponent.mem_supp_iff]
      exact (ConnectedComponent.sound hr').symm
    · rintro ⟨c, _, h⟩
      exact h
  · intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro S h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨h1, ⟨f⟩⟩ := h1
    obtain ⟨h2, _⟩ := h2
    have hS : (A.induce (S : Set V)).Connected := f.connected_iff.mpr hF
    obtain ⟨v⟩ := hS.nonempty
    apply hcc'
    have a1 : v.1 ∈ c.supp := h1 v.2
    have a2 : v.1 ∈ c'.supp := h2 v.2
    rw [ConnectedComponent.mem_supp_iff] at a1 a2
    rw [← a1, ← a2]

lemma ind_small {W : Type*} [Fintype W] (B : SimpleGraph W) {k : ℕ} (F : SimpleGraph (Fin k))
    (hW : Fintype.card W ≤ k) : ind B F = if Nonempty (B ≃g F) then 1 else 0 := by
  unfold ind
  have iu : B.induce ((Finset.univ : Finset W) : Set W) ≃g B := by
    rw [Finset.coe_univ]
    exact induceUnivIso B
  have key : ∀ T : Finset W, Nonempty (B.induce (T : Set W) ≃g F) ↔
      T = Finset.univ ∧ Nonempty (B ≃g F) := by
    intro T
    constructor
    · rintro ⟨f⟩
      have hc : T.card = k := by
        have := Fintype.card_congr f.toEquiv
        simpa using this
      have hT : T = Finset.univ := Finset.eq_univ_of_card T
        (le_antisymm (Finset.card_le_univ T) (by omega))
      subst hT
      exact ⟨rfl, ⟨iu.symm.trans f⟩⟩
    · rintro ⟨rfl, ⟨f⟩⟩
      exact ⟨iu.trans f⟩
  simp_rw [key]
  split_ifs with h
  · simp [h, Finset.filter_eq']
  · simp [h]

lemma comp_eq_sum {V : Type*} [Fintype V] [DecidableEq V] (A : SimpleGraph V)
    [DecidableRel A.Adj] {k : ℕ}
    (F : SimpleGraph (Fin k)) :
    {c : A.ConnectedComponent | Nonempty (A.induce c.supp ≃g F)}.ncard =
      ∑ c : A.ConnectedComponent, if Nonempty (A.induce c.supp ≃g F) then 1 else 0 := by
  rw [Finset.sum_boole, ← Set.ncard_coe_finset]
  congr 1
  ext c
  simp

lemma split {V : Type*} [Fintype V] [DecidableEq V] (A : SimpleGraph V)
    [DecidableRel A.Adj] {k : ℕ} (F : SimpleGraph (Fin k))
    (hF : F.Connected) :
    ind A F = (∑ c : {c : A.ConnectedComponent // k < Nat.card c.supp},
      ind (A.induce c.1.supp) F) +
      {c : A.ConnectedComponent | Nonempty (A.induce c.supp ≃g F)}.ncard := by
  rw [decomp A F hF, comp_eq_sum]
  simp_rw [indIn_eq]
  have s1 := Fintype.sum_subtype_add_sum_subtype
    (fun c : A.ConnectedComponent => k < Nat.card c.supp)
    (fun c => ind (A.induce c.supp) F)
  have s2 := Fintype.sum_subtype_add_sum_subtype
    (fun c : A.ConnectedComponent => k < Nat.card c.supp)
    (fun c => if Nonempty (A.induce c.supp ≃g F) then 1 else 0)
  have h1 : ∑ c : {c : A.ConnectedComponent // k < Nat.card c.supp},
      (if Nonempty (A.induce c.1.supp ≃g F) then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    rw [ite_eq_right_iff]
    intro hne
    exfalso
    revert hne
    rintro ⟨f⟩
    have := Nat.card_congr f.toEquiv
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    have h2 := c.2
    simp only [Nat.card_eq_fintype_card] at h2
    omega
  have h2 : ∀ c : {c : A.ConnectedComponent // ¬ k < Nat.card c.supp},
      ind (A.induce c.1.supp) F = if Nonempty (A.induce c.1.supp ≃g F) then 1 else 0 := by
    intro c
    apply ind_small
    have h3 := c.2
    simp only [Nat.card_eq_fintype_card] at h3
    omega
  rw [Finset.sum_congr rfl (fun c _ => h2 c)] at s1
  omega

lemma card_sub {V : Type*} [Fintype V] (A : SimpleGraph V) (k m : ℕ) (hm : k < m)
    (F : SimpleGraph (Fin m)) {U : Type*} (Y : SimpleGraph U) (j : Y ≃g F) :
    Nat.card {a : {c : A.ConnectedComponent // k < Nat.card c.supp} //
        Nonempty (A.induce a.1.supp ≃g Y)} =
      {c : A.ConnectedComponent | Nonempty (A.induce c.supp ≃g F)}.ncard := by
  rw [← Nat.card_coe_set_eq]
  apply Nat.card_congr
  exact {
    toFun := fun a => ⟨a.1.1, a.2.map (fun f => f.trans j)⟩
    invFun := fun c => ⟨⟨c.1, by
      obtain ⟨f⟩ := c.2
      have := Nat.card_congr f.toEquiv
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
      simp only [Nat.card_eq_fintype_card]
      omega⟩, c.2.map (fun f => f.trans j.symm)⟩
    left_inv := fun a => rfl
    right_inv := fun c => rfl }

lemma matching {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (k : ℕ)
    (ih : ∀ m, k < m → ∀ F : SimpleGraph (Fin m), F.Connected →
      {c : G.ConnectedComponent | Nonempty (G.induce c.supp ≃g F)}.ncard =
      {c : H.ConnectedComponent | Nonempty (H.induce c.supp ≃g F)}.ncard) :
    ∃ φ : {c : G.ConnectedComponent // k < Nat.card c.supp} ≃
        {d : H.ConnectedComponent // k < Nat.card d.supp},
      ∀ c, Nonempty (G.induce c.1.supp ≃g H.induce (φ c).1.supp) := by
  let r : {c : G.ConnectedComponent // k < Nat.card c.supp} →
      {c : G.ConnectedComponent // k < Nat.card c.supp} → Prop :=
    fun a a' => Nonempty (G.induce a.1.supp ≃g G.induce a'.1.supp)
  let s : {c : G.ConnectedComponent // k < Nat.card c.supp} →
      {d : H.ConnectedComponent // k < Nat.card d.supp} → Prop :=
    fun a b => Nonempty (G.induce a.1.supp ≃g H.induce b.1.supp)
  have hr : Equivalence r :=
    ⟨fun c => ⟨Iso.refl⟩, fun ⟨j⟩ => ⟨j.symm⟩, fun ⟨j⟩ ⟨k⟩ => ⟨j.trans k⟩⟩
  have hs1 : ∀ a a' b, s a b → s a' b → r a a' := fun _ _ _ ⟨j⟩ ⟨k⟩ => ⟨j.trans k.symm⟩
  have hs2 : ∀ a a' b, r a a' → s a' b → s a b := fun _ _ _ ⟨j⟩ ⟨k⟩ => ⟨j.trans k⟩
  have hcard : ∀ a, Nat.card {a' // r a' a} = Nat.card {b // s a b} := by
    intro a
    let F := (G.induce a.1.supp).map (Finite.equivFin a.1.supp).toEmbedding
    let i : G.induce a.1.supp ≃g F := Iso.map _ _
    have hF : F.Connected := i.connected_iff.mp a.1.connected_toSimpleGraph
    have h := ih _ a.2 F hF
    rw [← card_sub G k _ a.2 F _ i, ← card_sub H k _ a.2 F _ i] at h
    rw [h]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun b => ⟨fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ => ⟨f.symm⟩⟩)
  have hsur : ∀ b, ∃ a, s a b := by
    intro b
    let F := (H.induce b.1.supp).map (Finite.equivFin b.1.supp).toEmbedding
    let i : H.induce b.1.supp ≃g F := Iso.map _ _
    have hF : F.Connected := i.connected_iff.mp b.1.connected_toSimpleGraph
    have h := ih _ b.2 F hF
    rw [← card_sub G k _ b.2 F _ i, ← card_sub H k _ b.2 F _ i] at h
    have hne : Nonempty {b' : {d : H.ConnectedComponent // k < Nat.card d.supp} //
        Nonempty (H.induce b'.1.supp ≃g H.induce b.1.supp)} := ⟨⟨b, ⟨Iso.refl⟩⟩⟩
    have hpos := Nat.card_pos (α := {b' : {d : H.ConnectedComponent // k < Nat.card d.supp} //
        Nonempty (H.induce b'.1.supp ≃g H.induce b.1.supp)})
    rw [← h] at hpos
    obtain ⟨⟨a, ha⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨a, ha⟩
  exact Recon.Checked.L_conj_kelly_ulam__disconnected__iso_of_component_counts.match_fibres
    r s hr hs1 hs2 hsur hcard

lemma zero {n : ℕ} (A : SimpleGraph (Fin n)) (hA : ¬ A.Connected) (k : ℕ) (hk : n ≤ k)
    (F : SimpleGraph (Fin k)) :
    {c : A.ConnectedComponent | Nonempty (A.induce c.supp ≃g F)}.ncard = 0 := by
  rw [Set.ncard_eq_zero]
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨f⟩
  apply hA
  have hc := Nat.card_congr f.toEquiv
  rw [Nat.card_coe_set_eq] at hc
  have hu : c.supp = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ Set.finite_univ
    rw [Set.ncard_univ, hc]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  obtain ⟨v, _⟩ := c.nonempty_supp
  rw [connected_iff]
  refine ⟨fun u w => ?_, ⟨v⟩⟩
  have hu' : u ∈ c.supp := by rw [hu]; trivial
  have hw' : w ∈ c.supp := by rw [hu]; trivial
  rw [ConnectedComponent.mem_supp_iff] at hu' hw'
  exact ConnectedComponent.exact (hu'.trans hw'.symm)

end Recon.Checked.L_conj_kelly_ulam__disconnected__component_counts_of_induced_counts

open Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count
  Recon.Checked.L_conj_kelly_ulam__disconnected__component_counts_of_induced_counts in
theorem Recon.Checked.L_conj_kelly_ulam__disconnected__component_counts_of_induced_counts : Recon.Statements.S_conj_kelly_ulam__disconnected__component_counts_of_induced_counts := by
  intro n G H hG hH hind
  classical
  have hset : ∀ A : SimpleGraph (Fin n), ∀ k (F : SimpleGraph (Fin k)),
      {S : Finset (Fin n) | Nonempty (A.induce (S : Set (Fin n)) ≃g F)}.ncard = ind A F := by
    intro A k F
    unfold ind
    rw [← Set.ncard_coe_finset]
    congr 1
    ext S
    simp
  have P : ∀ d k, n ≤ k + d → ∀ F : SimpleGraph (Fin k), F.Connected →
      {c : G.ConnectedComponent | Nonempty (G.induce c.supp ≃g F)}.ncard =
      {c : H.ConnectedComponent | Nonempty (H.induce c.supp ≃g F)}.ncard := by
    intro d
    induction d with
    | zero =>
      intro k hk F _
      rw [zero G hG k (by omega), zero H hH k (by omega)]
    | succ d ih =>
      intro k hk F hF
      by_cases hkn : n ≤ k
      · rw [zero G hG k hkn, zero H hH k hkn]
      · have ih' : ∀ m, k < m → ∀ F : SimpleGraph (Fin m), F.Connected →
            {c : G.ConnectedComponent | Nonempty (G.induce c.supp ≃g F)}.ncard =
            {c : H.ConnectedComponent | Nonempty (H.induce c.supp ≃g F)}.ncard :=
          fun m hm F hF => ih m (by omega) F hF
        obtain ⟨φ, hφ⟩ := matching G H k ih'
        have e := hind k (by omega) F
        rw [hset, hset, split G F hF, split H F hF] at e
        have hs : (∑ c : {c : G.ConnectedComponent // k < Nat.card c.supp},
            ind (G.induce c.1.supp) F) =
            ∑ c : {c : H.ConnectedComponent // k < Nat.card c.supp},
            ind (H.induce c.1.supp) F := by
          rw [← Equiv.sum_comp φ]
          apply Finset.sum_congr rfl
          intro c _
          obtain ⟨ψ⟩ := hφ c
          exact ind_iso ψ F
        omega
  intro k F hF
  exact P n k (by omega) F hF
