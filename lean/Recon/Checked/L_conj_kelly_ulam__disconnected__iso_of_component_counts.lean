import Mathlib
import Recon.Statements.S_conj_kelly_ulam__disconnected__iso_of_component_counts

namespace Recon.Checked.L_conj_kelly_ulam__disconnected__iso_of_component_counts

open SimpleGraph

theorem match_fibres {α β : Type*} [Finite α] [Finite β]
    (r : α → α → Prop) (s : α → β → Prop)
    (hr : Equivalence r)
    (hs1 : ∀ a a' b, s a b → s a' b → r a a')
    (hs2 : ∀ a a' b, r a a' → s a' b → s a b)
    (hsur : ∀ b, ∃ a, s a b)
    (hcard : ∀ a, Nat.card {a' // r a' a} = Nat.card {b // s a b}) :
    ∃ e : α ≃ β, ∀ a, s a (e a) := by
  classical
  let f : α → Set α := fun a => {a' | r a a'}
  let g : β → Set α := fun b => {a' | s a' b}
  have hg : ∀ a0 b, g b = f a0 ↔ s a0 b := by
    intro a0 b
    constructor
    · intro h
      have : a0 ∈ f a0 := hr.refl a0
      rw [← h] at this
      exact this
    · intro h
      ext x
      constructor
      · intro hx
        exact hs1 a0 x b h hx
      · intro hx
        exact hs2 x a0 b (hr.symm hx) h
  have hf : ∀ a0 a, f a = f a0 ↔ r a a0 := by
    intro a0 a
    constructor
    · intro h
      have : a ∈ f a := hr.refl a
      rw [h] at this
      exact hr.symm this
    · intro h
      ext x
      constructor
      · intro hx
        exact hr.trans (hr.symm h) hx
      · intro hx
        exact hr.trans h hx
  have hfib : ∀ q, Nonempty ({a // f a = q} ≃ {b // g b = q}) := by
    intro q
    by_cases hq : ∃ a0, f a0 = q
    · obtain ⟨a0, rfl⟩ := hq
      have h1 : {a // f a = f a0} ≃ {a' // r a' a0} := Equiv.subtypeEquivRight (hf a0)
      have h2 : {b // g b = f a0} ≃ {b // s a0 b} := Equiv.subtypeEquivRight (hg a0)
      rw [← Finite.card_eq, Nat.card_congr h1, Nat.card_congr h2, hcard]
    · have i1 : IsEmpty {a // f a = q} := ⟨fun ⟨a, ha⟩ => hq ⟨a, ha⟩⟩
      have i2 : IsEmpty {b // g b = q} := ⟨fun ⟨b, hb⟩ => by
        obtain ⟨a, ha⟩ := hsur b
        exact hq ⟨a, ((hg a b).mpr ha).symm.trans hb⟩⟩
      exact ⟨Equiv.equivOfIsEmpty _ _⟩
  refine ⟨Equiv.ofFiberEquiv (fun q => (hfib q).some), fun a => ?_⟩
  have hm := Equiv.ofFiberEquiv_map (fun q => (hfib q).some) a
  exact (hg a _).mp hm

end Recon.Checked.L_conj_kelly_ulam__disconnected__iso_of_component_counts

open SimpleGraph in
theorem Recon.Checked.L_conj_kelly_ulam__disconnected__iso_of_component_counts : Recon.Statements.S_conj_kelly_ulam__disconnected__iso_of_component_counts := by
  intro n G H hcount
  classical
  let rG : G.ConnectedComponent → G.ConnectedComponent → Prop :=
    fun c c' => Nonempty (G.induce c.supp ≃g G.induce c'.supp)
  let s : G.ConnectedComponent → H.ConnectedComponent → Prop :=
    fun c d => Nonempty (G.induce c.supp ≃g H.induce d.supp)
  have key : ∀ c : G.ConnectedComponent, Nat.card {c' // rG c' c} = Nat.card {d // s c d} := by
    intro c
    let F := (G.induce c.supp).map (Fintype.equivFin c.supp).toEmbedding
    let i : G.induce c.supp ≃g F := Iso.map _ _
    have hF : F.Connected := i.connected_iff.mp c.connected_toSimpleGraph
    have h := hcount _ F hF
    have e1 : {c' : G.ConnectedComponent | Nonempty (G.induce c'.supp ≃g F)} = {c' | rG c' c} := by
      ext c'
      exact ⟨fun ⟨j⟩ => ⟨j.trans i.symm⟩, fun ⟨j⟩ => ⟨j.trans i⟩⟩
    have e2 : {d : H.ConnectedComponent | Nonempty (H.induce d.supp ≃g F)} = {d | s c d} := by
      ext d
      exact ⟨fun ⟨j⟩ => ⟨i.trans j.symm⟩, fun ⟨j⟩ => ⟨j.symm.trans i⟩⟩
    rw [e1, e2, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h
    exact h
  have hsur : ∀ d : H.ConnectedComponent, ∃ c, s c d := by
    intro d
    let F := (H.induce d.supp).map (Fintype.equivFin d.supp).toEmbedding
    let i : H.induce d.supp ≃g F := Iso.map _ _
    have hF : F.Connected := i.connected_iff.mp d.connected_toSimpleGraph
    have h := hcount _ F hF
    have hne : {d' : H.ConnectedComponent | Nonempty (H.induce d'.supp ≃g F)}.ncard ≠ 0 :=
      Set.ncard_ne_zero_of_mem (a := d) ⟨i⟩
    rw [← h] at hne
    obtain ⟨c, ⟨j⟩⟩ := Set.nonempty_of_ncard_ne_zero hne
    exact ⟨c, ⟨j.trans i.symm⟩⟩
  have hr : Equivalence rG :=
    ⟨fun c => ⟨Iso.refl⟩, fun ⟨j⟩ => ⟨j.symm⟩, fun ⟨j⟩ ⟨k⟩ => ⟨j.trans k⟩⟩
  have hs1 : ∀ a a' b, s a b → s a' b → rG a a' := fun _ _ _ ⟨j⟩ ⟨k⟩ => ⟨j.trans k.symm⟩
  have hs2 : ∀ a a' b, rG a a' → s a' b → s a b := fun _ _ _ ⟨j⟩ ⟨k⟩ => ⟨j.trans k⟩
  obtain ⟨φ, hφ⟩ := Recon.Checked.L_conj_kelly_ulam__disconnected__iso_of_component_counts.match_fibres
    rG s hr hs1 hs2 hsur key
  let ψ : ∀ c, G.induce c.supp ≃g H.induce (φ c).supp := fun c => (hφ c).some
  have hmem : ∀ c (w : Fin n), w ∈ (φ c).supp ↔ φ.symm (H.connectedComponentMk w) = c := by
    intro c w
    rw [ConnectedComponent.mem_supp_iff, Equiv.symm_apply_eq, eq_comm]
  let fib : ∀ c, {v // G.connectedComponentMk v = c} ≃
      {w // φ.symm (H.connectedComponentMk w) = c} := fun c =>
    ((ψ c).toEquiv).trans (Equiv.subtypeEquivRight (hmem c))
  let e : Fin n ≃ Fin n := Equiv.ofFiberEquiv fib
  have he : ∀ c (v : Fin n) (h : v ∈ c.supp), e v = (ψ c ⟨v, h⟩).1 := by
    intro c v h
    have h' : G.connectedComponentMk v = c := h
    subst h'
    rfl
  have hm : ∀ v, H.connectedComponentMk (e v) = φ (G.connectedComponentMk v) := by
    intro v
    have := Equiv.ofFiberEquiv_map fib v
    rw [Equiv.symm_apply_eq] at this
    exact this
  refine ⟨⟨e, fun {u v} => ?_⟩⟩
  constructor
  · intro h
    have huv : G.connectedComponentMk u = G.connectedComponentMk v := by
      apply φ.injective
      rw [← hm, ← hm]
      exact ConnectedComponent.connectedComponentMk_eq_of_adj h
    have hu : u ∈ (G.connectedComponentMk u).supp := rfl
    have hv : v ∈ (G.connectedComponentMk u).supp := huv.symm
    rw [he _ u hu, he _ v hv] at h
    exact (ψ (G.connectedComponentMk u)).map_rel_iff.mp h
  · intro h
    have huv : G.connectedComponentMk u = G.connectedComponentMk v :=
      ConnectedComponent.connectedComponentMk_eq_of_adj h
    have hu : u ∈ (G.connectedComponentMk u).supp := rfl
    have hv : v ∈ (G.connectedComponentMk u).supp := huv.symm
    show H.Adj (e u) (e v)
    rw [he _ u hu, he _ v hv]
    exact (ψ (G.connectedComponentMk u)).map_rel_iff.mpr h
