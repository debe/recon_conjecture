import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing
import Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count
import Recon.Checked.L_kelly_edge_count
import Recon.Checked.L_kelly_card_edges_add_degree

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing

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

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing := by
  classical
  intro n hn G ⟨u, v, huv, huniq, hfact⟩ H ⟨σ, hσ⟩
  set S : Set (Fin n) := ({u, v}ᶜ : Set (Fin n)) with hS
  have memS : ∀ x, x ∈ S ↔ x ≠ u ∧ x ≠ v := by intro x; simp [S]
  obtain ⟨fu⟩ := hσ u
  obtain ⟨fv⟩ := hσ v
  set Fu := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing.extE fu with hFu
  set Fv := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing.extE fv with hFv
  have hFuu : Fu u = σ u := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing.extE_a fu
  have hFvv : Fv v = σ v := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing.extE_a fv
  have hFuadj : ∀ x y, x ≠ u → y ≠ u → (H.Adj (Fu x) (Fu y) ↔ G.Adj x y) := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing.extE_adj fu
  have hFvadj : ∀ x y, x ≠ v → y ≠ v → (H.Adj (Fv x) (Fv y) ↔ G.Adj x y) := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing.extE_adj fv
  -- F on Fin k
  let k := Fintype.card S
  let F : SimpleGraph (Fin k) := (G.induce S).map (Fintype.equivFin S).toEmbedding
  have e0 : G.induce S ≃g F := SimpleGraph.Iso.map _ _
  have hk : k < n := by
    have := Fintype.card_subtype_lt (p := fun x : Fin n => x ∈ S) (x := u) (by simp [memS])
    rw [Fintype.card_fin] at this
    exact this
  have hKG : {T : Finset (Fin n) | Nonempty (G.induce (T : Set (Fin n)) ≃g F)} = {S.toFinset} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨f⟩
      have := huniq T ⟨e0.trans f.symm⟩
      rw [← Finset.coe_inj, Set.coe_toFinset]
      exact this
    · rintro rfl
      rw [Set.coe_toFinset]
      exact ⟨e0⟩
  have hK := Recon.Checked.L_conj_kelly_ulam__disconnected__kelly_induced_count n G H ⟨σ, hσ⟩ k hk F
  rw [hKG, Set.ncard_singleton] at hK
  obtain ⟨TH, hTH⟩ := Set.ncard_eq_one.mp hK.symm
  have huH : ∀ T : Finset (Fin n), Nonempty (H.induce (T : Set (Fin n)) ≃g F) → T = TH := by
    intro T hT
    have : T ∈ {T : Finset (Fin n) | Nonempty (H.induce (T : Set (Fin n)) ≃g F)} := hT
    rw [hTH] at this
    exact this
  have himg : ∀ (Φ : Fin n ≃ Fin n), (∀ x y, x ∈ S → y ∈ S → (H.Adj (Φ x) (Φ y) ↔ G.Adj x y)) →
      (S.toFinset.map Φ.toEmbedding) = TH := by
    intro Φ hΦ
    apply huH
    have hc : ((S.toFinset.map Φ.toEmbedding : Finset (Fin n)) : Set (Fin n)) = Φ '' S := by
      simp
    rw [hc]
    refine ⟨(Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing.isoOn Φ S (Φ '' S) ?_ hΦ).symm.trans e0⟩
    intro x
    exact (Φ.injective.mem_set_image).symm
  have hIu := himg Fu (fun x y hx hy => hFuadj x y ((memS x).1 hx).1 ((memS y).1 hy).1)
  have hIv := himg Fv (fun x y hx hy => hFvadj x y ((memS x).1 hx).2 ((memS y).1 hy).2)
  have hIeq : Fu '' S = Fv '' S := by
    have := congrArg (fun T : Finset (Fin n) => (T : Set (Fin n))) (hIu.trans hIv.symm)
    simpa using this
  have hpair : ({Fu u, Fu v} : Set (Fin n)) = {Fv u, Fv v} := by
    have := hIeq
    rw [hS, Set.image_compl_eq Fu.bijective, Set.image_compl_eq Fv.bijective, compl_inj_iff,
      Set.image_pair, Set.image_pair] at this
    exact this
  have hσuv : σ u ≠ σ v := fun h => huv (σ.injective h)
  have hFvu : Fv u = σ u := by
    have m : Fu u ∈ ({Fu u, Fu v} : Set (Fin n)) := by simp
    rw [hpair] at m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m
    rcases m with m | m
    · rw [← m, hFuu]
    · rw [hFuu, hFvv] at m; exact absurd m hσuv
  have hFuv : Fu v = σ v := by
    have m : Fu v ∈ ({Fu u, Fu v} : Set (Fin n)) := by simp
    rw [hpair] at m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m
    rcases m with m | m
    · rw [hFvu, ← hFuu] at m; exact absurd (Fu.injective m) (Ne.symm huv)
    · rw [m, hFvv]
  have hSu : ∀ x, x ∈ S → x ≠ u := fun x hx => ((memS x).1 hx).1
  have hSv : ∀ x, x ∈ S → x ≠ v := fun x hx => ((memS x).1 hx).2
  let ψ : Fin n ≃ Fin n := Fu.trans Fv.symm
  have hψ : ∀ x, ψ x = Fv.symm (Fu x) := fun x => rfl
  have hψS : ∀ x, x ∈ S ↔ ψ x ∈ S := by
    intro x
    rw [hψ, ← Fu.injective.mem_set_image, hIeq, Equiv.image_eq_preimage_symm]
    rfl
  have hψadj : ∀ x y, x ∈ S → y ∈ S → (G.Adj (ψ x) (ψ y) ↔ G.Adj x y) := by
    intro x y hx hy
    rw [← hFvadj (ψ x) (ψ y) (hSv _ ((hψS x).1 hx)) (hSv _ ((hψS y).1 hy)), hψ, hψ,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hFuadj x y (hSu x hx) (hSu y hy)
  let g := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing.isoOn (G := G) (H := G) ψ S S hψS hψadj
  have hg : ∀ y : S, (g y).1 = ψ y.1 := fun y => rfl
  obtain ⟨h, h1, h2⟩ := hfact g
  let hh : Equiv.Perm (Fin n) :=
    Equiv.Perm.subtypeCongr (p := fun x => x ∈ S) h.toEquiv (Equiv.refl _)
  have hhS : ∀ x (hx : x ∈ S), hh x = (h ⟨x, hx⟩).1 := by
    intro x hx
    exact Equiv.Perm.subtypeCongr.left_apply _ _ hx
  have hhN : ∀ x, x ∉ S → hh x = x := by
    intro x hx
    rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
    rfl
  have hhu : hh u = u := hhN u (by simp [memS])
  have hhv : hh v = v := hhN v (by simp [memS])
  have hvS : ∀ x, x ≠ u → x ∉ S → x = v := by
    intro x hxu hx
    by_contra hxv
    exact hx ((memS x).2 ⟨hxu, hxv⟩)
  have hhne : ∀ x, x ≠ u → hh x ≠ u := by
    intro x hx
    by_cases hxS : x ∈ S
    · rw [hhS x hxS]; exact hSu _ (h ⟨x, hxS⟩).2
    · rw [hhN x hxS]; exact hx
  have hvadj : ∀ x, x ∈ S → (G.Adj v (hh x) ↔ G.Adj v x) := by
    intro x hx
    rw [hhS x hx]
    exact h1 ⟨x, hx⟩
  have hhadj : ∀ a b, a ≠ u → b ≠ u → (G.Adj (hh a) (hh b) ↔ G.Adj a b) := by
    intro a b ha hb
    by_cases haS : a ∈ S
    · by_cases hbS : b ∈ S
      · rw [hhS a haS, hhS b hbS]
        exact h.map_rel_iff (a := ⟨a, haS⟩) (b := ⟨b, hbS⟩)
      · have := hvS b hb hbS
        subst this
        rw [hhv, G.adj_comm, hvadj a haS, G.adj_comm]
    · have := hvS a ha haS
      subst this
      by_cases hbS : b ∈ S
      · rw [hhv, hvadj b hbS]
      · have := hvS b hb hbS
        subst this
        rw [hhv]
  let Φ : Fin n ≃ Fin n := hh.trans Fu
  have hΦ : ∀ x, Φ x = Fu (hh x) := fun x => rfl
  have hΦu : Φ u = σ u := by rw [hΦ, hhu, hFuu]
  have hΦv : Φ v = σ v := by rw [hΦ, hhv, hFuv]
  have hoff : ∀ a b, a ≠ u → b ≠ u → (H.Adj (Φ a) (Φ b) ↔ G.Adj a b) := by
    intro a b ha hb
    rw [hΦ, hΦ, hFuadj _ _ (hhne a ha) (hhne b hb)]
    exact hhadj a b ha hb
  have hkeyS : ∀ b, b ∈ S → (H.Adj (σ u) (Φ b) ↔ G.Adj u b) := by
    intro b hb
    have e1 : Φ b = Fv (ψ (hh b)) := by
      rw [hΦ, hψ, Equiv.apply_symm_apply]
    have hmem : ψ (hh b) ∈ S := by
      rw [hhS b hb]; exact (hψS _).1 (h ⟨b, hb⟩).2
    rw [e1, ← hFvu, hFvadj u _ huv (hSv _ hmem), hhS b hb, ← hg]
    exact h2 ⟨b, hb⟩
  have hdeg : (G.neighborSet u).ncard = (H.neighborSet (σ u)).ncard := by
    have e1 := Recon.Checked.L_kelly_card_edges_add_degree n G u
    have e2 := Recon.Checked.L_kelly_card_edges_add_degree n H (σ u)
    have e3 := Recon.Checked.L_kelly_edge_count.ncard_eq_of_iso fu
    have e4 := Recon.Checked.L_kelly_edge_count n hn G H ⟨σ, hσ⟩
    omega
  have hpre : (Φ ⁻¹' H.neighborSet (σ u)).ncard = (H.neighborSet (σ u)).ncard :=
    Set.ncard_preimage_of_injective_subset_range Φ.injective (by simp)
  have hkey' : ∀ b, b ≠ v → (b ∈ Φ ⁻¹' H.neighborSet (σ u) ↔ b ∈ G.neighborSet u) := by
    intro b hb
    simp only [Set.mem_preimage, SimpleGraph.mem_neighborSet]
    by_cases hbu : b = u
    · subst hbu
      rw [hΦu]
      simp
    · exact hkeyS b ((memS b).2 ⟨hbu, hb⟩)
  have huv' : H.Adj (σ u) (σ v) ↔ G.Adj u v := by
    by_contra hne
    rw [iff_iff_implies_and_implies, not_and_or, not_imp, not_imp] at hne
    rcases hne with ⟨hH, hG⟩ | ⟨hG, hH⟩
    · have hsub : G.neighborSet u ⊂ Φ ⁻¹' H.neighborSet (σ u) := by
        rw [Set.ssubset_iff_of_subset]
        · refine ⟨v, ?_, hG⟩
          simp only [Set.mem_preimage, SimpleGraph.mem_neighborSet]
          rw [hΦv]; exact hH
        · intro b hb
          have hbv : b ≠ v := by rintro rfl; exact hG hb
          exact (hkey' b hbv).2 hb
      have := Set.ncard_lt_ncard hsub
      omega
    · have hsub : Φ ⁻¹' H.neighborSet (σ u) ⊂ G.neighborSet u := by
        rw [Set.ssubset_iff_of_subset]
        · refine ⟨v, hG, ?_⟩
          simp only [Set.mem_preimage, SimpleGraph.mem_neighborSet]
          rw [hΦv]; exact hH
        · intro b hb
          have hbv : b ≠ v := by
            rintro rfl
            apply hH
            have := hb
            simp only [Set.mem_preimage, SimpleGraph.mem_neighborSet] at this
            rw [hΦv] at this
            exact this
          exact (hkey' b hbv).1 hb
      have := Set.ncard_lt_ncard hsub
      omega
  have hkey : ∀ b, H.Adj (σ u) (Φ b) ↔ G.Adj u b := by
    intro b
    by_cases hbv : b = v
    · subst hbv; rw [hΦv]; exact huv'
    · have := hkey' b hbv
      simp only [Set.mem_preimage, SimpleGraph.mem_neighborSet] at this
      exact this
  refine ⟨{ toEquiv := Φ, map_rel_iff' := ?_ }⟩
  intro a b
  by_cases ha : a = u
  · subst ha
    rw [hΦu]
    exact hkey b
  · by_cases hb : b = u
    · subst hb
      rw [hΦu, H.adj_comm, G.adj_comm]
      exact hkey a
    · exact hoff a b ha hb
