import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class
import Recon.Checked.L_kelly_edge_count
import Recon.Checked.L_kelly_card_edges_add_degree

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class

open SimpleGraph

lemma ncard_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.edgeSet.ncard = H.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr e.mapEdgeSet

lemma card_add_deg {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    (G.induce ({v}ᶜ : Set V)).edgeSet.ncard + (G.neighborSet v).ncard = G.edgeSet.ncard := by
  classical
  rw [Recon.Checked.L_kelly_card_edges_add_degree.ncard_edgeSet_eq,
    Recon.Checked.L_kelly_card_edges_add_degree.ncard_edgeSet_eq, SimpleGraph.ncard_neighborSet,
    SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  have := G.degree_le_card_edgeFinset v
  omega

lemma mem_pair_compl {V : Type*} {x z w : V} :
    w ∈ ({x, z}ᶜ : Set V) ↔ w ≠ x ∧ w ≠ z := by
  simp

def iterIso {V : Type*} (G : SimpleGraph V) (x z : V) (hz : z ≠ x) :
    (G.induce ({x}ᶜ : Set V)).induce ({⟨z, hz⟩}ᶜ : Set ({x}ᶜ : Set V)) ≃g
      G.induce ({x, z}ᶜ : Set V) where
  toFun w := ⟨w.1.1, mem_pair_compl.2 ⟨w.1.2, fun h => w.2 (Subtype.ext h)⟩⟩
  invFun w := ⟨⟨w.1, (mem_pair_compl.1 w.2).1⟩, fun h =>
    (mem_pair_compl.1 w.2).2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

lemma img_nbr {V : Type*} (G : SimpleGraph V) (x z : V) (hz : z ≠ x) :
    Subtype.val '' ((G.induce ({x}ᶜ : Set V)).neighborSet ⟨z, hz⟩) =
      G.neighborSet z \ {x} := by
  ext w
  simp only [Set.mem_image, mem_neighborSet, comap_adj, Function.Embedding.subtype_apply,
    Subtype.exists, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨w', hw', hadj, rfl⟩
    exact ⟨hadj, hw'⟩
  · rintro ⟨hadj, hw⟩
    exact ⟨w, hw, hadj, rfl⟩

open Classical in
lemma deg_in_card {V : Type*} [Fintype V] (G : SimpleGraph V) (x z : V) (hz : z ≠ x) :
    ((G.induce ({x}ᶜ : Set V)).neighborSet ⟨z, hz⟩).ncard + (if G.Adj x z then 1 else 0) =
      (G.neighborSet z).ncard := by
  have h1 := Set.ncard_image_of_injective ((G.induce ({x}ᶜ : Set V)).neighborSet ⟨z, hz⟩)
    Subtype.val_injective
  rw [img_nbr] at h1
  rw [← h1]
  by_cases h : G.Adj x z
  · rw [ite_eq_left h]
    exact Set.ncard_sdiff_singleton_add_one (h.symm : x ∈ G.neighborSet z)
  · rw [ite_eq_right h, Set.sdiff_singleton_eq_self (fun h' => h (h' : G.Adj z x).symm), add_zero]

open Classical in
lemma bit_law {V : Type*} [Fintype V] (G : SimpleGraph V) (x z : V) (hz : z ≠ x) :
    (G.induce ({x, z}ᶜ : Set V)).edgeSet.ncard + (G.neighborSet x).ncard +
      (G.neighborSet z).ncard = G.edgeSet.ncard + (if G.Adj x z then 1 else 0) := by
  have h1 := card_add_deg G x
  have h2 := card_add_deg (G.induce ({x}ᶜ : Set V)) ⟨z, hz⟩
  have h3 := ncard_iso (iterIso G x z hz)
  have h4 := deg_in_card G x z hz
  omega

def restrictIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {x : V} {x' : W}
    (f : G.induce ({x}ᶜ : Set V) ≃g H.induce ({x'}ᶜ : Set W)) (z : V) (hz : z ≠ x) :
    G.induce ({x, z}ᶜ : Set V) ≃g H.induce ({x', (f ⟨z, hz⟩).1}ᶜ : Set W) where
  toFun v := ⟨(f ⟨v.1, (mem_pair_compl.1 v.2).1⟩).1, mem_pair_compl.2
    ⟨(f ⟨v.1, (mem_pair_compl.1 v.2).1⟩).2, fun h =>
      (mem_pair_compl.1 v.2).2 (congrArg Subtype.val (f.injective (Subtype.ext h)))⟩⟩
  invFun w := ⟨(f.symm ⟨w.1, (mem_pair_compl.1 w.2).1⟩).1, mem_pair_compl.2
    ⟨(f.symm ⟨w.1, (mem_pair_compl.1 w.2).1⟩).2, fun h => (mem_pair_compl.1 w.2).2 (by
      have h2 : f.symm ⟨w.1, (mem_pair_compl.1 w.2).1⟩ = ⟨z, hz⟩ := Subtype.ext h
      have h3 := congrArg f h2
      rw [RelIso.apply_symm_apply] at h3
      exact congrArg Subtype.val h3)⟩⟩
  left_inv v := by
    apply Subtype.ext
    have := congrArg Subtype.val (f.symm_apply_apply ⟨v.1, (mem_pair_compl.1 v.2).1⟩)
    exact this
  right_inv w := by
    apply Subtype.ext
    have := congrArg Subtype.val (f.apply_symm_apply ⟨w.1, (mem_pair_compl.1 w.2).1⟩)
    exact this
  map_rel_iff' {a b} := by
    change (H.induce ({x'}ᶜ : Set W)).Adj (f ⟨a.1, _⟩) (f ⟨b.1, _⟩) ↔ G.Adj a.1 b.1
    rw [f.map_rel_iff]
    rfl

lemma iso_of_nbhd {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v : V} {w : W} (e : Recon.card G v ≃g Recon.card H w)
    (hn : ∀ x (hx : x ≠ v), G.Adj v x ↔ H.Adj w (e ⟨x, hx⟩).1) : Nonempty (G ≃g H) := by
  classical
  let f : V → W := fun x => if h : x = v then w else (e ⟨x, h⟩ : W)
  let g : W → V := fun y => if h : y = w then v else (e.symm ⟨y, h⟩ : V)
  have hf : ∀ x (h : ¬ x = v), f x = (e ⟨x, h⟩ : W) := fun x h => dite_eq_right h
  have hg : ∀ y (h : ¬ y = w), g y = (e.symm ⟨y, h⟩ : V) := fun y h => dite_eq_right h
  have hfv : f v = w := dite_eq_left rfl
  have hgw : g w = v := dite_eq_left rfl
  have hgf : ∀ x, g (f x) = x := by
    intro x
    by_cases h : x = v
    · subst h; rw [hfv, hgw]
    · have h2 : ¬ f x = w := by rw [hf x h]; exact (e ⟨x, h⟩).2
      rw [hg _ h2]
      have : (⟨f x, h2⟩ : ({w}ᶜ : Set W)) = e ⟨x, h⟩ := Subtype.ext (hf x h)
      rw [this, RelIso.symm_apply_apply]
  have hfg : ∀ y, f (g y) = y := by
    intro y
    by_cases h : y = w
    · subst h; rw [hgw, hfv]
    · have h2 : ¬ g y = v := by rw [hg y h]; exact (e.symm ⟨y, h⟩).2
      rw [hf _ h2]
      have : (⟨g y, h2⟩ : ({v}ᶜ : Set V)) = e.symm ⟨y, h⟩ := Subtype.ext (hg y h)
      rw [this, RelIso.apply_symm_apply]
  refine ⟨{ toEquiv := ⟨f, g, hgf, hfg⟩, map_rel_iff' := ?_ }⟩
  intro a b
  change H.Adj (f a) (f b) ↔ G.Adj a b
  by_cases ha : a = v
  · by_cases hb : b = v
    · rw [ha, hb, hfv]
      exact ⟨fun h => (H.loopless.irrefl _ h).elim, fun h => (G.loopless.irrefl _ h).elim⟩
    · rw [ha, hfv, hf b hb]
      exact (hn b hb).symm
  · by_cases hb : b = v
    · rw [hb, hfv, hf a ha]
      exact ⟨fun h => ((hn a ha).2 h.symm).symm, fun h => ((hn a ha).1 h.symm).symm⟩
    · rw [hf a ha, hf b hb]
      exact e.map_rel_iff (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)

def Pset {n : ℕ} {W : Type} (X : SimpleGraph (Fin n)) (F : SimpleGraph W) (a : ℕ) :
    Set (Fin n × Fin n) :=
  {p | p.1 ≠ p.2 ∧ Nonempty (X.induce ({p.1, p.2}ᶜ : Set (Fin n)) ≃g F) ∧
    (X.neighborSet p.1).ncard = a}

def Eset {n : ℕ} {W : Type} (X : SimpleGraph (Fin n)) (F : SimpleGraph W) (a : ℕ) :
    Set (Fin n × Fin n) :=
  {p | p ∈ Pset X F a ∧ X.Adj p.1 p.2}

def Mset {n : ℕ} {W : Type} (X : SimpleGraph (Fin n)) (F : SimpleGraph W) (a : ℕ) :
    Set (Fin n × Fin n) :=
  {p | p ∈ Pset X F a ∧ ¬ X.Adj p.1 p.2}

lemma p_eq_e_add_m {n : ℕ} {W : Type} (X : SimpleGraph (Fin n)) (F : SimpleGraph W) (a : ℕ) :
    (Pset X F a).ncard = (Eset X F a).ncard + (Mset X F a).ncard := by
  rw [← Set.ncard_union_eq]
  · congr 1
    ext p
    constructor
    · intro h
      by_cases hp : X.Adj p.1 p.2
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨h, hp⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  · rw [Set.disjoint_left]
    intro p h1 h2
    exact h2.2 h1.2

lemma swap_count {n : ℕ} {A B : Set (Fin n × Fin n)} (h1 : ∀ p ∈ A, p.swap ∈ B)
    (h2 : ∀ q ∈ B, q.swap ∈ A) : A.ncard = B.ncard :=
  Set.ncard_congr (fun p _ => p.swap) h1 (fun _ _ _ _ h => Prod.swap_injective h)
    (fun q hq => ⟨q.swap, h2 q hq, Prod.swap_swap q⟩)

lemma sym_facts {n : ℕ} {W : Type} (X : SimpleGraph (Fin n)) (F : SimpleGraph W) (s : ℕ)
    (hb1 : ∀ x z : Fin n, x ≠ z → Nonempty (X.induce ({x, z}ᶜ : Set (Fin n)) ≃g F) →
      X.Adj x z → (X.neighborSet x).ncard + (X.neighborSet z).ncard = s + 1)
    (hb0 : ∀ x z : Fin n, x ≠ z → Nonempty (X.induce ({x, z}ᶜ : Set (Fin n)) ≃g F) →
      ¬ X.Adj x z → (X.neighborSet x).ncard + (X.neighborSet z).ncard = s) :
    (∀ a ≤ s, (Eset X F (s - a)).ncard = (Eset X F (a + 1)).ncard) ∧
    (∀ a ≤ s, (Mset X F a).ncard = (Mset X F (s - a)).ncard) ∧
    (∀ a, s < a → (Mset X F a).ncard = 0) := by
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · apply swap_count
    · rintro ⟨x, z⟩ ⟨⟨hne, hiso, hd⟩, hadj⟩
      have := hb1 x z hne hiso hadj
      refine ⟨⟨Ne.symm hne, ?_, ?_⟩, hadj.symm⟩
      · change Nonempty (X.induce ({z, x}ᶜ : Set (Fin n)) ≃g F)
        rw [Set.pair_comm]; exact hiso
      · change (X.neighborSet z).ncard = a + 1
        change (X.neighborSet x).ncard = s - a at hd
        omega
    · rintro ⟨x, z⟩ ⟨⟨hne, hiso, hd⟩, hadj⟩
      have := hb1 x z hne hiso hadj
      refine ⟨⟨Ne.symm hne, ?_, ?_⟩, hadj.symm⟩
      · change Nonempty (X.induce ({z, x}ᶜ : Set (Fin n)) ≃g F)
        rw [Set.pair_comm]; exact hiso
      · change (X.neighborSet z).ncard = s - a
        change (X.neighborSet x).ncard = a + 1 at hd
        omega
  · apply swap_count
    · rintro ⟨x, z⟩ ⟨⟨hne, hiso, hd⟩, hadj⟩
      have := hb0 x z hne hiso hadj
      refine ⟨⟨Ne.symm hne, ?_, ?_⟩, fun h => hadj h.symm⟩
      · change Nonempty (X.induce ({z, x}ᶜ : Set (Fin n)) ≃g F)
        rw [Set.pair_comm]; exact hiso
      · change (X.neighborSet z).ncard = s - a
        change (X.neighborSet x).ncard = a at hd
        omega
    · rintro ⟨x, z⟩ ⟨⟨hne, hiso, hd⟩, hadj⟩
      have := hb0 x z hne hiso hadj
      refine ⟨⟨Ne.symm hne, ?_, ?_⟩, fun h => hadj h.symm⟩
      · change Nonempty (X.induce ({z, x}ᶜ : Set (Fin n)) ≃g F)
        rw [Set.pair_comm]; exact hiso
      · change (X.neighborSet z).ncard = a
        change (X.neighborSet x).ncard = s - a at hd
        omega
  · rw [Set.ncard_eq_zero]
    apply Set.eq_empty_of_forall_notMem
    rintro ⟨x, z⟩ ⟨⟨hne, hiso, hd⟩, hadj⟩
    have := hb0 x z hne hiso hadj
    change (X.neighborSet x).ncard = a at hd
    omega

lemma arith (s : ℕ) (pG pH eG eH mG mH : ℕ → ℕ) (hp : ∀ a, pG a = pH a)
    (hG : ∀ a, pG a = eG a + mG a) (hH : ∀ a, pH a = eH a + mH a)
    (heG : ∀ a ≤ s, eG (s - a) = eG (a + 1)) (heH : ∀ a ≤ s, eH (s - a) = eH (a + 1))
    (hmG : ∀ a ≤ s, mG a = mG (s - a)) (hmH : ∀ a ≤ s, mH a = mH (s - a))
    (hm0G : ∀ a, s < a → mG a = 0) (hm0H : ∀ a, s < a → mH a = 0) :
    ∀ a, eG a = eH a := by
  have big : ∀ a, s < a → eG a = eH a := fun a ha => by
    have := hp a; have := hG a; have := hH a; have := hm0G a ha; have := hm0H a ha
    omega
  have step : ∀ k a, a + k = s + 1 → eG a = eH a := by
    intro k
    induction k with
    | zero => intro a ha; exact big a (by omega)
    | succ k ih =>
      intro a ha
      have h1 := ih (a + 1) (by omega)
      have := hp a; have := hp (s - a); have := hG a; have := hH a
      have := hG (s - a); have := hH (s - a)
      have := heG a (by omega); have := heH a (by omega)
      have := hmG a (by omega); have := hmH a (by omega)
      omega
  intro a
  by_cases h : s < a
  · exact big a h
  · exact step (s + 1 - a) a (by omega)

lemma pi_eq {n : ℕ} (G H : SimpleGraph (Fin n)) (σ : Fin n ≃ Fin n)
    (f : ∀ x, G.induce ({x}ᶜ : Set (Fin n)) ≃g H.induce ({σ x}ᶜ : Set (Fin n)))
    (hdeg : ∀ x, (G.neighborSet x).ncard = (H.neighborSet (σ x)).ncard)
    {W : Type} (F : SimpleGraph W) (a : ℕ) :
    (Pset G F a).ncard = (Pset H F a).ncard := by
  refine Set.ncard_congr (fun p hp => (σ p.1, (f p.1 ⟨p.2, fun h => hp.1 h.symm⟩).1))
    ?_ ?_ ?_
  · rintro ⟨x, z⟩ ⟨hne, ⟨hiso⟩, hd⟩
    refine ⟨fun h => (f x ⟨z, fun h => hne h.symm⟩).2 h.symm,
      ⟨(restrictIso (f x) z (fun h => hne h.symm)).symm.trans hiso⟩, ?_⟩
    change (H.neighborSet (σ x)).ncard = a
    rw [← hdeg x]; exact hd
  · rintro ⟨x, z⟩ ⟨x', z'⟩ hp hq h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hx := σ.injective h1
    subst hx
    have := (f x).injective (Subtype.ext h2)
    simp only [Subtype.mk.injEq] at this
    rw [this]
  · rintro ⟨x', w⟩ ⟨hne, ⟨hiso⟩, hd⟩
    obtain ⟨x, rfl⟩ := σ.surjective x'
    have hw : w ∈ ({σ x}ᶜ : Set (Fin n)) := fun h => hne h.symm
    obtain ⟨⟨z, hz⟩, hzw⟩ : ∃ z', f x z' = ⟨w, hw⟩ := ⟨_, (f x).apply_symm_apply _⟩
    have hw' : (f x ⟨z, hz⟩).1 = w := by rw [hzw]
    have e1 := restrictIso (f x) z hz
    rw [hw'] at e1
    refine ⟨(x, z), ⟨fun h => hz h.symm, ⟨e1.trans hiso⟩, ?_⟩, ?_⟩
    · change (G.neighborSet x).ncard = a
      rw [hdeg x]; exact hd
    · exact Prod.ext rfl hw'

open Classical in
lemma hbit {n : ℕ} {W : Type} (X : SimpleGraph (Fin n)) (F : SimpleGraph W) (s : ℕ)
    (hs : X.edgeSet.ncard = s + F.edgeSet.ncard) (x z : Fin n) (hne : x ≠ z)
    (hiso : Nonempty (X.induce ({x, z}ᶜ : Set (Fin n)) ≃g F)) :
    (X.Adj x z → (X.neighborSet x).ncard + (X.neighborSet z).ncard = s + 1) ∧
    (¬ X.Adj x z → (X.neighborSet x).ncard + (X.neighborSet z).ncard = s) := by
  have h1 := bit_law X x z (Ne.symm hne)
  have h2 := ncard_iso hiso.some
  constructor
  · intro h
    rw [ite_eq_left h] at h1
    omega
  · intro h
    rw [ite_eq_right h] at h1
    omega

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class := by
  open Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class in
  intro n hn G ⟨u, hpure⟩ H ⟨σ, hσ⟩
  have hE := Recon.Checked.L_kelly_edge_count n hn G H ⟨σ, hσ⟩
  let f : ∀ x, G.induce ({x}ᶜ : Set (Fin n)) ≃g H.induce ({σ x}ᶜ : Set (Fin n)) :=
    fun x => (hσ x).some
  have hdeg : ∀ x, (G.neighborSet x).ncard = (H.neighborSet (σ x)).ncard := fun x => by
    have h1 := card_add_deg G x
    have h2 := card_add_deg H (σ x)
    have h3 := ncard_iso (f x)
    omega
  have key : ∀ y (hy : y ≠ u), G.Adj u y ↔ H.Adj (σ u) (f u ⟨y, hy⟩).1 := by
    intro y hy
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
        exact hnadj ((hpure u y x z rfl hd hy.symm hne ⟨hiso.symm⟩).1 hadj)
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
        exact hadj ((hpure u y x z rfl hd hy.symm hne ⟨hiso.symm⟩).2 hxz)
      have hEH : (Eset H (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard).ncard = 0 := by
        omega
      refine ⟨fun h => (hadj h).elim, fun h => ?_⟩
      rw [Set.ncard_eq_zero] at hEH
      have : (σ u, (f u ⟨y, hy⟩).1) ∈
          Eset H (G.induce ({u, y}ᶜ : Set (Fin n))) (G.neighborSet u).ncard := ⟨hmem, h⟩
      rw [hEH] at this
      exact this.elim
  exact iso_of_nbhd (f u) key
