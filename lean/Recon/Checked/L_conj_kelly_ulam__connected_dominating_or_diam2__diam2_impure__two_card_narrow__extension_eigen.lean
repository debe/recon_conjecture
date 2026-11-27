import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen
import Recon.Checked.L_kelly_edge_count
import Recon.Checked.L_kelly_card_edges_add_degree
import Recon.Checked.L_kelly_degree_sequence
import Recon.Checked.L_found_hypomorphic_iso_invariant
import Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class

namespace Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen

open SimpleGraph Classical

noncomputable def dgN {n : ℕ} (K : SimpleGraph (Fin n)) (x : Fin n) : ℕ := (K.neighborSet x).ncard

noncomputable def chi {n : ℕ} (d : ℕ) (K : SimpleGraph (Fin n)) (y : Fin n) : ℤ :=
  if dgN K y = d + 1 then 1 else 0

noncomputable def AK {n : ℕ} (K : SimpleGraph (Fin n)) (f : Fin n → ℤ) (x : Fin n) : ℤ :=
  ∑ y, if K.Adj x y then f y else 0

noncomputable def zz {n : ℕ} (A B : SimpleGraph (Fin n)) (u y : Fin n) : ℤ :=
  (if A.Adj u y then 1 else 0) - (if B.Adj u y then 1 else 0)

lemma ncard_eq_sum {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ((Set.ncard {y | p y} : ℕ) : ℤ) = ∑ y, if p y then (1:ℤ) else 0 := by
  rw [Set.ncard_eq_toFinset_card', Finset.sum_boole]
  simp

lemma deg_sum {n : ℕ} (K : SimpleGraph (Fin n)) (x : Fin n) :
    (dgN K x : ℤ) = ∑ y, if K.Adj x y then (1:ℤ) else 0 := ncard_eq_sum (K.Adj x)

lemma deg_pres {n : ℕ} (hn : 3 ≤ n) {G K : SimpleGraph (Fin n)} (σ : Fin n ≃ Fin n)
    (hσ : ∀ x, Nonempty (Recon.card G x ≃g Recon.card K (σ x))) (x : Fin n) :
    dgN K (σ x) = dgN G x := by
  have hE := Recon.Checked.L_kelly_edge_count n hn G K ⟨σ, hσ⟩
  have h1 := Recon.Checked.L_kelly_card_edges_add_degree n G x
  have h2 := Recon.Checked.L_kelly_card_edges_add_degree n K (σ x)
  have h3 := Recon.Checked.L_kelly_degree_sequence.ncard_eq_of_iso (hσ x).some
  unfold dgN; omega

lemma a0 {n d : ℕ} (hn : 3 ≤ n) {G K : SimpleGraph (Fin n)}
    (hdeg : ∀ x : Fin n, dgN G x = d ∨ dgN G x = d + 1) (hK : Recon.Hypomorphic G K)
    (y : Fin n) : dgN K y = d ∨ dgN K y = d + 1 := by
  obtain ⟨σ, hσ⟩ := hK
  have := deg_pres hn σ hσ (σ.symm y)
  rw [Equiv.apply_symm_apply] at this
  rw [this]; exact hdeg _

lemma card_back {n : ℕ} {G K : SimpleGraph (Fin n)} (σ : Fin n ≃ Fin n)
    (hσ : ∀ x, Nonempty (Recon.card G x ≃g Recon.card K (σ x))) (v : Fin n) :
    Nonempty (Recon.card K v ≃g Recon.card G (σ.symm v)) := by
  have h := hσ (σ.symm v)
  rw [Equiv.apply_symm_apply] at h
  exact ⟨h.some.symm⟩

lemma nbr_iso {V W : Type*} {A : SimpleGraph V} {B : SimpleGraph W} (e : A ≃g B) (v : V) :
    (B.neighborSet (e v)).ncard = (A.neighborSet v).ncard := by
  have : B.neighborSet (e v) = e '' A.neighborSet v := by
    ext w
    simp only [mem_neighborSet, Set.mem_image]
    constructor
    · intro h
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      rw [← e.map_rel_iff, e.apply_symm_apply]; exact h
    · rintro ⟨y, hy, rfl⟩; exact e.map_rel_iff.2 hy
  rw [this, Set.ncard_image_of_injective _ e.injective]

lemma cnt_iso {V W : Type*} {A : SimpleGraph V} {B : SimpleGraph W} (e : A ≃g B) (t : ℕ) :
    Set.ncard {v : V | (A.neighborSet v).ncard = t} =
      Set.ncard {w : W | (B.neighborSet w).ncard = t} := by
  have : {w : W | (B.neighborSet w).ncard = t} = e '' {v : V | (A.neighborSet v).ncard = t} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      rw [← nbr_iso e, e.apply_symm_apply]; exact h
    · rintro ⟨v, hv, rfl⟩
      rw [nbr_iso e]; exact hv
  rw [this, Set.ncard_image_of_injective _ e.injective]

noncomputable def cnt {n : ℕ} (d : ℕ) (X : SimpleGraph (Fin n)) (x : Fin n) : ℕ :=
  Set.ncard {v : ({x}ᶜ : Set (Fin n)) |
    ((X.induce ({x}ᶜ : Set (Fin n))).neighborSet v).ncard = d + 1}

lemma cnt_eq {n d : ℕ} (X : SimpleGraph (Fin n)) (hX : ∀ v, dgN X v ≤ d + 1) (x : Fin n) :
    cnt d X x = Set.ncard {v : Fin n | v ≠ x ∧ ¬ X.Adj x v ∧ dgN X v = d + 1} := by
  unfold cnt
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨w, hw⟩, h, rfl⟩
    have hw' : w ≠ x := hw
    have h' : ((X.induce ({x}ᶜ : Set (Fin n))).neighborSet ⟨w, hw⟩).ncard = d + 1 := h
    show w ≠ x ∧ ¬ X.Adj x w ∧ dgN X w = d + 1
    have key := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class.deg_in_card X x w hw'
    have hb := hX w
    unfold dgN at hb
    by_cases hA : X.Adj x w
    · rw [if_pos hA] at key; omega
    · rw [if_neg hA] at key
      exact ⟨hw', hA, by unfold dgN; omega⟩
  · rintro ⟨hv, hA, hd⟩
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    have key := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class.deg_in_card X x v hv
    rw [if_neg hA] at key
    unfold dgN at hd
    show _ = _
    omega


lemma a1_ident {n d : ℕ} (X : SimpleGraph (Fin n)) (x : Fin n) :
    ∑ y, chi d X y = chi d X x + AK X (chi d X) x +
      ∑ y, (if (y ≠ x ∧ ¬ X.Adj x y ∧ dgN X y = d + 1) then (1:ℤ) else 0) := by
  have h : ∀ y, chi d X y = ((if y = x then chi d X y else 0) +
      (if X.Adj x y then chi d X y else 0)) +
      (if (y ≠ x ∧ ¬ X.Adj x y ∧ dgN X y = d + 1) then (1:ℤ) else 0) := by
    intro y
    by_cases hy : y = x
    · subst hy; simp
    · by_cases ha : X.Adj x y
      · simp [hy, ha]
      · simp only [hy, ha, chi]; split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun y _ => h y), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq']
  simp [AK]

noncomputable def Ct {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) (t : ℕ) : ℤ :=
  if h : ∃ w, dgN G w = t then (cnt d G h.choose : ℤ) else 0

lemma cS_K {n d : ℕ} (hn : 3 ≤ n) {G K : SimpleGraph (Fin n)}
    (hdeg : ∀ x : Fin n, dgN G x = d ∨ dgN G x = d + 1)
    (hNF : ∀ x y : Fin n, (G.neighborSet x).ncard = (G.neighborSet y).ncard →
      Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({y}ᶜ : Set (Fin n))))
    (hK : Recon.Hypomorphic G K) (x : Fin n) :
    ∑ y, (if (y ≠ x ∧ ¬ K.Adj x y ∧ dgN K y = d + 1) then (1:ℤ) else 0) = Ct d G (dgN K x) := by
  have hK' := hK
  obtain ⟨σ, hσ⟩ := hK'
  have hX : ∀ v, dgN K v ≤ d + 1 := fun v => by rcases a0 hn hdeg hK v with h | h <;> omega
  rw [← ncard_eq_sum (fun y => y ≠ x ∧ ¬ K.Adj x y ∧ dgN K y = d + 1), ← cnt_eq K hX x]
  obtain ⟨e⟩ := card_back σ hσ x
  have h1 : cnt d K x = cnt d G (σ.symm x) := cnt_iso e (d + 1)
  have h2 : dgN K x = dgN G (σ.symm x) := by
    have := deg_pres hn σ hσ (σ.symm x)
    rwa [Equiv.apply_symm_apply] at this
  have hex : ∃ w, dgN G w = dgN K x := ⟨σ.symm x, h2.symm⟩
  unfold Ct
  rw [dif_pos hex]
  have hc := hex.choose_spec
  obtain ⟨e2⟩ := hNF (σ.symm x) hex.choose (h2.symm.trans hc.symm)
  have h3 : cnt d G (σ.symm x) = cnt d G hex.choose := cnt_iso e2 (d + 1)
  rw [h1, h3]

lemma Q_eq {n d : ℕ} (hn : 3 ≤ n) {G K : SimpleGraph (Fin n)} (hK : Recon.Hypomorphic G K) :
    ∑ y, chi d K y = ∑ y, chi d G y := by
  obtain ⟨σ, hσ⟩ := hK
  rw [← Equiv.sum_comp σ]
  apply Finset.sum_congr rfl
  intro y _
  unfold chi
  rw [deg_pres hn σ hσ y]

lemma h_form {n d : ℕ} (hn : 3 ≤ n) {G K : SimpleGraph (Fin n)}
    (hdeg : ∀ x : Fin n, dgN G x = d ∨ dgN G x = d + 1)
    (hNF : ∀ x y : Fin n, (G.neighborSet x).ncard = (G.neighborSet y).ncard →
      Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({y}ᶜ : Set (Fin n))))
    (hK : Recon.Hypomorphic G K) (x : Fin n) :
    AK K (chi d K) x = ∑ y, chi d G y - chi d K x - Ct d G (dgN K x) := by
  have h1 := a1_ident (d := d) K x
  rw [cS_K hn hdeg hNF hK x, Q_eq hn hK] at h1
  linarith

lemma h_diff {n d : ℕ} (hn : 3 ≤ n) {G K₁ K₂ : SimpleGraph (Fin n)}
    (hdeg : ∀ x : Fin n, dgN G x = d ∨ dgN G x = d + 1)
    (hNF : ∀ x y : Fin n, (G.neighborSet x).ncard = (G.neighborSet y).ncard →
      Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({y}ᶜ : Set (Fin n))))
    (h1 : Recon.Hypomorphic G K₁) (h2 : Recon.Hypomorphic G K₂) (x : Fin n) :
    AK K₁ (chi d K₁) x - AK K₂ (chi d K₂) x =
      (Ct d G d - Ct d G (d + 1) - 1) * (chi d K₁ x - chi d K₂ x) := by
  rw [h_form hn hdeg hNF h1, h_form hn hdeg hNF h2]
  rcases a0 hn hdeg h1 x with e1 | e1 <;> rcases a0 hn hdeg h2 x with e2 | e2 <;>
    simp [chi, e1, e2] <;> ring


lemma induce_eq {n : ℕ} {A B : SimpleGraph (Fin n)} {u : Fin n}
    (hag : ∀ x y, x ≠ u → y ≠ u → (A.Adj x y ↔ B.Adj x y)) :
    A.induce ({u}ᶜ : Set (Fin n)) = B.induce ({u}ᶜ : Set (Fin n)) := by
  ext a b
  exact hag a.1 b.1 a.2 b.2

lemma deg_u {n : ℕ} (hn : 3 ≤ n) {G A B : SimpleGraph (Fin n)}
    (hA : Recon.Hypomorphic G A) (hB : Recon.Hypomorphic G B) {u : Fin n}
    (hag : ∀ x y, x ≠ u → y ≠ u → (A.Adj x y ↔ B.Adj x y)) : dgN A u = dgN B u := by
  have e1 := Recon.Checked.L_kelly_edge_count n hn G A hA
  have e2 := Recon.Checked.L_kelly_edge_count n hn G B hB
  have h1 := Recon.Checked.L_kelly_card_edges_add_degree n A u
  have h2 := Recon.Checked.L_kelly_card_edges_add_degree n B u
  have h3 : (Recon.card A u).edgeSet.ncard = (Recon.card B u).edgeSet.ncard := by
    unfold Recon.card; rw [induce_eq hag]
  unfold dgN; omega

lemma zz_self {n : ℕ} (A B : SimpleGraph (Fin n)) (u : Fin n) : zz A B u u = 0 := by
  simp [zz]

lemma a2a {n : ℕ} (hn : 3 ≤ n) {G A B : SimpleGraph (Fin n)}
    (hA : Recon.Hypomorphic G A) (hB : Recon.Hypomorphic G B) {u : Fin n}
    (hag : ∀ x y, x ≠ u → y ≠ u → (A.Adj x y ↔ B.Adj x y)) (x : Fin n) :
    (dgN A x : ℤ) = dgN B x + zz A B u x := by
  by_cases hx : x = u
  · subst hx; rw [zz_self, deg_u hn hA hB hag]; ring
  · rw [deg_sum, deg_sum]
    have : ∑ y, ((if A.Adj x y then (1:ℤ) else 0) - (if B.Adj x y then 1 else 0)) =
        zz A B u x := by
      rw [Finset.sum_eq_single u]
      · unfold zz; rw [A.adj_comm, B.adj_comm]
      · intro y _ hy; simp [hag x y hx hy]
      · simp
    rw [Finset.sum_sub_distrib] at this; linarith

lemma z_chi {n d : ℕ} (hn : 3 ≤ n) {G A B : SimpleGraph (Fin n)}
    (hdeg : ∀ x : Fin n, dgN G x = d ∨ dgN G x = d + 1)
    (hA : Recon.Hypomorphic G A) (hB : Recon.Hypomorphic G B) {u : Fin n}
    (hag : ∀ x y, x ≠ u → y ≠ u → (A.Adj x y ↔ B.Adj x y)) (y : Fin n) :
    zz A B u y = chi d A y - chi d B y := by
  have h := a2a hn hA hB hag y
  rcases a0 hn hdeg hA y with e1 | e1 <;> rcases a0 hn hdeg hB y with e2 | e2 <;>
    simp [chi, e1, e2] at h ⊢ <;> linarith

lemma AK_sub {n : ℕ} (K : SimpleGraph (Fin n)) (f g : Fin n → ℤ) (x : Fin n) :
    AK K (fun y => f y - g y) x = AK K f x - AK K g x := by
  unfold AK
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro y _; split_ifs <;> ring

lemma AK_lin {n : ℕ} (K : SimpleGraph (Fin n)) (a b : ℤ) (f g : Fin n → ℤ) (x : Fin n) :
    AK K (fun y => a * f y - b * g y) x = a * AK K f x - b * AK K g x := by
  unfold AK
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro y _; split_ifs <;> ring

lemma a2c {n d : ℕ} (hn : 3 ≤ n) {G A B : SimpleGraph (Fin n)}
    (hdeg : ∀ x : Fin n, dgN G x = d ∨ dgN G x = d + 1)
    (hNF : ∀ x y : Fin n, (G.neighborSet x).ncard = (G.neighborSet y).ncard →
      Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({y}ᶜ : Set (Fin n))))
    (hA : Recon.Hypomorphic G A) (hB : Recon.Hypomorphic G B) {u : Fin n}
    (hag : ∀ x y, x ≠ u → y ≠ u → (A.Adj x y ↔ B.Adj x y)) (x : Fin n) (hx : x ≠ u) :
    AK A (zz A B u) x = ((Ct d G d - Ct d G (d + 1) - 1) - chi d A u) * zz A B u x := by
  have e1 : AK A (zz A B u) x = AK A (chi d A) x - AK A (chi d B) x := by
    rw [← AK_sub]
    unfold AK
    apply Finset.sum_congr rfl; intro y _; rw [z_chi hn hdeg hA hB hag y]
  have e2 : AK A (chi d B) x - AK B (chi d B) x = zz A B u x * chi d B u := by
    unfold AK
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single u]
    · unfold zz; rw [A.adj_comm, B.adj_comm]; split_ifs <;> ring
    · intro y _ hy; simp [hag x y hx hy]
    · simp
  have e3 : chi d B u = chi d A u := by unfold chi; rw [deg_u hn hA hB hag]
  have e4 := h_diff hn hdeg hNF hA hB x
  have e5 := z_chi hn hdeg hA hB hag x
  rw [e3] at e2
  rw [e1]
  linear_combination e4 - e2 - (Ct d G d - Ct d G (d + 1) - 1) * e5


noncomputable def reat {n : ℕ} (K X : SimpleGraph (Fin n)) (u x : Fin n)
    (e : Recon.card K u ≃g Recon.card X x) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b => (a ≠ u ∧ b ≠ u ∧ K.Adj a b) ∨
    (a = u ∧ ∃ hb : b ≠ u, X.Adj x (e ⟨b, hb⟩).1))

lemma reat_off {n : ℕ} (K X : SimpleGraph (Fin n)) (u x : Fin n)
    (e : Recon.card K u ≃g Recon.card X x) (a b : Fin n) (ha : a ≠ u) (hb : b ≠ u) :
    (reat K X u x e).Adj a b ↔ K.Adj a b := by
  unfold reat
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · rcases h with ⟨_, _, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h ha
    · rcases h with ⟨_, _, h⟩ | ⟨h, _⟩
      · exact h.symm
      · exact absurd h hb
  · intro h
    exact ⟨K.ne_of_adj h, Or.inl (Or.inl ⟨ha, hb, h⟩)⟩

lemma reat_u {n : ℕ} (K X : SimpleGraph (Fin n)) (u x : Fin n)
    (e : Recon.card K u ≃g Recon.card X x) (b : Fin n) (hb : b ≠ u) :
    (reat K X u x e).Adj u b ↔ X.Adj x (e ⟨b, hb⟩).1 := by
  unfold reat
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · rcases h with ⟨h, _, _⟩ | ⟨_, hb', h⟩
      · exact absurd rfl h
      · exact h
    · rcases h with ⟨_, h, _⟩ | ⟨h, _⟩
      · exact absurd rfl h
      · exact absurd h hb
  · intro h
    exact ⟨fun h' => hb h'.symm, Or.inl (Or.inr ⟨rfl, hb, h⟩)⟩

lemma reat_iso {n : ℕ} (K X : SimpleGraph (Fin n)) (u x : Fin n)
    (e : Recon.card K u ≃g Recon.card X x) : Nonempty (reat K X u x e ≃g X) := by
  let i : Recon.card (reat K X u x e) u ≃g Recon.card K u :=
    { toEquiv := Equiv.refl _,
      map_rel_iff' := fun {a b} => (reat_off K X u x e a.1 b.1 a.2 b.2).symm }
  exact Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class.iso_of_nbhd
    (i.trans e) (fun y hy => reat_u K X u x e y hy)

lemma a3 {n : ℕ} {G H K : SimpleGraph (Fin n)} (hGH : Recon.Hypomorphic G H)
    (hni : ¬ Nonempty (G ≃g H)) (hK : Recon.Hypomorphic G K) (u : Fin n) :
    ∃ K' : SimpleGraph (Fin n), Recon.Hypomorphic G K' ∧
      (∀ x y : Fin n, x ≠ u → y ≠ u → (K.Adj x y ↔ K'.Adj x y)) ∧ K' ≠ K := by
  obtain ⟨σ, hσ⟩ := hK
  obtain ⟨eG⟩ := card_back σ hσ u
  obtain ⟨τ, hτ⟩ := hGH
  obtain ⟨f⟩ := hτ (σ.symm u)
  let eH := eG.trans f
  obtain ⟨iG⟩ := reat_iso K G u _ eG
  obtain ⟨iH⟩ := reat_iso K H u _ eH
  have hypG : Recon.Hypomorphic G (reat K G u _ eG) :=
    Recon.Checked.L_found_hypomorphic_iso_invariant n G G G _ ⟨Iso.refl⟩ ⟨iG.symm⟩
      (Recon.anchor_hypomorphic_refl G)
  have hypH : Recon.Hypomorphic G (reat K H u _ eH) :=
    Recon.Checked.L_found_hypomorphic_iso_invariant n G G H _ ⟨Iso.refl⟩ ⟨iH.symm⟩ ⟨τ, hτ⟩
  by_cases h1 : reat K G u _ eG = K
  · refine ⟨reat K H u _ eH, hypH, fun a b ha hb => (reat_off K H u _ eH a b ha hb).symm, ?_⟩
    intro h2
    apply hni
    have h3 : reat K H u _ eH = reat K G u _ eG := h2.trans h1.symm
    exact ⟨iG.symm.trans (h3 ▸ iH : reat K G u _ eG ≃g H)⟩
  · exact ⟨reat K G u _ eG, hypG, fun a b ha hb => (reat_off K G u _ eG a b ha hb).symm, h1⟩


noncomputable def lossL {n : ℕ} (A B : SimpleGraph (Fin n)) (u : Fin n) : ℤ :=
  ∑ y, if A.Adj u y ∧ ¬ B.Adj u y then (1:ℤ) else 0

noncomputable def gainL {n : ℕ} (A B : SimpleGraph (Fin n)) (u : Fin n) : ℤ :=
  ∑ y, if ¬ A.Adj u y ∧ B.Adj u y then (1:ℤ) else 0

lemma AK_u {n : ℕ} (A B : SimpleGraph (Fin n)) (u : Fin n) :
    AK A (zz A B u) u = lossL A B u := by
  unfold AK lossL zz
  apply Finset.sum_congr rfl; intro y _
  by_cases h1 : A.Adj u y <;> by_cases h2 : B.Adj u y <;> simp [h1, h2]

lemma gain_eq {n : ℕ} (hn : 3 ≤ n) {G A B : SimpleGraph (Fin n)}
    (hA : Recon.Hypomorphic G A) (hB : Recon.Hypomorphic G B) {u : Fin n}
    (hag : ∀ x y, x ≠ u → y ≠ u → (A.Adj x y ↔ B.Adj x y)) : gainL A B u = lossL A B u := by
  have h := deg_u hn hA hB hag
  have h1 := deg_sum A u
  have h2 := deg_sum B u
  have h3 : (∑ y, if A.Adj u y then (1:ℤ) else 0) - (∑ y, if B.Adj u y then (1:ℤ) else 0) =
      lossL A B u - gainL A B u := by
    unfold lossL gainL
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro y _
    by_cases h1 : A.Adj u y <;> by_cases h2 : B.Adj u y <;> simp [h1, h2]
  rw [h] at h1
  linarith

lemma loss_pos {n : ℕ} (hn : 3 ≤ n) {G A B : SimpleGraph (Fin n)}
    (hA : Recon.Hypomorphic G A) (hB : Recon.Hypomorphic G B) {u : Fin n}
    (hag : ∀ x y, x ≠ u → y ≠ u → (A.Adj x y ↔ B.Adj x y)) (hne : B ≠ A) :
    0 < lossL A B u := by
  have hg := gain_eq hn hA hB hag
  have nn1 : 0 ≤ lossL A B u := Finset.sum_nonneg (fun y _ => by split_ifs <;> norm_num)
  by_contra hc
  have h0 : lossL A B u = 0 := by omega
  have h0' : gainL A B u = 0 := by omega
  have t1 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by split_ifs <;> norm_num)).1 h0
  have t2 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by split_ifs <;> norm_num)).1 h0'
  have key : ∀ y, A.Adj u y ↔ B.Adj u y := by
    intro y
    have a1 := t1 y (Finset.mem_univ y)
    have a2 := t2 y (Finset.mem_univ y)
    by_cases h1 : A.Adj u y <;> by_cases h2 : B.Adj u y <;> simp_all
  apply hne
  ext a b
  by_cases ha : a = u
  · subst ha; exact (key b).symm
  · by_cases hb : b = u
    · subst hb; rw [A.adj_comm, B.adj_comm]; exact (key a).symm
    · exact (hag a b ha hb).symm

lemma AK_sym {n : ℕ} (K : SimpleGraph (Fin n)) (f g : Fin n → ℤ) :
    ∑ x, f x * AK K g x = ∑ x, AK K f x * g x := by
  unfold AK
  simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _
  rw [K.adj_comm]

lemma AK_z {n d : ℕ} (hn : 3 ≤ n) {G A B : SimpleGraph (Fin n)}
    (hdeg : ∀ x : Fin n, dgN G x = d ∨ dgN G x = d + 1)
    (hNF : ∀ x y : Fin n, (G.neighborSet x).ncard = (G.neighborSet y).ncard →
      Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({y}ᶜ : Set (Fin n))))
    (hA : Recon.Hypomorphic G A) (hB : Recon.Hypomorphic G B) {u : Fin n}
    (hag : ∀ x y, x ≠ u → y ≠ u → (A.Adj x y ↔ B.Adj x y)) (x : Fin n) :
    AK A (zz A B u) x = ((Ct d G d - Ct d G (d + 1) - 1) - chi d A u) * zz A B u x +
      (if x = u then lossL A B u else 0) := by
  by_cases hx : x = u
  · subst hx; rw [AK_u, zz_self]; simp
  · rw [a2c hn hdeg hNF hA hB hag x hx, if_neg hx]; ring

lemma a4 {n d : ℕ} (hn : 3 ≤ n) {G H K : SimpleGraph (Fin n)}
    (hdeg : ∀ x : Fin n, dgN G x = d ∨ dgN G x = d + 1)
    (hNF : ∀ x y : Fin n, (G.neighborSet x).ncard = (G.neighborSet y).ncard →
      Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({y}ᶜ : Set (Fin n))))
    (hGH : Recon.Hypomorphic G H) (hni : ¬ Nonempty (G ≃g H))
    (hK : Recon.Hypomorphic G K) (f : Fin n → ℤ) (s : ℤ)
    (hf : ∀ x, AK K f x = ((Ct d G d - Ct d G (d + 1) - 1) - s) * f x)
    (v : Fin n) (hv : chi d K v = s) : f v = 0 := by
  obtain ⟨K', hK', hag, hne⟩ := a3 hGH hni hK v
  have hz := AK_z hn hdeg hNF hK hK' hag
  have hL := loss_pos hn hK hK' hag hne
  have hs := AK_sym K f (zz K K' v)
  simp only [hz, hf, hv, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  have : f v * lossL K K' v = 0 := by
    have e : ∑ x, f x * (((Ct d G d - Ct d G (d + 1) - 1) - s) * zz K K' v x) =
        ∑ x, ((Ct d G d - Ct d G (d + 1) - 1) - s) * f x * zz K K' v x := by
      apply Finset.sum_congr rfl; intro x _; ring
    linarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · omega


lemma a5 {n d : ℕ} (hn : 3 ≤ n) {G H K K₁ K₂ : SimpleGraph (Fin n)}
    (hdeg : ∀ x : Fin n, dgN G x = d ∨ dgN G x = d + 1)
    (hNF : ∀ x y : Fin n, (G.neighborSet x).ncard = (G.neighborSet y).ncard →
      Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({y}ᶜ : Set (Fin n))))
    (hGH : Recon.Hypomorphic G H) (hni : ¬ Nonempty (G ≃g H))
    (hK : Recon.Hypomorphic G K) (hK1 : Recon.Hypomorphic G K₁) (hK2 : Recon.Hypomorphic G K₂)
    {u : Fin n}
    (hag1 : ∀ x y, x ≠ u → y ≠ u → (K.Adj x y ↔ K₁.Adj x y))
    (hag2 : ∀ x y, x ≠ u → y ≠ u → (K.Adj x y ↔ K₂.Adj x y))
    (hne1 : K₁ ≠ K) (hne2 : K₂ ≠ K) :
    lossL K K₁ u = lossL K K₂ u ∧ ∀ x, dgN K x = dgN K u → (K₁.Adj u x ↔ K₂.Adj u x) := by
  have hz1 := AK_z hn hdeg hNF hK hK1 hag1
  have hz2 := AK_z hn hdeg hNF hK hK2 hag2
  have k1p := loss_pos hn hK hK1 hag1 hne1
  have k2p := loss_pos hn hK hK2 hag2 hne2
  have hf : ∀ x, AK K (fun y => lossL K K₂ u * zz K K₁ u y - lossL K K₁ u * zz K K₂ u y) x =
      ((Ct d G d - Ct d G (d + 1) - 1) - chi d K u) *
        (fun y => lossL K K₂ u * zz K K₁ u y - lossL K K₁ u * zz K K₂ u y) x := by
    intro x; rw [AK_lin, hz1, hz2]; split_ifs <;> ring
  have h0 := fun v hv => a4 hn hdeg hNF hGH hni hK _ _ hf v hv
  have hkey : lossL K K₁ u = lossL K K₂ u := by
    rcases a0 hn hdeg hK u with hu | hu
    · have hg := gain_eq hn hK hK1 hag1
      obtain ⟨x0, hx0⟩ : ∃ x0, ¬ K.Adj u x0 ∧ K₁.Adj u x0 := by
        by_contra hc
        have : gainL K K₁ u = 0 :=
          Finset.sum_eq_zero (fun y _ => if_neg (fun h => hc ⟨y, h⟩))
        omega
      have hd := a2a hn hK hK1 hag1 x0
      have hz : zz K K₁ u x0 = -1 := by simp [zz, hx0.1, hx0.2]
      rw [hz] at hd
      have hdx : dgN K x0 = d := by
        rcases a0 hn hdeg hK x0 with e | e <;> rcases a0 hn hdeg hK1 x0 with e' | e' <;> omega
      have hc : chi d K x0 = chi d K u := by unfold chi; rw [hdx, hu]
      have := h0 x0 hc
      rw [hz] at this
      by_cases h2 : K₂.Adj u x0
      · simp [zz, hx0.1, h2] at this; linarith
      · simp [zz, hx0.1, h2] at this; omega
    · obtain ⟨x0, hx0⟩ : ∃ x0, K.Adj u x0 ∧ ¬ K₁.Adj u x0 := by
        by_contra hc
        have : lossL K K₁ u = 0 :=
          Finset.sum_eq_zero (fun y _ => if_neg (fun h => hc ⟨y, h⟩))
        omega
      have hd := a2a hn hK hK1 hag1 x0
      have hz : zz K K₁ u x0 = 1 := by simp [zz, hx0.1, hx0.2]
      rw [hz] at hd
      have hdx : dgN K x0 = d + 1 := by
        rcases a0 hn hdeg hK x0 with e | e <;> rcases a0 hn hdeg hK1 x0 with e' | e' <;> omega
      have hc : chi d K x0 = chi d K u := by unfold chi; rw [hdx, hu]
      have := h0 x0 hc
      rw [hz] at this
      by_cases h2 : K₂.Adj u x0
      · simp [zz, hx0.1, h2] at this; omega
      · simp [zz, hx0.1, h2] at this; linarith
  refine ⟨hkey, fun x hx => ?_⟩
  have hc : chi d K x = chi d K u := by unfold chi; rw [hx]
  have := h0 x hc
  rw [hkey] at this
  have h3 : zz K K₁ u x = zz K K₂ u x := by
    have : lossL K K₂ u * (zz K K₁ u x - zz K K₂ u x) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · omega
    · linarith
  unfold zz at h3
  by_cases a1 : K₁.Adj u x <;> by_cases a2 : K₂.Adj u x <;> by_cases a3 : K.Adj u x <;>
    simp [a1, a2, a3] at h3 ⊢

end Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen

theorem Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen := by
  intro n hn d G H hdeg hNF hGH hni dg ag z
  classical
  refine ⟨fun K hK x => Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.a0 hn hdeg hK x,
    fun K hK u => Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.a3 hGH hni hK u,
    Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.Ct d G d - Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.Ct d G (d + 1) - 1, ?_, ?_⟩
  · intro K₁ K₂ h1 h2 u hag x
    have hz : ∀ y, z K₁ K₂ u y = Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.zz K₁ K₂ u y := by
      intro y
      by_cases a : K₁.Adj u y <;> by_cases b : K₂.Adj u y <;> simp [z, a, b, Set.indicator, Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.zz]
    refine ⟨?_, fun hx => ?_⟩
    · rw [hz]; exact Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.a2a hn h1 h2 hag x
    · have : ∑ y : Fin n, Set.indicator {w : Fin n | K₁.Adj x w} (z K₁ K₂ u) y =
          Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.AK K₁ (Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.zz K₁ K₂ u) x := by
        unfold Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.AK
        apply Finset.sum_congr rfl; intro y _; rw [Set.indicator_apply, hz]; rfl
      rw [this, hz]; exact Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.a2c hn hdeg hNF h1 h2 hag x hx
  · intro K K₁ K₂ hK h1 h2 u hag1 hag2 hne1 hne2
    obtain ⟨e1, e2⟩ := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.a5 hn hdeg hNF hGH hni hK h1 h2 hag1 hag2 hne1 hne2
    refine ⟨?_, e2⟩
    have c1 := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.ncard_eq_sum (fun y => K.Adj u y ∧ ¬ K₁.Adj u y)
    have c2 := Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.ncard_eq_sum (fun y => K.Adj u y ∧ ¬ K₂.Adj u y)
    unfold Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen.lossL at e1
    exact_mod_cast c1.trans (e1.trans c2.symm)
