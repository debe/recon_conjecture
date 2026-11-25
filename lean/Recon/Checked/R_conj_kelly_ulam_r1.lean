import Mathlib
import Recon.Statements.S_conj_kelly_ulam
import Recon.Statements.S_conj_kelly_ulam__disconnected
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2

namespace Recon.Checked.R_conj_kelly_ulam_r1

open SimpleGraph

theorem iso_compl {V W : Type*} {A : SimpleGraph V} {B : SimpleGraph W} (f : A ≃g B) :
    Nonempty (Aᶜ ≃g Bᶜ) := by
  refine ⟨{ toEquiv := f.toEquiv, map_rel_iff' := ?_ }⟩
  intro a b
  show (¬ f a = f b ∧ ¬ B.Adj (f a) (f b)) ↔ (¬ a = b ∧ ¬ A.Adj a b)
  rw [f.map_rel_iff, f.injective.eq_iff]

theorem card_compl_iso {V : Type*} (G : SimpleGraph V) (x : V) :
    Nonempty (Recon.card Gᶜ x ≃g (Recon.card G x)ᶜ) := by
  refine ⟨{ toEquiv := Equiv.refl _, map_rel_iff' := ?_ }⟩
  intro a b
  simp only [Recon.card, compl_adj, comap_adj, Function.Embedding.coe_subtype,
    Equiv.refl_apply, ne_eq, Subtype.ext_iff]

theorem hyp_compl {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Recon.Hypomorphic G H) : Recon.Hypomorphic Gᶜ Hᶜ := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun x => ?_⟩
  obtain ⟨f⟩ := hσ x
  obtain ⟨g⟩ := iso_compl f
  obtain ⟨a⟩ := card_compl_iso G x
  obtain ⟨b⟩ := card_compl_iso H (σ x)
  exact ⟨(a.trans g).trans b.symm⟩

theorem recon_of_compl {n : ℕ} (G : SimpleGraph (Fin n)) (hG : Recon.Reconstructible Gᶜ) :
    Recon.Reconstructible G := by
  intro H hH
  have h2 := hyp_compl hH
  obtain ⟨e⟩ := hG _ h2
  obtain ⟨e'⟩ := iso_compl e
  rw [compl_compl, compl_compl] at e'
  exact ⟨e'⟩

theorem dominating_compl {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (h : 2 < G.edist u v) :
    Gᶜ.Adj u v ∧ ∀ x : Fin n, x = u ∨ x = v ∨ Gᶜ.Adj x u ∨ Gᶜ.Adj x v := by
  obtain ⟨hne, hadj, hcn⟩ := two_lt_edist_iff.mp h
  refine ⟨⟨hne, hadj⟩, fun x => ?_⟩
  by_cases hxu : x = u
  · exact Or.inl hxu
  by_cases hxv : x = v
  · exact Or.inr (Or.inl hxv)
  right; right
  by_cases hu : G.Adj x u
  · right
    refine ⟨hxv, fun hv => ?_⟩
    have hx : x ∈ G.commonNeighbors u v := ⟨hu.symm, hv.symm⟩
    rw [hcn] at hx
    exact hx
  · left
    exact ⟨hxu, hu⟩

end Recon.Checked.R_conj_kelly_ulam_r1

theorem Recon.Checked.R_conj_kelly_ulam_r1 : Recon.Statements.S_conj_kelly_ulam__disconnected → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2 → Recon.Statements.S_conj_kelly_ulam := by
  intro h1 h2 n hn G
  by_cases hc : G.Connected
  · by_cases hcc : Gᶜ.Connected
    · by_cases hall : ∀ u v : Fin n, G.edist u v ≤ 2 ∧ Gᶜ.edist u v ≤ 2
      · exact h2 n hn G ⟨hc, hcc, Or.inr hall⟩
      · push_neg at hall
        obtain ⟨u, v, huv⟩ := hall
        by_cases hG : G.edist u v ≤ 2
        · have h' := huv hG
          obtain ⟨hadj, hdom⟩ :=
            Recon.Checked.R_conj_kelly_ulam_r1.dominating_compl Gᶜ u v h'
          rw [compl_compl] at hadj hdom
          exact h2 n hn G ⟨hc, hcc, Or.inl ⟨u, v, hadj, hdom⟩⟩
        · push_neg at hG
          obtain ⟨hadj, hdom⟩ :=
            Recon.Checked.R_conj_kelly_ulam_r1.dominating_compl G u v hG
          apply Recon.Checked.R_conj_kelly_ulam_r1.recon_of_compl
          refine h2 n hn Gᶜ ⟨hcc, ?_, Or.inl ⟨u, v, hadj, hdom⟩⟩
          rw [compl_compl]; exact hc
    · apply Recon.Checked.R_conj_kelly_ulam_r1.recon_of_compl
      exact h1 n hn Gᶜ hcc
  · exact h1 n hn G hc
