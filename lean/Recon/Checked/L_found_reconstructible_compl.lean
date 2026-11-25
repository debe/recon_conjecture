import Mathlib
import Recon.Statements.S_found_reconstructible_compl

namespace Recon.Checked.L_found_reconstructible_compl

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

theorem forward {n : ℕ} (G : SimpleGraph (Fin n)) (hG : Recon.Reconstructible G) :
    Recon.Reconstructible Gᶜ := by
  intro H hH
  have h2 := hyp_compl hH
  rw [compl_compl] at h2
  obtain ⟨e⟩ := hG _ h2
  obtain ⟨e'⟩ := iso_compl e
  rw [compl_compl] at e'
  exact ⟨e'⟩

end Recon.Checked.L_found_reconstructible_compl

theorem Recon.Checked.L_found_reconstructible_compl : Recon.Statements.S_found_reconstructible_compl := by
  intro n G
  constructor
  · exact Recon.Checked.L_found_reconstructible_compl.forward G
  · intro h
    have := Recon.Checked.L_found_reconstructible_compl.forward Gᶜ h
    rwa [compl_compl] at this
