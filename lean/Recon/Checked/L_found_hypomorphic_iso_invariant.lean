import Mathlib
import Recon.Statements.S_found_hypomorphic_iso_invariant

namespace Recon.Checked.L_found_hypomorphic_iso_invariant

/-- Restrict a graph isomorphism to the cards at `x` and `f x`. -/
def cardIso {n : ℕ} {G H : SimpleGraph (Fin n)} (f : G ≃g H) (x : Fin n) :
    Recon.card G x ≃g Recon.card H (f x) where
  toEquiv := f.toEquiv.subtypeEquiv (fun a => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact not_congr f.injective.eq_iff.symm)
  map_rel_iff' := by
    intro a b
    simp only [Recon.card, SimpleGraph.comap_adj, SimpleGraph.induce, Function.Embedding.coe_subtype]
    exact f.map_adj_iff

end Recon.Checked.L_found_hypomorphic_iso_invariant

theorem Recon.Checked.L_found_hypomorphic_iso_invariant : Recon.Statements.S_found_hypomorphic_iso_invariant := by
  intro n G G' H H' ⟨φ⟩ ⟨ψ⟩ ⟨σ, hσ⟩
  refine ⟨φ.symm.toEquiv.trans (σ.trans ψ.toEquiv), fun y => ?_⟩
  obtain ⟨e⟩ := hσ (φ.symm y)
  have h1 := Recon.Checked.L_found_hypomorphic_iso_invariant.cardIso φ.symm y
  have h2 := Recon.Checked.L_found_hypomorphic_iso_invariant.cardIso ψ (σ (φ.symm y))
  exact ⟨(h1.trans e).trans h2⟩
