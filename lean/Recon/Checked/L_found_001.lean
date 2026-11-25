import Mathlib
import Recon.Statements.S_found_001

namespace Recon.Checked.L_found_001

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

end Recon.Checked.L_found_001

theorem Recon.Checked.L_found_001 : Recon.Statements.S_found_001 := by
  intro n G H ⟨f⟩
  exact ⟨f.toEquiv, fun x => ⟨Recon.Checked.L_found_001.cardIso f x⟩⟩
