import Mathlib
import Recon.Statements.S_found_hypomorphic_compl

namespace Recon.Checked.L_found_hypomorphic_compl

theorem card_compl_iso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (x : V) (y : W)
    (e : Recon.card G x ≃g Recon.card H y) : Nonempty (Recon.card Gᶜ x ≃g Recon.card Hᶜ y) := by
  refine ⟨{ toEquiv := e.toEquiv, map_rel_iff' := ?_ }⟩
  intro a b
  have h1 : (Recon.card H y).Adj (e a) (e b) ↔ (Recon.card G x).Adj a b := e.map_rel_iff
  have h2 : e a = e b ↔ a = b := e.injective.eq_iff
  show (Hᶜ).Adj (e a).1 (e b).1 ↔ (Gᶜ).Adj a.1 b.1
  change H.Adj (e a).1 (e b).1 ↔ G.Adj a.1 b.1 at h1
  rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj, h1, Ne, Ne, ← Subtype.ext_iff,
    ← Subtype.ext_iff, h2]

end Recon.Checked.L_found_hypomorphic_compl

theorem Recon.Checked.L_found_hypomorphic_compl : Recon.Statements.S_found_hypomorphic_compl := by
  intro n G H ⟨σ, hσ⟩
  refine ⟨σ, fun x => ?_⟩
  obtain ⟨e⟩ := hσ x
  exact Recon.Checked.L_found_hypomorphic_compl.card_compl_iso G H x (σ x) e
