import Mathlib
import Recon.Statements.S_found_hypomorphic_trans

namespace Recon.Checked.L_found_hypomorphic_trans
end Recon.Checked.L_found_hypomorphic_trans

theorem Recon.Checked.L_found_hypomorphic_trans : Recon.Statements.S_found_hypomorphic_trans := by
  intro n G H K ⟨σ, hσ⟩ ⟨τ, hτ⟩
  refine ⟨σ.trans τ, fun x => ?_⟩
  obtain ⟨e⟩ := hσ x
  obtain ⟨f⟩ := hτ (σ x)
  exact ⟨e.trans f⟩
