import Mathlib
import Recon.Statements.S_found_hypomorphic_symm

namespace Recon.Checked.L_found_hypomorphic_symm
end Recon.Checked.L_found_hypomorphic_symm

theorem Recon.Checked.L_found_hypomorphic_symm : Recon.Statements.S_found_hypomorphic_symm := by
  intro n G H hGH
  obtain ⟨σ, hσ⟩ := hGH
  refine ⟨σ.symm, fun y => ?_⟩
  obtain ⟨e⟩ := hσ (σ.symm y)
  rw [Equiv.apply_symm_apply] at e
  exact ⟨e.symm⟩
