import Mathlib
import Recon.Statements.S_conj_kelly_ulam__disconnected
import Recon.Statements.S_conj_kelly_ulam__disconnected__connected_recognizable
import Recon.Statements.S_conj_kelly_ulam__disconnected__kelly_induced_count
import Recon.Statements.S_conj_kelly_ulam__disconnected__component_counts_of_induced_counts
import Recon.Statements.S_conj_kelly_ulam__disconnected__iso_of_component_counts

theorem Recon.Checked.R_conj_kelly_ulam__disconnected_r1 : Recon.Statements.S_conj_kelly_ulam__disconnected__connected_recognizable → Recon.Statements.S_conj_kelly_ulam__disconnected__kelly_induced_count → Recon.Statements.S_conj_kelly_ulam__disconnected__component_counts_of_induced_counts → Recon.Statements.S_conj_kelly_ulam__disconnected__iso_of_component_counts → Recon.Statements.S_conj_kelly_ulam__disconnected := by
  intro hconn hkelly hcomp hiso n hn G hG H hH
  have hH' : ¬ H.Connected := fun h => hG ((hconn n hn G H hH).mpr h)
  exact hiso n G H (hcomp n G H hG hH' (hkelly n G H hH))
