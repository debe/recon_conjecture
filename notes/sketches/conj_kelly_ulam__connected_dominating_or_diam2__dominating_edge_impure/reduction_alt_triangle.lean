import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__triangle_free_dominating_edge
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__dominating_edges_in_triangles

theorem Recon.Checked.R_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure_r1 : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__triangle_free_dominating_edge → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__dominating_edges_in_triangles → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure := by
  intro h1 h2 n hn G hG
  by_cases hq : ∃ u v : Fin n, G.Adj u v ∧ (∀ x : Fin n, x = u ∨ x = v ∨ G.Adj x u ∨ G.Adj x v) ∧ ∀ x : Fin n, ¬ (G.Adj x u ∧ G.Adj x v)
  · exact h1 n hn G ⟨hG, hq⟩
  · exact h2 n hn G ⟨hG, hq⟩
