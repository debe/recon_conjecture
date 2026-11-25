import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure

theorem Recon.Checked.R_conj_kelly_ulam__connected_dominating_or_diam2_r1 : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__unique_copy_gluing → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2 := by
  intro hP hG hDE hD2 n hn G hC
  obtain ⟨hc, hcc, hdis⟩ := hC
  by_cases hp : ∃ u : Fin n, ∀ x y x' y' : Fin n, (G.neighborSet x).ncard = (G.neighborSet u).ncard → (G.neighborSet x').ncard = (G.neighborSet u).ncard → x ≠ y → x' ≠ y' → Nonempty (G.induce ({x, y}ᶜ : Set (Fin n)) ≃g G.induce ({x', y'}ᶜ : Set (Fin n))) → (G.Adj x y ↔ G.Adj x' y')
  · exact hP n hn G hp
  by_cases hg : ∃ u v : Fin n, u ≠ v ∧ (∀ T : Finset (Fin n), Nonempty (G.induce ({u, v}ᶜ : Set (Fin n)) ≃g G.induce (T : Set (Fin n))) → (T : Set (Fin n)) = {u, v}ᶜ) ∧ ∀ g : G.induce ({u, v}ᶜ : Set (Fin n)) ≃g G.induce ({u, v}ᶜ : Set (Fin n)), ∃ h : G.induce ({u, v}ᶜ : Set (Fin n)) ≃g G.induce ({u, v}ᶜ : Set (Fin n)), (∀ x : ({u, v}ᶜ : Set (Fin n)), G.Adj v (h x).1 ↔ G.Adj v x.1) ∧ (∀ x : ({u, v}ᶜ : Set (Fin n)), G.Adj u (g (h x)).1 ↔ G.Adj u x.1)
  · exact hG n hn G hg
  rcases hdis with hde | hd2
  · exact hDE n hn G ⟨hc, hcc, hde, hp, hg⟩
  · exact hD2 n hn G ⟨hc, hcc, hd2, hp, hg⟩
