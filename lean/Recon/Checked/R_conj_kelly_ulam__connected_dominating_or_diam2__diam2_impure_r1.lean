import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card

theorem Recon.Checked.R_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure_r1 : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__level_half_pure → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure := by
  intro hD hN hR n hn G hG
  by_cases hd : ∃ u : Fin n, ∀ j : ℕ, (∀ y : Fin n, G.Adj u y → (G.neighborSet y).ncard = j + 1 → ∀ x' y' : Fin n, (G.neighborSet x').ncard = (G.neighborSet u).ncard → x' ≠ y' → Nonempty (G.induce ({u, y}ᶜ : Set (Fin n)) ≃g G.induce ({x', y'}ᶜ : Set (Fin n))) → G.Adj x' y') ∨ (∀ y : Fin n, y ≠ u → ¬ G.Adj u y → (G.neighborSet y).ncard = j → ∀ x' y' : Fin n, (G.neighborSet x').ncard = (G.neighborSet u).ncard → x' ≠ y' → Nonempty (G.induce ({u, y}ᶜ : Set (Fin n)) ≃g G.induce ({x', y'}ᶜ : Set (Fin n))) → ¬ G.Adj x' y')
  · exact hD n hn G hd
  by_cases hm : (∃ d : ℕ, ∀ x : Fin n, (G.neighborSet x).ncard = d ∨ (G.neighborSet x).ncard = d + 1) ∧ (∀ x y : Fin n, (G.neighborSet x).ncard = (G.neighborSet y).ncard → Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({y}ᶜ : Set (Fin n)))) ∧ ∃ u u' : Fin n, ∃ α : G.induce ({u}ᶜ : Set (Fin n)) ≃g G.induce ({u'}ᶜ : Set (Fin n)), ∃ x : ({u}ᶜ : Set (Fin n)), G.Adj u x.1 ∧ ¬ G.Adj u' (α x).1
  · exact hN n hn G hm
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG
  exact hR n hn G ⟨h1, h2, h3, h4, h5, hd, hm⟩
