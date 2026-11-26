import Mathlib
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__low_extension_pair
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_pair_compl
import Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__three_extensions

theorem Recon.Checked.R_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow_r1 : Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_eigen → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__low_extension_pair → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__extension_pair_compl → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow__three_extensions → Recon.Statements.S_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow := by
  intro hA hB hBc hC n hn G hG H hGH
  obtain ⟨⟨d, hdeg⟩, hcard, u, u', α, x, hx1, hx2⟩ := hG
  by_contra hne
  obtain ⟨K₁, K₂, K₃, h1, h2, h3, a1, a2, a3, n12, n13, n23⟩ := hC n hn G H u u' α x hx1 hx2 hGH hne
  have hL := fun n hn d G H h1 h2 h3 h4 => hB n hn d G H h1 h2 h3 h4 (hA n hn d G H h1 h2 h3 h4)
  rcases hBc hL n hn d G H hdeg hcard hGH hne u' K₁ K₂ K₃ h1 h2 h3 a1 a2 a3 with h | h | h
  · exact n12 h
  · exact n13 h
  · exact n23 h
