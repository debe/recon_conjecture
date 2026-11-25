import Mathlib
import Recon.Statements.S_kelly_card_edges_add_degree

namespace Recon.Checked.L_kelly_card_edges_add_degree

open SimpleGraph

lemma ncard_edgeSet_eq {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeSet.ncard = Finset.card G.edgeFinset := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset]

end Recon.Checked.L_kelly_card_edges_add_degree

theorem Recon.Checked.L_kelly_card_edges_add_degree : Recon.Statements.S_kelly_card_edges_add_degree := by
  intro n G v
  classical
  rw [Recon.Checked.L_kelly_card_edges_add_degree.ncard_edgeSet_eq,
    Recon.Checked.L_kelly_card_edges_add_degree.ncard_edgeSet_eq, SimpleGraph.ncard_neighborSet,
    SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  have := G.degree_le_card_edgeFinset v
  omega
