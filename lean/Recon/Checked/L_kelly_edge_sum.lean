import Mathlib
import Recon.Statements.S_kelly_edge_sum

namespace Recon.Checked.L_kelly_edge_sum

open SimpleGraph

lemma card_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    (Recon.card G v).edgeSet.ncard = (G.edgeFinset.filter (fun e => v ∉ e)).card := by
  rw [SimpleGraph.edgeSet_induce,
    ← Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective),
    ← Set.ncard_coe_finset]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Set.mem_image, Set.mem_preimage, Finset.coe_filter, Set.mem_ofPred_eq,
      SimpleGraph.mem_edgeFinset, Sym2.mem_iff, not_or]
    constructor
    · rintro ⟨e, he, hee⟩
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk] at hee he
        have hx : (x : Fin n) ≠ v := fun h => x.2 (Set.mem_singleton_iff.mpr h)
        have hy : (y : Fin n) ≠ v := fun h => y.2 (Set.mem_singleton_iff.mpr h)
        rcases Sym2.eq_iff.mp hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨he, hx.symm, hy.symm⟩
        · exact ⟨by rwa [Sym2.eq_swap], hy.symm, hx.symm⟩
    · rintro ⟨h, ha, hb⟩
      refine ⟨s(⟨a, by simpa [eq_comm] using ha⟩, ⟨b, by simpa [eq_comm] using hb⟩), ?_, ?_⟩
      · simpa using h
      · simp

lemma card_split {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    (G.edgeFinset.filter (fun e => v ∉ e)).card + G.degree v = G.edgeFinset.card := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.incidenceFinset_eq_filter,
    add_comm]
  exact Finset.card_filter_add_card_filter_not _

lemma main : Recon.Statements.S_kelly_edge_sum := by
  intro n G
  classical
  simp only [card_edges]
  have h1 : ∑ v : Fin n, ((G.edgeFinset.filter (fun e => v ∉ e)).card + G.degree v)
      = n * G.edgeFinset.card := by
    simp [card_split]
  rw [Finset.sum_add_distrib, SimpleGraph.sum_degrees_eq_twice_card_edges] at h1
  have h2 : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  rw [h2, Nat.sub_mul]
  omega

end Recon.Checked.L_kelly_edge_sum

theorem Recon.Checked.L_kelly_edge_sum : Recon.Statements.S_kelly_edge_sum :=
  Recon.Checked.L_kelly_edge_sum.main
