import Mathlib

/-!
# Reconstruction conjecture: trusted definitions

TRUSTED FILE. Changes require explicit human approval (see CLAUDE.md, "Trusted zones").
Every statement the fleet proves is phrased with these definitions, so a wrong definition
makes every checked result meaningless. The anchors at the bottom are proved sanity checks
that a wrong definition would break.

Conventions:
* Graphs are Mathlib `SimpleGraph`s (undirected, loopless, no multi-edges).
* The headline statements use vertex type `Fin n`; the general definitions allow any type.
* A *card* is the vertex-deleted subgraph `G - v`, as an induced subgraph on `{v}ᶜ`.
* The *deck* is never built as a multiset of isomorphism classes. Two graphs have the same
  deck (are *hypomorphic*) iff some bijection of vertices matches every card with an
  isomorphic card. This is the standard definition (Bondy–Hemminger).
-/

namespace Recon

open SimpleGraph

universe u v

variable {V : Type u} {W : Type v}

/-- The card `G - v`: the subgraph of `G` induced on every vertex except `v`. -/
abbrev card (G : SimpleGraph V) (x : V) : SimpleGraph ({x}ᶜ : Set V) :=
  G.induce ({x}ᶜ : Set V)

/-- `G` and `H` are hypomorphic (have the same deck): a bijection `σ` of the vertices
matches every card `G - x` with an isomorphic card `H - σ x`. -/
def Hypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ x : V, Nonempty (card G x ≃g card H (σ x))

/-- `G` on `Fin n` is reconstructible: every graph with the same deck is isomorphic to it. -/
def Reconstructible {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H : SimpleGraph (Fin n), Hypomorphic G H → Nonempty (G ≃g H)

/-- A graph property `P` is recognizable (from the deck, for graphs on at least 3 vertices):
hypomorphic graphs either both have `P` or both lack it. -/
def Recognizable (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Hypomorphic G H → (P n G ↔ P n H)

/-- A class of graphs `C` is reconstructible: every member on at least 3 vertices is
reconstructible. (The deck need not reveal membership of `H`; `Reconstructible` quantifies
over all `H`.) -/
def ClassReconstructible (C : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ G : SimpleGraph (Fin n), C n G → Reconstructible G

/-- The Kelly–Ulam reconstruction conjecture: every graph on at least 3 vertices is
reconstructible. -/
def ReconstructionConjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ G : SimpleGraph (Fin n), Reconstructible G

/-! ## Definition anchors

These prove nothing new. They pin the definitions down: a definition of `Hypomorphic` that
was always true, always false, or ignored the cards would break one of them. -/

/-- Anchor: `Hypomorphic` is reflexive. -/
theorem anchor_hypomorphic_refl (G : SimpleGraph V) : Hypomorphic G G :=
  ⟨Equiv.refl V, fun _ => ⟨Iso.refl⟩⟩

/-- Anchor: on 2 vertices, the edge and the non-edge have the same deck (two single-vertex
cards each), so the conjecture needs `3 ≤ n`. -/
theorem anchor_two_vertices_hypomorphic :
    Hypomorphic (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) := by
  refine ⟨Equiv.refl _, fun x => ⟨{ toEquiv := Equiv.refl _, map_rel_iff' := ?_ }⟩⟩
  intro a b
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ha hb
  have hab : a = b := by omega
  subst hab
  simp

/-- Anchor: the edge and the non-edge on 2 vertices are not isomorphic. -/
theorem anchor_two_vertices_not_iso :
    ¬ Nonempty ((⊤ : SimpleGraph (Fin 2)) ≃g (⊥ : SimpleGraph (Fin 2))) := by
  rintro ⟨e⟩
  have h : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by simp
  exact (e.map_rel_iff.mpr h).elim

/-- Anchor: on 3 vertices, the triangle and the empty graph are not hypomorphic
(cards of the triangle have an edge, cards of the empty graph do not). -/
theorem anchor_three_vertices_not_hypomorphic :
    ¬ Hypomorphic (⊤ : SimpleGraph (Fin 3)) (⊥ : SimpleGraph (Fin 3)) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨e⟩ := hσ 0
  have h : (card (⊤ : SimpleGraph (Fin 3)) 0).Adj ⟨1, by simp⟩ ⟨2, by simp⟩ := by
    simp [card]
  exact (e.map_rel_iff.mpr h).elim

/-! ## Edge reconstruction

An *edge card* is the edge-deleted subgraph `G - e`, keeping every vertex. As for vertex
cards, the edge deck is never built as a multiset of isomorphism classes: two graphs have the
same edge deck (are *edge-hypomorphic*) iff some bijection of edge sets matches every edge
card with an isomorphic edge card. -/

/-- The edge card `G - e`: `G` with the single edge `e` deleted; every vertex is kept. -/
abbrev edgeCard (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph V := G.deleteEdges {e}

/-- `G` and `H` are edge-hypomorphic (have the same edge deck): a bijection `σ` of the edge sets
matches every edge card `G - e` with an isomorphic edge card `H - σ e`. -/
def EdgeHypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet, Nonempty (edgeCard G e ≃g edgeCard H (σ e))

/-- `G` on `Fin n` is edge-reconstructible: every graph with the same edge deck is isomorphic
to it. -/
def EdgeReconstructible {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H : SimpleGraph (Fin n), EdgeHypomorphic G H → Nonempty (G ≃g H)

/-- Harary's edge reconstruction conjecture: every graph with at least four edges is
edge-reconstructible. -/
def EdgeReconstructionConjecture : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), 4 ≤ G.edgeSet.ncard → EdgeReconstructible G

/-! ## Edge definition anchors

These pin the edge definitions down: a definition of `EdgeHypomorphic` that was always true,
always false, or ignored the edge cards would break one of them. -/

/-- Anchor: `EdgeHypomorphic` is reflexive. -/
theorem anchor_edge_hypomorphic_refl (G : SimpleGraph V) : EdgeHypomorphic G G :=
  ⟨Equiv.refl _, fun _ => ⟨Iso.refl⟩⟩

/-- The star `K_{1,3}` on `Fin 4`, with centre `0`. -/
abbrev anchorStar : SimpleGraph (Fin 4) where
  Adj a b := (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with h | h <;> exact h.2 h.1⟩

/-- The triangle on `{0, 1, 2}` plus the isolated vertex `3` (`K_3 + K_1`) on `Fin 4`. -/
abbrev anchorTriangle : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b ∧ a ≠ 3 ∧ b ≠ 3
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The path `0 - 1 - 2 - 3` (`P_4`) on `Fin 4`. -/
abbrev anchorPath : SimpleGraph (Fin 4) where
  Adj a b := a.val + 1 = b.val ∨ b.val + 1 = a.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with h | h <;> omega⟩

/-- Every edge card of the star is isomorphic to the matching edge card of `K_3 + K_1` under
the edge bijection swapping `s(0,3)` and `s(1,2)` (both are `P_3 + K_1`). -/
theorem anchor_edge_star_triangle_cards : ∀ e : Sym2 (Fin 4), e ∈ anchorStar.edgeSet →
    ∃ p : Equiv.Perm (Fin 4), ∀ a b, (edgeCard anchorTriangle (Equiv.swap s(0,3) s(1,2) e)).Adj
      (p a) (p b) ↔ (edgeCard anchorStar e).Adj a b := by decide

/-- Anchor: `K_{1,3}` and `K_3 + K_1` have the same edge deck (every edge card is
`P_3 + K_1`). -/
theorem anchor_edge_star_triangle_hypomorphic : EdgeHypomorphic anchorStar anchorTriangle := by
  refine ⟨Equiv.subtypeEquiv (Equiv.swap s(0,3) s(1,2)) (by decide), fun e => ?_⟩
  obtain ⟨p, hp⟩ := anchor_edge_star_triangle_cards e.1 e.2
  exact ⟨⟨p, hp _ _⟩⟩

/-- Anchor: `K_{1,3}` and `K_3 + K_1` are not isomorphic (`3` is isolated in `K_3 + K_1`,
no vertex is isolated in the star), so edge reconstruction needs a lower bound on the edge
count. -/
theorem anchor_edge_star_triangle_not_iso : ¬ Nonempty (anchorStar ≃g anchorTriangle) := by
  rintro ⟨f⟩
  have hnb : ∀ x : Fin 4, ∃ y, anchorStar.Adj x y := by decide
  obtain ⟨y, hy⟩ := hnb (f.symm 3)
  have h := f.map_rel_iff.mpr hy
  rw [RelIso.apply_symm_apply] at h
  exact h.2.1 rfl

/-- Anchor: the star and `K_3 + K_1` have 3 edges, just below the `4 ≤` threshold of
`EdgeReconstructionConjecture`. -/
theorem anchor_edge_card_count :
    anchorStar.edgeSet.ncard = 3 ∧ anchorTriangle.edgeSet.ncard = 3 := by
  constructor <;> rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] <;> decide

/-- No edge card of the star (`P_3 + K_1`) is isomorphic to the middle edge card of `P_4`
(`2 K_2`). -/
theorem anchor_edge_path_star_cards : ∀ e : Sym2 (Fin 4), e ∈ anchorStar.edgeSet →
    ∀ p : Equiv.Perm (Fin 4), ¬ ∀ a b, (edgeCard anchorStar e).Adj (p a) (p b) ↔
      (edgeCard anchorPath s(1,2)).Adj a b := by decide

/-- Anchor: `P_4` and `K_{1,3}` both have 3 edges but different edge decks, so
`EdgeHypomorphic` looks at the edge cards, not just at the number of edges. -/
theorem anchor_edge_path_star_not_hypomorphic : ¬ EdgeHypomorphic anchorPath anchorStar := by
  rintro ⟨σ, hσ⟩
  obtain ⟨f⟩ := hσ ⟨s(1,2), by decide⟩
  exact anchor_edge_path_star_cards (σ ⟨s(1,2), by decide⟩).1 (σ ⟨s(1,2), by decide⟩).2
    f.toEquiv (fun _ _ => f.map_rel_iff)

end Recon
