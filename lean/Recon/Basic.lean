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

end Recon
