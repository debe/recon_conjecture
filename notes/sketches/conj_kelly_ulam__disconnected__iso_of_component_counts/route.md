# Route: equal component counts ⇒ isomorphic

Sketch, not a result. Standard: a finite graph is the disjoint union of its components.

1. **Type-preserving bijection of components.** Relation c ~ d :⇔ Nonempty (G[c.supp] ≃g H[d.supp]).
   For each component c with |c.supp| = k, pick F on Fin k with G[c.supp] ≃g F
   (`Fintype.equivFin` + `SimpleGraph.Iso.map` / `Equiv` transport; F connected since c is).
   Equal counts for that F ⇒ the fibres over "iso type" have equal size in G and H ⇒ a
   bijection φ : G.ConnectedComponent ≃ H.ConnectedComponent with G[c.supp] ≃g H[(φ c).supp]
   (build fibrewise, e.g. by `Fintype.card` equality on each class + `Equiv.sigmaFiberEquiv`,
   or by strong induction on the number of components, removing one matched pair).
   Make this a reusable helper: the sibling step `component_counts_of_induced_counts`
   needs it too, and may import the checked file.
2. **Glue.** V ≃ Σ c : G.ConnectedComponent, c.supp (`Equiv.sigmaFiberEquiv
   G.connectedComponentMk`, supp = fibre). Same for H. Combine φ with the chosen component
   isos into an Equiv on the sigma types, and show adjacency is preserved: adjacent vertices
   lie in one component (`ConnectedComponent.connectedComponentMk_eq_of_adj`), and adjacency
   inside a component is adjacency of the induced graph.
Mathlib: `Connectivity/Connected.lean` (ConnectedComponent, supp, `mem_supp_iff`),
`Connectivity/Subgraph.lean`, `ConnectedComponent.connected_toSimpleGraph`/`induce_supp`-style lemmas.
