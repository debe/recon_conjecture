# Builder plan for WR (main session, round 14)

This is a sketch, not a result. Theorem WR comes from t3.md §3.2 in the phantom_and_mate directory of the diameter-2 branch. The main session checked it by hand.

## Reuse

Import the checked DWC₁ file:

```
Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degree_corank_one
```

Open its namespace. It provides:
- `alg`, `ser`, `ser_left`, `ser_right`, `del`, `Es`, `alpha`;
- `cc` (closed walks), `ww` (walks from a vertex), `trace_id`, `sum_id`, `good`;
- `hagos_induction`, `card_tr`, `ww_succ`.

Its main proof derives, for a pull-back K of a hypomorph that is hypomorphic to G through the identity, `cc (A_K) k v = cc (A_G) k v` and `ww (A_K) k v = ww (A_G) k v` for all k and v.
- Factor that part out as a local lemma, "Theorem H through the identity", by copying the relevant block.
- Also copy the helpers `nbr_bal` and `deg_T0` usage from the checked `…aligned_switch_kelly4` file and the `…pointed_pair_symmetric` file.

## Route

1. **The re-attachment K.**
   - H is hypomorphic to G through σ, with card isomorphisms f_y. Let φ := extE (f_x) extended by x ↦ σx, a permutation of `Fin n`. The checked files build exactly this extension.
   - Set K := H.comap φ. Then K agrees with G on all pairs avoiding x, and K ≃g H.
   - K is hypomorphic to G through σ′ := φ⁻¹ ∘ σ, and σ′ x = x.
   - Simpler alternative if it fits: get hypomorphic-through-the-identity data as the DWC₁ proof does, then handle the x-row.
   - Goal: Theorem H for (G, K) at the vertex x, i.e. cc (A_K) k x = cc (A_G) k x and ww (A_K) k x = ww (A_G) k x.
   - Theorem H ties along σ′, and σ′ x = x. If the checked lemma only works through the identity, first compose K with σ′. Then pick the version that keeps x fixed: K agrees with G off x, and it is the x-row that matters.
2. **δ := 1_{N_K(x)} − 1_{N_G(x)}.**
   - δ x = 0.
   - The signs follow by cases.
   - The card-degree balance follows from the degree multisets of K and G by level telescoping: the `level_bal` pattern in the checked `…level_half_pure` file, or `nbr_bal`.
3. **First-return identity (walk balance).**
   - Let A₀ := del A x. It is the same matrix for K and G, because they agree off x.
   - Let b := the x-row of A, so A = A₀ + e_x bᵀ + b e_xᵀ.
   - With N = (I − tA)⁻¹ and N₀ = (I − tA₀)⁻¹ over PowerSeries ℤ (`ser`): e_xᵀ N 1 = N_xx · (1 + t bᵀ N₀ 1).
   - Derivation, a ring identity like `alg`:
     - N = N₀ + t N (A − A₀) N₀;
     - e_xᵀ N₀ = e_xᵀ, since x is isolated in A₀;
     - e_xᵀ N b = (N_xx − 1)/t, i.e. t·(e_xᵀ N b) = N_xx − 1, since N = I + t A N.
   - The left side and N_xx agree for K and G (step 1). N_xx is a unit (constant coefficient 1).
   - So bᵀ_K N₀ 1 = bᵀ_G N₀ 1 coefficientwise, i.e. Σ_y δ y · (A₀^k 1)_y = 0 for all k.
   - The statement's `w` is the walk sequence of A₀: its recursion uses neighbours z with G.Adj y z ∧ y ≠ x ∧ z ≠ x.
4. **Conclusion.** The WR hypothesis gives δ = 0. So N_K(x) = N_G(x), K = G, and G ≃g H through φ.
