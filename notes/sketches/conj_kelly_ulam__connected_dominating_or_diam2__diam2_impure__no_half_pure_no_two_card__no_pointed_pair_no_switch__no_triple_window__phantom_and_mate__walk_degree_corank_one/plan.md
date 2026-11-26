# Builder plan for DWC₁ (main session, round 14)

This is a sketch, not a result. It combines the main session's check of t2.md (Theorem H) and t3.md §3.1 (Theorem DWC) in `../conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate/`.

## Route

1. **Pull-back.**
   - Given H hypomorphic to G via σ, set K := H.comap σ.
   - K ≃g H through σ, and G, K are hypomorphic through the identity.
   - The checked `…__aligned_switch_kelly4` proof (diam2 copy) does exactly this. Reuse its pattern and its helpers (open its namespace).
2. **Theorem H** (t2.md §3, builder table in t2.md §9). For all k and v: (A_K^k 1)_v = (A_G^k 1)_v.
   - The Scratch file `t2_hagos_induction.lean` in the phantom_and_mate Scratch directory has the complete induction, taking (I)–(III) as hypotheses.
   - Still to prove:
     - the resolvent identity (α) and its consequences (I) and (II);
     - the card bridge (tr A₀^k and 1ᵀA₀^k1 agree for (G, v) and (K, v));
     - the bridge from the statement's quantified sequence `w` to matrix powers.
   - Alternative to power series: prove (I) and (II) directly as coefficient identities by induction on k, whichever is shorter.
3. **Degree classes.** For every v and every degree j, v has as many neighbours of degree j in K as in G. This is `nbr_bal` in the checked `…__aligned_switch_kelly4` file. Degrees agree by `deg_T0`.
4. **Δ := A_K − A_G**, integer-valued with zero diagonal.
   - Each row r_v := (x ↦ [K.Adj v x] − [G.Adj v x]) is orthogonal to every walk vector. Write Σ_x r_v(x) w_k(x) = w_{k+1}^K(v) − w_{k+1}^G(v), and the walk vectors of K and G agree by step 2.
   - Each row sums to zero over every degree class (step 3).
5. **Endgame (corank ≤ 1, over ℤ).**
   - All rows are pairwise dependent by the class hypothesis.
   - Suppose some row r_u ≠ 0 and pick x with r_u(x) ≠ 0 (so x ≠ u). Apply the hypothesis to r_u and r_x: a·r_u + b·r_x = 0 with (a, b) ≠ 0.
     - At coordinate x, r_x(x) = 0, so a·r_u(x) = 0 and therefore a = 0.
     - Then b ≠ 0 and r_x = 0, so r_x(u) = 0.
     - Symmetry gives r_x(u) = r_u(x) ≠ 0, a contradiction.
   - Hence every row vanishes.
   - So K = G as graphs, and G ≃g H follows through σ.

## Reuse for WR (`…__walk_rigid_apex`)

Theorem H also gives WR via the first-return identity W_x(t) = (1 + t Σ_{y∈N′} F_y(t)) · R_x(t), where:
- R_x is the closed-walk generating function at x, and it is invertible;
- F_y are the walk vectors of the card.

Keep Theorem H's helpers general (any two hypomorphic graphs on `Fin n` through the identity) so the WR builder can import them.
