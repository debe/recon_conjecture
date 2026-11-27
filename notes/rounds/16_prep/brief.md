# Round 16 prep: the signed-cover problem (paper only)

Prepared 2026-11-27 for next week. Nothing in here has run yet.

## Why this problem

Every checked step so far uses counts that are tied along a hypomorphism, such as degrees, Kelly counts and walk counts. Round 15 showed where counts stop working:
- **Coset freedom:** counts cannot separate vertices with isomorphic cards.
- **Prop AV:** real-valued "fake hypomorphs" are consistent with every linear tie.

The signed-cover problem is the smallest place where the card isomorphisms themselves have to be used, not only the numbers they preserve. That is the hard core in miniature.

## Setting (from round-15 t2.md §5)

Step: `conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degenerate`. It is the diameter-2 copy; the dominating-edge twin follows by reuse. The sketches live in its sketch directory. Round 15 wrote t1.md to t3.md there, so this round starts at t4 (`offset: 3`).

**H1.** τ ∈ Aut(G) with τ² = 1, and 𝒰(G) = Fix(τ). Here 𝒰 is the span of the walk vectors and the degree-class indicators. Equivalently, every integer vector orthogonal to 𝒰 is τ-antisymmetric.

The data, as defined in t2 §5.1:
- **F** is the set of fixed points of τ.
- **P_i = {u_i, u′_i}** are the τ-pairs.
- **The matching graph M_τ** has the pairs as vertices. Pairs P_i and P_j are adjacent in M_τ when the edges between them form a perfect matching.
- **The signature σ** is +1 when u_i u_j is an edge and −1 when u_i u′_j is an edge.
- **G^Q** is G with the matching flipped on every edge of Q ⊆ E(M_τ).

Paper results, refuter-checked in round 15 (t2.md §5.2–5.4):
- **PM:** every aligned hypomorph is G^Q for some Q.
- **Cuts:** G^Q ≅ G whenever [Q] = 0 in H¹(M_τ; ℤ₂), that is, whenever Q is a cut.
- **Forests:** if M_τ is a forest, G is reconstructible.
- **PM⁺ (closed-walk tie):** every vertex of a shortest Q-odd cycle lies on another Q-odd cycle of the same length and opposite sign. So G is reconstructible unless some vertex of M_τ lies on two cycles of equal length and opposite sign.

## The problem

**Signed-cover lemma (SCL), the target.** Assume H1, and G^Q − v ≅ G − v for every vertex v. Then G^Q ≅ G.

The natural form is "Q is a cut". The weaker G^Q ≅ G also suffices for reconstruction.

Equivalent signed-graph form: two signatures σ and σ·(−1)^Q on the same M_τ, with the same τ-symmetric decoration (complete blocks, the inner edges u_i u′_i, attachments to F). Assume their double covers have isomorphic vertex-deleted subgraphs vertex by vertex. Must the signatures be switching-equivalent, up to an automorphism of the cover?

The first case PM⁺ leaves open: some vertex of M_τ lies on two Q-odd cycles of the same length ℓ and opposite sign. Theorem H has been fully used at that point; only the cards remain.

## Angles (2 Fable thinkers, Opus refuters)

1. **Card-local (prove SCL).**
   - In the card G − u_i the involution τ is broken at i. A Q-odd ℓ-cycle through i lifts to a path on 2ℓ − 1 vertices in one cover, and to a cycle plus a path in the other.
   - Show that the card isomorphism f : G^Q − u_i → G − u_i must respect the pair structure near i. Possible levers: fixed points of τ, degrees, rooted walk data, the partner u′_i. Then derive a contradiction, or show that Q is a cut.
   - Use several cards at once, for example all u_i on one cycle, and induct on the cycle space of M_τ.
   - Say exactly where graph symmetry is used, since tournaments are not reconstructible.
2. **Signed graphs and CFI (prove SCL, or build the obstruction).**
   - Recast SCL as a statement about signed graphs and their double covers. Relevant literature, each to be checked or marked UNVERIFIED: Zaslavsky on signed graphs and switching; Stanley 1985 and Ellingham–Royle on switching reconstruction; Cai–Fürer–Immerman twists.
   - Neutral prior. Try to build ONE explicit CFI-type gadget where the cards cannot see the twist, verified by hand.
   - If such a gadget gives hypomorphic, non-isomorphic G and G^Q on n ≥ 3 vertices, that would be a counterexample to the conjecture. It would be worth as much as a proof, but it needs n ≥ 14 (McKay), so it must be argued on paper.
   - Otherwise, find the exact invariant the cards carry that kills [Q].

## Rules

- **No counting.** Do not enumerate or sample, and do not use `small_graphs.py`. At most one hand-built example per lemma. This is the standing memory rule `no-small-n-counting`.
- **Paper only.** No builders and no reduction submission in this round, unless the user asks.
- **The goal is a statement that holds for all n.** A clean "we could not" is an acceptable outcome, with the exact point where card maps fail to beat counts.

## How to run (when the user says go)

1. `git pull` on `main`, then branch `debe/round-16-signed-cover`.
2. `borg inbox`, then `borg tell collective "round 16 (debe): signed-cover problem (t2 §5.5) on diam2 …__walk_degenerate, paper only"`.
3. `python3 tools/desk.py lease <step> --holder round16 --minutes 120 --note "round 16 think: signed-cover problem"`.
4. Run `Workflow({scriptPath: "notes/rounds/16_prep/think_structural.js", args: {step: "<step>", holder: "round16", offset: 3, angles: [<angle 1 text>, <angle 2 text>]}})`.
   - The angle texts are the two items above. Prefix each with the Setting section, or point the thinker to this file and to t2.md §5.
   - Estimated cost: about 0.5M subagent tokens for 2 thinkers and 2 refuters.
5. Hand-check what survives, then write `notes/rounds/16.md`. Record the sketches and dead ends with `desk.py`, release the lease, and ship the notes with `python3 tools/ship.py "<title>"`.
