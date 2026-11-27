# Card maps beyond counts: where the isomorphisms themselves have been used

Librarian scout, 2026-11-27, for round 16: the signed-cover problem of t2.md §5.5 in
`…__phantom_and_mate__walk_degenerate` (brief: `notes/rounds/16_prep/brief.md`). Nothing in this file
is a result.

Tags:
- **read**: I read the statement in the text named.
- **secondary**: seen only in a later paper or in a search summary.
- **UNVERIFIED**: from memory or from a bare citation.
- **[derived]**: my own paper argument, not refuter-checked.

## 0. Summary

1. **Card maps used as maps.** Only one line of the classical literature uses the card
   isomorphisms as maps rather than through what they count: Kocay's partial automorphisms
   (1984), and the Godsil–Kocay / Kocay coset completion (1982, 1984). The mechanism extends a
   card map to an automorphism of a *different* graph, then reads structure off the orbits
   (§1).
2. **The finite ℤ₂-twist counterexamples** run on a 2-adic tower on 2ⁿ points, and they put the
   twist where a graph cannot: Stockmeyer on the arc inside an antipodal pair, Kocay's 3-graphs
   in the link of an apex. The infinite tree counterexample uses self-similarity and no twist
   (§2).
3. **[derived] Lemma E.** A card map at u_i that fixes u′_i and commutes with τ on N(u′_i)
   extends to G^Q ≅ G (§3.1). So SCL is a question of whether card maps preserve fibres. Covers
   whose isomorphisms ignore the fibres are studied as TF-isomorphisms and unstable graphs
   (§3.3).
4. **Searched for, not found:**
   - a deck theorem for double covers, 2-lifts, or signed graphs up to switching;
   - any test of CFI pairs against true vertex decks;
   - a card-map theorem for vertex-transitive or Cayley graphs.

   The nearest item is an open two-graph conjecture (§4).

## 1. Using the card isomorphism as a map

### 1.1 Kocay, partial automorphisms

W. L. Kocay, *Partial automorphisms and the reconstruction conjecture*, J. Austral. Math. Soc.
(Ser. A) 37 (1984) 317–336, doi:10.1017/S1446788700022291. **Read**: pp. 317–324 and 335–336
(publisher PDF, text layer).

**Setting.** G has n vertices of degree k, and non-adjacent vertices u, v of degree k − 1. H
rejoins u differently, with new vertex x and other low vertex w, so that G − u = H − x. Let
p : G − v → H − w be a card map.

**Lemma 1.3 (orbit chain).** Iterate p from u (and from w) until the iterate lands in {v, x}.
This terminates because p is a bijection V ∖ {v, x} → V ∖ {u, w} on a finite set.

**Lemma 1.5 (the key step).** Let Γ := G + uv ≅ H + wx, via ψ. Then θ = ψp : Γ − v → Γ − w
extends to Aut(Γ) by v ↦ w. The reason given is that θ maps the degree-(k−1) vertices of Γ − v
onto those of Γ − w, "that is, it maps the vertices adjacent to v in Γ to those adjacent to w".
**The deleted vertex's neighbourhood is recognizable inside the card, so every card map
respects it.**

**Theorems 2.3 and 3.1.**
- If uv and uw lie in one edge-orbit of ⟨θ⟩, then G = Γ − uv ≅ Γ − uw ≅ H.
- This happens when gcd(k₁, k₂ + 1) = 1, and when k₁ = k₂.
- Otherwise, explicit circulant-type orbit graphs determine Γ for k = 3 (Corollary 3.6).
- §5 suggests that two card maps, generating ⟨θ, θ′⟩, "would force much more of the
  structure".

**Lean.** Medium, about 200–400 lines. Lemma 1.5 is an `Equiv` extension; the edge orbits use
`MulAction.orbit` on `Sym2`.

### 1.2 Kocay, orbits of partial permutations; Godsil–Kocay

W. L. Kocay, *Graphs, groups and pseudo-similar vertices*, J. Austral. Math. Soc. (Ser. A) 37
(1984) 181–189, doi:10.1017/S1446788700022023. **Read**: pp. 181–185.

**Setting.** U = {u₀, …, u_{k−1}} are mutually pseudosimilar, and p_i : X − u_i → X − u₀ are the
card maps, viewed as "partial permutations".

**Theorem 3.1.** The orbit graph of {p_i} has exactly one open orbit, and it contains U. The
proof iterates p_i from u₀ until it reaches u_i. Off the open orbit, the p_i are automorphisms
of the induced subgraph.

**Theorems 3.2–3.3 (completion).**
- The construction uses a spanning tree of the open orbit, the free group on the p_i, and
  Schreier coset diagrams.
- It embeds X as an induced subgraph of a graph Y, infinite in general. Each p_i extends to
  an automorphism of Y, and U lies in one Aut(Y)-orbit.
- In Kocay's words, the vertices are "pseudo-similar due to the action of a group on the
  cosets of some subgroup".

**Godsil–Kocay (JCTB 1982).** The k = 2 case, made finite by adding relators. **Secondary**, via
Kocay 1984, pp. 181 and 185.

**Relevance.** This is the classical form of the holonomy in r14-t1 (Prop. 2.3). Kocay,
*Hypomorphisms, orbits, and reconstruction*, JCTB 44 (1988) 187–200, reportedly treats
hypomorphic pairs. I could not access it: **UNVERIFIED**.

**Lean.** Theorem 3.1 is easy, about 100–200 lines. Use only the finite shadow of the
completion.

### 1.3 Mechanisms that use the maps only through a number

- **Nash-Williams' lemma** counts permutations. It collapses at the vertex level (t2 §4.3;
  `groups_and_harmonic.md` S1–S2).
- **Krasikov–Roditty**, *Balance equations for reconstruction problems*, Arch. Math. 48 (1987)
  458–464, use modified decks (**secondary**, via Thatte, arXiv:math/0608080).
- **Fourier methods**: Radcliffe–Scott 1998, Pebody 2004, Stanley 1985
  (`groups_and_harmonic.md` S8, S9, S11).
  - The freedom that low-order data leave is a phase (a character), and triple products remove
    it.
  - Homometric pairs have the form u(x)v(x) against u(x)v(x⁻¹) (Rosenblatt–Seymour, SIAM
    J. Alg. Disc. Meth. 3 (1982) 343–350, doi:10.1137/0603035). The citation is read; the form
    is **UNVERIFIED**.
  - This is the abelian prototype of a ℤ₂ flip that low-order data cannot see. It does not
    transfer, because here *all* count data are blind.
- **Signed switching decks**: Cavaleri–Donno–Spessato, arXiv:2611.13901 (abstract); Silva,
  UFMG thesis 2024 (**UNVERIFIED**). Both reconstruct from switched copies, by counting.

## 2. Known ℤ₂-twist counterexamples: why they work, what a graph would need

### 2.1 Stockmeyer tournaments

**Read** in R. Egrot and R. Hirsch, *Seurat games on Stockmeyer graphs*, arXiv:2008.01327v4: §6
(Def. 6.1 and Figs. 8–9, restating Stockmeyer's Census I, JCTB 1981) and Lemmas 7.9–7.10.

**Construction.** T_k on {1, …, 2^k} has the arc i → j iff odd(j − i) ≡ 1 (mod 4), where odd(z)
strips the powers of 2. Lemma 7.10: odd((j − i) ± 2ⁿ) ≡ odd(j − i) (mod 4) unless
j − i ∈ {0, ±2^{n−1}}.

**[derived] Reading.**
- T_k is a circulant on ℤ/2^k except on the antipodal matching.
- That matching cannot be oriented invariantly, because 2^{k−1} is its own negative. It is
  oriented "by halves" instead, which is a ℤ₂ cocycle.

**Census II** (arXiv:2110.06158; scan read in r14-t1 §6). Each vertex k has an antipode k̄. The
card map σ_{p,k}, extended by k ↦ k, carries G_p to G_p* except on the arc kk̄, which it
reverses. So the twist sits **inside a τ-pair**.

**Why graphs differ.** A graph cannot do this: the edge x τx is τ-invariant, and PM.1 gives
Δ_{x,τx} = 0. A graph analogue would need both a 2-adic self-similarity (a ℤ/2^k action whose
top involution is τ) and a twist carried by the inter-pair matchings. PM⁺ already restricts the
second.

### 2.2 Kocay's 3-uniform hypergraphs (JCTB 42 (1987) 46–63)

**Read** in J. Cooper and U. Okur, *Polynomial reconstruction problem for hypergraphs*,
arXiv:2312.16152v2, Defs. 10–15 and Thm 2.1. Kocay's own proof was not read.

**Construction.**
- Vertices: an apex 0 and ℤ/N, with N = 2ⁿ.
- E_r(x_i) = Σ_{j ≡ i (mod 2^r)} x_j lifts a hypergraph mod 2^r, and the base Γⁿ is a sum of
  lifted cyclic triple patterns.
- The pair is X = Γ + x₀E₂(x₁x₂ + x₃x₄) and Y = Γ + x₀E₂(x₁x₄ + x₂x₃).

**[derived] Reading.** The link of the apex joins residue classes mod 4 completely: as
{1,2},{3,0} in X and as {1,0},{2,3} in Y. So X and Y differ by **flipping a perfect matching
of four classes**. That is the block-level analogue of G against G^Q.

**Why the decks agree.** **UNVERIFIED**.

**What fails for graphs.** A 3-graph stores a whole graph (the link) at one vertex. A graph
stores only a set there, and a set has no matching to flip.

### 2.3 Infinite examples

N. Bowler, J. Erde, P. Heinig, F. Lehner and M. Pitz, *A counterexample to the reconstruction
conjecture for locally finite trees*, Bull. LMS (2017), doi:10.1112/blms.12053, arXiv:1606.02926.
**Read**: abstract, and the §2 overview on ar5iv.

**Mechanism.** Finite stages carry red and blue leaves as "promises", and every leaf of one
colour is extended identically. The colour-preserving card maps T_n − x_j → S_n − y_j persist in
the limit. Ever-longer bare paths keep the two trees non-isomorphic. There is no twist.

Fisher, J. Combin. Theory 7 (1969): citation only, **UNVERIFIED**.

**Common feature.** In all three examples, each card map relabels along a self-similar
structure and moves the discrepancy into the hole. A graph counterexample to SCL needs such a
map at every vertex. By §3.1, that map must fail τ-equivariance near the hole.

## 3. Local structure forced on card maps, and the global conclusion

### 3.1 The extension criterion ([derived], elementary, not refuter-checked)

**Lemma E.**
- *Hypotheses.*
  - G and K are graphs on V with a common involutive automorphism τ, and they agree on the
    pair {x, τx}.
  - f : K − x → G − x is an isomorphism with f(τx) = τx.
  - f(τy) = τf(y) for every y ∈ N_K(τx) ∖ {x}.
- *Conclusion.* f, extended by x ↦ x, is an isomorphism K → G.

*Proof.*
1. N_K(x) ∖ τx = τ(N_K(τx) ∖ x).
2. f maps N_K(τx) ∖ x onto N_G(τx) ∖ x.
3. By equivariance, f maps N_K(x) ∖ τx onto τ(N_G(τx) ∖ x) = N_G(x) ∖ τx.
4. The pair edge is the same in K and G. ∎

**Application to SCL.** Take K = G^Q and x = u_i: τ ∈ Aut(G^Q), and PM.1 holds on the pair
(t2 §5.2–5.3). So **SCL follows if, for some i, a card map G^Q − u_i → G − u_i fixes u′_i and
commutes with τ on N(u′_i).** This is Kocay's Lemma 1.5 with "recognized by degree" replaced by
"recognized as τ of the partner's neighbourhood", and it makes the "near i" of t2 §5.5 exact.

**Cohomological reading.** Suppose f fixes u′_i, maps every P_j (j ≠ i) onto itself, and maps F
onto F.
- Then f acts as a switching π_S on M_τ − i, so Q|_{M_τ−i} = δ(S).
- The edges at u′_i force j ∈ S ⟺ ij ∈ Q, so Q = δ_{M_τ}(S): a single card kills [Q].
- So [Q] ≠ 0 needs every card map either to cover a non-trivial automorphism α_i of the
  decorated M_τ − i with α_i*[σ^Q] = [σ], or to swap vertices across fibres.

**Lean.** Easy, about 60–120 lines (`SimpleGraph.Iso` plus an `Equiv` extension). A natural first
child step.

### 3.2 Switching classes are determined by circle signs

T. Zaslavsky, *Six signed Petersen graphs, and their automorphisms*, arXiv:1303.3347 (2013).
**Read** (ar5iv). Lemma 4.1: "if two signatures of Γ have the same circle signs, then one is a
switching of the other". "Switching isomorphic" means isomorphic to a switching. The earlier
source is Zaslavsky, *Signed graphs*, Discrete Appl. Math. 4 (1982) 47–74 (**secondary**).

**[derived]** The standard voltage-graph consequence: G^Q ≅ G by a *fibre-preserving* map iff
(M_τ, σ^Q) and (M_τ, σ) are switching isomorphic by an automorphism that preserves the
decoration. For the general lifting theory see Malnič, Nedela and Škoviera, Europ. J. Combin.
21 (2000) 927–947, doi:10.1006/eujc.2000.0390 (zbMATH summary only, **UNVERIFIED**).

### 3.3 When isomorphisms of double covers ignore the fibres

**Lauri, Mizzi and Scapellato**, *Unstable graphs: a fresh outlook via TF-automorphisms*,
arXiv:1401.6552 (Ars Math. Contemp. 2015, **secondary**). **Read**:
- a TF-isomorphism is a pair (α, β) with uv ∈ E(G) iff (αu, βv) ∈ E(H);
- G and H are TF-isomorphic iff their canonical double covers are isomorphic (they credit their
  own 2004 paper);
- G is *unstable* iff Aut(G) × ℤ₂ < Aut(G × K₂).

**R. Mizzi**, arXiv:2603.27559 (v4, Nov 2026); **abstract only**. Instability, and non-isomorphic
graphs sharing a canonical double cover, are both governed by "the conjugacy classes of strongly
switching involutions in Aut(CDC(G))".

**Relevance.** The canonical double cover is the all-negative signature. TF-cousins are exactly
the covers that are isomorphic only by maps that ignore the fibres: the second escape route of
§3.1.

### 3.4 Whitney and Hemminger: local structure forces an induced map

- **Whitney (1932)**: an edge isomorphism of connected graphs other than K₃ and K₁,₃ is
  induced by a vertex isomorphism (**secondary**).
- **Hemminger**, *On reconstructing a graph*, Proc. AMS 20 (1969) 185–187,
  doi:10.1090/S0002-9939-1969-0232696-4. Greenwell (Proc. AMS 30, 1971) credits it with: G is
  edge-reconstructible iff L(G) is vertex-reconstructible (**secondary**; text not opened).
- **Mechanism.** Card maps of L(G) send stars to stars, and the stars rebuild G.
- **Analogue here.** Show that card maps send τ-pairs to τ-pairs, then apply §§3.1–3.2.

## 4. Covers, twists and symmetric graphs: what exists

- **Two-graphs.** D. M. Duncan, T. R. Hoffman and J. P. Solazzo, *Numerical measures for
  two-graphs*, arXiv:0810.3189 (**read**, §5).
  - Conjecture 2: "Every switching equivalent class on at least 4 vertices is
    reconstructible" (deck up to switching).
  - It is checked only on the four non-trivial regular two-graphs on 26 vertices.
  - It is the only statement of its kind that I found.
- **Cai–Fürer–Immerman.**
  - Node-deletion subgraph GNNs are bounded by 3-WL (Frasca, Bevilacqua, Bronstein and Maron,
    arXiv:2206.11140; **secondary**). So colour refinement on cards is a count relaxation.
  - **[derived, UNVERIFIED]** CFI's twist group is ℤ₂^E modulo the *even* subsets of stars.
    This is coarser than H¹ = ℤ₂^E/⟨stars⟩, because the gadgets kill π_S. So G^Q is a plain
    signed-cover twist, not a CFI twist.
  - No test of CFI pairs against vertex decks was found.
- **Vertex-transitive and Cayley graphs.** They are regular, hence reconstructible. No card-map
  theorem was found.
- **Shared-card pairs** (Ivanov, arXiv:2608.11930 and arXiv:2609.00394; read in r14-t1 §7). The
  gluing obstruction is a sign carried by an even/odd selector, which only the unshared cards
  see.

## 5. Levers for the signed-cover problem

- **L1. Neighbourhood recognition, then extension** (Kocay 1984, Lemma 1.5; Lemma E). Find an
  isomorphism invariant of the card that pins u′_i (the vertex whose τ-partner is missing) and
  forces f to be τ-equivariant on N(u′_i), as degree k − 1 did for Kocay. Then G^Q ≅ G directly,
  with no cohomology needed.
- **L2. Common supergraph and edge orbits** (Kocay 1984, Theorems 2.3 and 3.1).
  - Let Γ⁺ := G ∪ G^Q (Q-blocks filled to K₂,₂) and Γ⁻ := G ∩ G^Q (Q-blocks emptied). Both are
    τ-symmetric with matching graph M_τ ∖ Q.
  - Ask which of Γ± a card map extends to as a partial automorphism.
  - If both matchings of a Q-block lie in one edge-orbit, then G ≅ G^Q.
- **L3. Orbit chains and the single open orbit** (Kocay 1984b, Theorem 3.1). The composites
  f_j⁻¹f_i are corank-2 partial automorphisms (r14-t1 Lemma 2.1), and they are automorphisms off
  one open orbit. Show that this orbit forces fibre preservation with α_i = id at some i; then
  §3.1 gives Q = δ(S).
- **L4. Fibre preservation is the whole problem** (Zaslavsky Lemma 4.1; Lauri–Mizzi–Scapellato;
  Mizzi 2026).
  - By §3.1, [Q] ≠ 0 forces every card map to swap fibres, or to cover a non-trivial switching
    isomorphism of the decorated M_τ − i.
  - Classify these maps by conjugacy classes of fibre-switching involutions, as Mizzi does.
  - Or build the counterexample: by §2 it needs a self-similar relabelling at every vertex.
- **Calibration** (not a lever; [derived]). Drop H1, the sparsity of M_τ and the decoration,
  and take M_τ = K_n. Up to alignment, the fibre-preserving form of SCL then becomes
  Duncan–Hoffman–Solazzo's open Conjecture 2. So distrust any L4 argument that never uses H1 or
  the decoration.

## 6. Sources opened this session

- **Opened:**
  - Kocay 1984a and 1984b (publisher PDFs);
  - Egrot–Hirsch, arXiv:2008.01327v4;
  - Cooper–Okur, arXiv:2312.16152v2;
  - Duncan–Hoffman–Solazzo, arXiv:0810.3189;
  - Bowler et al., arXiv:1606.02926;
  - Zaslavsky, arXiv:1303.3347;
  - Lauri–Mizzi–Scapellato, arXiv:1401.6552;
  - Mizzi, arXiv:2603.27559 (abstract only);
  - Stockmeyer, arXiv:2110.06158 (abstract only; the scan facts come from r14-t1).
- **Search pages only:** Malnič–Nedela–Škoviera, Rosenblatt–Seymour, Hemminger, Frasca et al., and
  Krasikov–Roditty (via Thatte).
