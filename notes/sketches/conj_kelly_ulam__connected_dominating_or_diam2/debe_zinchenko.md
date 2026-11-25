# debe_zinchenko: audit of Zinchenko, arXiv:2611.13728v1 (two card types), and a builder route

Thinker `debe_zinchenko`, 2026-11-26. Step: `conj_kelly_ulam__connected_dominating_or_diam2`
(status `reduced`, `dead_ends` empty; open residuals `diam2_impure`, `dominating_edge_impure`).
**A sketch, not a result.** Nothing here is checked. "Paper argument" = an argument on paper,
the paper's or mine (mine is marked "own"). "Tested" = small-graph search, evidence only.
"Elaborates" = a Scratch file compiled; it says nothing about the gate.

Source: M. Zinchenko, *Two Types of Cards in Kelly-Ulam Conjecture*, arXiv:2611.13728v1
[math.CO], 10 Nov 2026, 28 pp., unrefereed. Read in full from the PDF (pp. 1-28). The PDF has
Sections 1-9 only; the roadmap on p. 2 says "Section 10" for what is Section 9.
Claim (Thm 1.1, p. 2): a graph on n ≥ 3 vertices whose deck has exactly two isomorphism types
of cards, t(G) = 2, is reconstructible.

## 0. Verdict

1. **The audit found no gap that breaks the argument.** I checked every lemma, proposition and
   theorem of Sections 2-9 line by line for all n (table in §2). Every step follows once the
   misprints in §3 are corrected. There is one false sentence (Prop 2.3(i): "t(G) = 2, so there
   are two distinct degrees"; a regular graph can have t = 2, e.g. C₃ ∪ C₄), and the paper's own
   next paragraph repairs it. Prop 2.3(ii) is never needed. So: **correct as far as a paper
   audit can tell; UNVERIFIED until the Lean gate accepts it.**
2. **Graph-specific steps (§5).** (a) Lemma 2.1/2.2: deg v = e(G) − e(G − v) and the bit law
   deg_{G−v} x = deg x − [x ~ v]. For tournaments e(T − v) is constant; tested: the only
   non-reconstructible tournament pair with t = 2 for n ≤ 6 (n = 4) has different score
   sequences, and no Stockmeyer pair B_k, C_k (k ≤ 4) has t = 2 (t = 3, 9, 17). (b) Lemma 3.3:
   fᵀ(A − λ)z = ((A − λ)f)ᵀz needs A = Aᵀ. For a tournament the identity of Lemma 3.1(c)
   survives, but Lemma 3.3 then only gives vanishing of *left* eigenvectors, and Lemma 3.4 feeds
   it a *right* kernel vector. Lemma 4.1 and 4.2(c) use the same symmetry. The argument does not
   run verbatim for digraphs.
3. **Normal form.** The theorem is the statement "degrees d, d + 1 and one card type per degree
   class ⇒ reconstructible"; the rest of t ≤ 2 is covered by the checked `pure_degree_class`.
4. **A cheaper sub-result (own observation, §6).** Sections 2-4 alone (Thm 4.4 / Cor 4.5) give:
   *a normal-form graph in which some card isomorphism G − u → G − u′ does not extend to an
   automorphism of G is reconstructible.* About 40% of the Lean cost. Tested: all three known
   residual members with t = 2 (`GhEJ]o`, ``K[N_ZpBVe`q{``, ``OpyHvCM]IFJpsMdwu`pJp``) lie in
   this narrow class (|Aut(G − v)| = 2·|Aut(G)_v| at every vertex).
5. **Lean cost.** Narrow class: about 1500-2200 lines. Full theorem: about 3700-5600 lines. No
   missing Mathlib theory: finite sums over `Fin n`, one rank-nullity step, Kelly's lemma
   (checked). The cost is length and bookkeeping (card isomorphisms on subtypes, the family of
   graphs hypomorphic to G, two uses of complementation).
6. **Extensions (§8).** No argument for t(G) = 3, and none for "one card type per degree class"
   with three or more degrees. What survives: the degree partition is equitable (own, easy).
   The scalar eigen-relation of Lemma 3.1(c) becomes a matrix relation and the sign argument of
   Lemma 3.4 is lost.

## 1. Notation (the paper's, with the misprints fixed)

- n ≥ 3, V the vertex set. G ~ H: hypomorphic (some bijection σ with G − v ≅ H − σv).
- **Counterexample**: (G, H) with G ~ H, G ≇ H, G in **normal form NF(d)**: every degree is d
  or d + 1, both occur, and deg x = deg y ⇒ G − x ≅ G − y.
- 𝒦 := the set of *labelled* graphs K on V with G ~ K (the paper says "isomorphism classes";
  it uses labelled graphs). G, H ∈ 𝒦; 𝒦 is closed under isomorphic copies on V.
- For K ∈ 𝒦: L_K, U_K the vertices of degree d, d + 1 ("low", "high"); χ_K = indicator of U_K;
  p = |L|, q = |U|; b, e = number of high neighbours of a low, high vertex; θ = e − b;
  c = d + 1 − e.
- K′ ∈ 𝒦 is an **extension** of K at u if K′ and K agree on all pairs avoiding u.
  C_K(u) = set of extensions (K ∈ C_K(u)). For K₁, K₂ agreeing off u:
  z[K₁, K₂; u](x) = [x ~_{K₁} u] − [x ~_{K₂} u], k[K₁, K₂; u] = #{z = 1}.
- A_K f (x) := Σ_{y ~_K x} f(y). ε_u = indicator of u. ⟨f, g⟩ = Σ_x f(x) g(x).
- After Thm 4.4: C_G(u) = {G, alt(u)}, z_u := z[G, alt(u); u], and
  for v low: S₀(v) = {z_v = 1} ⊆ N(v) ∩ U (lost), R₀(v) = {z_v = −1} ⊆ L ∖ N[v] (gained);
  for w high: R₁(w) = {z_w = 1} ⊆ N(w) ∩ U (lost), S₁(w) = {z_w = −1} ⊆ L ∖ N(w) (gained).
  k₀ = |S₀(v)| = |R₀(v)|, k₁ = |R₁(w)| = |S₁(w)|.
- 0/1 matrices (rows L, columns U unless said): D₀(v,w) = [w ∈ S₀(v)], D₁(v,w) = [v ∈ S₁(w)],
  D₂(v,w) = [v ~ w, w ∉ S₀(v)], D₃(v,w) = [v ≁ w, v ∉ S₁(w)] (so D₀ + D₁ + D₂ + D₃ = J);
  R₀ on L × L, R₁ on U × U; E₀(v,v′) = [v′ ≠ v, v′ ≁ v, v′ ∉ R₀(v)], E₁(w,w′) = [w′ ~ w, w′ ∉ R₁(w)].
- Switching graph T on V: u, x adjacent iff z_u(x) ≠ 0 or z_x(u) ≠ 0.

## 2. Audit, item by item

Status: OK = the argument is complete as written (up to listed misprints); OK* = correct after
the stated repair. Page numbers are those of the arXiv PDF.

| Item (page) | Statement | Status | Note |
|---|---|---|---|
| L 2.1 (3) | e(G) = e(H); deg_H σv = deg_G v; G − u ≅ G − u′ ⇒ deg u = deg u′ | OK | = T0; checked as `kelly_edge_count`, `kelly_card_edges_add_degree`. Needs n ≥ 3. |
| L 2.2 (3-4) | if for some v equal card-degrees of x, y ≠ v force [x~v] = [y~v], then G is reconstructible | OK | Mulla's (★) of t1; the induction is T2 "level counts". |
| P 2.3(i) (4-5) | counterexample with t = 2 ⇒ degrees are exactly d, d + 1 | OK* | "Since t(G) = 2, there are two distinct degrees" is false (C₃ ∪ C₄ is 2-regular with t = 2). Correct: *at most* two degrees. The next paragraph ("no two degrees differ by 1 ⇒ L 2.2 applies") also covers the regular case, so nothing is lost. |
| P 2.3(ii) (5) | every vertex has a high neighbour and a low non-neighbour | OK | Not needed: its only use (b ≥ 1 in Thm 7.2) follows from ∅ ≠ S₀(v) ⊆ N(v) ∩ U. |
| L 2.4 (5) | one card type per degree class; b, e constant; the same d, p, q, b, e for every K ~ G | OK | #{card-degree d + 1 in K − v} = q − χ_K(v) − (high neighbours of v). |
| L 2.5 (6) | (Ḡ, H̄) is a counterexample with low/high swapped, θ′ = −θ | OK | b′ = p − c, e′ = p − 1 − (d − b). |
| eq. (1) (6) | A_K χ_K = b·1 + θ χ_K for K ∈ 𝒦 | OK | restates L 2.4. |
| L 3.1 (7-8) | K₁, K₂ ∈ 𝒦 agree off u, s = χ_{K₁}(u): (a) deg u equal, Σz = 0, χ_{K₁} − χ_{K₂} = z; (b) z = 1 ⇒ high in K₁, z = −1 ⇒ low in K₁; (c) (A_{K₁} − (θ − s))z = k ε_u; (d) K₁ ≠ K₂ ⇒ k ≥ 1 | OK | (c) rechecked in sum form, §4 A3. Tested in relaxed form. |
| L 3.2 (9) | every C_K(u) contains a copy of G and a copy of H, hence some K′ ≠ K | OK | re-attachment; `iso_of_nbhd`. |
| L 3.3 (9) | A_K f = (θ − s) f, s = χ_K(u) ⇒ f(u) = 0; so f = 0 on the class s of K | OK | **uses A_K symmetric.** |
| L 3.4 (9) | K₁, K₂ ∈ C_K(u) ∖ {K}: k₁ = k₂ and z₁ = z₂ on the class of u | OK | y = k₂z₁ − k₁z₂ is a (θ − s)-eigenvector; a point x₀ of the class with z₁(x₀) = ±1 exists by 3.1(a)(b)(d). |
| C 3.5 (9-10) | (a) k[X, Y; u] = κ(u) for all X ≠ Y in C_G(u); (b) deg u = deg u′ ⇒ a permutation π with πu = u′ carries C_G(u) onto C_G(u′); κ depends on the degree only | OK | (a) is printed with "X ≇ Y"; the argument gives, and §4 needs, X ≠ Y. |
| (∗) (10) | (A_G − λ_v) z_K = κ(v) ε_v, λ_v = θ (v low), θ − 1 (v high) | OK | "A_w ∈ C_G(v) ∖ {G}" should read C_G(w). |
| L 4.1 (11) | (a) ⟨z_K, z_K′⟩ = k₁ z_K(w) − k₀ z_K′(v) (v low, w high); (b) same degree: z_K(v′) = z_K′(v) | OK | symmetry of A_G again. Tested on 6 real graphs. |
| L 4.2 (11-12) | A_G f = θ f ⇒ (a) f = 0 on L; (b) f constant on S(K), K ∈ C_G(v) ∖ {G}, v low; (c) f(x) = f(w) for x ∈ R₁(w) | OK | (b): the row x ≠ v of A_K f also changes by −z(x) f(v), which is 0 by (a); the paper omits this. (b) uses L 3.3 for K ≠ G. (c): "all terms is non zero" should be "nonnegative". |
| L 4.3 (12) | v low, K₁, K₂ ∈ C_G(v) ∖ {G}, S(K₁) ∩ S(K₂) ≠ ∅ ⇒ K₁ = K₂ | OK | Shorter own route from L 3.4 alone: §4 B3. |
| T 4.4 (12-13) | \|C_G(v)\| = 2 for every v | OK | Step 1: k₁ ≤ k₀ − 1; Step 2: k₀ ≤ k₁ − 1. High v by L 2.5. "z_{M₁}(v₂)" should be z_{M₁}(v′). |
| C 4.5 (13) | C_G(u) = {G, alt(u)}, alt(u) ≅ H; every card isomorphism G − u → G − u′ extends to an automorphism; Aut(G) transitive on L and on U; z_{πu}(πx) = z_u(x) | OK | cites "Lemma 3.3", should be 3.2. |
| L 5.1 (14-15) | (a) R₀, R₁ symmetric; (b) R₀D₁ + D₀R₁ = k₁D₀ + k₀D₁; (c) D₀ has row sums k₀, column sums γ; D₁ column sums k₁, row sums δ ≥ 1; pk₀ = qγ, qk₁ = pδ, γδ = k₀k₁ | OK | (c) needs the transitivity of C 4.5. |
| L 5.2 (15-16) | k₁ − k₀ = θ | OK | Step 1: "z_w(v) = 1" should be −1 (the next line uses −1). Step 2: "⟨a_G(w), z_w⟩" should be ⟨a_G(w), z_v⟩. |
| P 5.3 (16-17) | (a) R₀D₃ + D₀E₁ = k₀(D₂ + D₃); (b) E₀D₁ + D₂R₁ = k₁(D₂ + D₃) | OK | recomputed entrywise. Tested on 6 real graphs. |
| L 6.1 (17-18) | G ~ K, \|W\| < n ⇒ emb(F, G) = emb(F, K) | OK | Kelly's lemma (Bondy-Murty GTM 244, Lemma 2.20, as cited by the paper; checked here as `kelly_induced_count`). "(n − \|W\|) ≥ 0" should be > 0. |
| L 6.2 (18) | B a module: emb(F, G) = Σ_S emb_B(F[S], G) · out(S; G) | OK | The side condition β_G(g(c)) = F(a, c) belongs to the definition of out(S; G); the statement is garbled, the argument is clear. |
| L 6.3 (18-19) | G ~ K agree off a module B of G ⇒ emb_B(F, G) = emb_B(F, K) for \|W\| < n | OK | induction on \|W\|. Tested in a non-vacuous census form, n ≤ 6. |
| T 6.4 (19) | G ~ K, B ⊊ V a module of G, G and K agree on all pairs not inside B ⇒ G ≅ K | OK | **general and reusable**; no counterexample hypothesis. |
| L 6.5 (19-20) | Σ_u f(u) z_u = 0 ⇒ R₀f_L = k₀f_L, R₁f_U = k₁f_U, D₁f_U = −k₀f_L, D₀ᵀf_L = −k₁f_U | OK | |
| L 6.6 (20) | two quadratic-form expansions | OK | |
| L 6.7 (21) | Σ_u f(u) z_u = 0 ⇒ g := (f on L, −(δ/k₀) f on U) is constant on T-components | OK | δE_{D₀} + k₀E_{D₁} = 0 uses γδ = k₀k₁. |
| T 6.8 (21-22) | T is connected | OK | Z_B square ⇒ left and right kernels have equal dimension; B is a module; T 6.4 gives alt(u) ≅ G. |
| §7 WLOG (22) | θ ≤ 0, hence k₁ ≤ k₀ | OK | by L 2.5 and L 5.2. |
| L 7.1 (22) | k₁ ≤ k₀, v ∈ S₁(w) ⇒ S₀(v) ∩ R₁(w) ≠ ∅ | OK | "w ∉ S₀(w)" should be S₀(v). |
| T 7.2 (23) | θ is not an eigenvalue of A_G | OK | "f is constant on every edge" should be "val"; "By Theorem 6.4" should be 6.8. |
| L 8.1 (23) | R₁g = k₁g ⇒ D₀ᵀD₁g = k₀k₁g and R₀D₁g = k₀D₁g | OK | |
| T 8.2 (24) | the graph R₁ on U is connected | OK | "(i) φ_C(u) ≥ 0" should be > 0; (ii) follows from L 8.1 and L 6.6(b), not L 6.5; the parenthesis in (c)(2) is wrong and unused; L 8.1 is also applied to C′ = U ∖ C (a union of components, fine). |
| T 8.3 (24-26) | every R₀-component meets {v : w ∈ S₀(v)} for every w | OK | sums "Lemma 5.1(c)", should be 5.1(b). |
| T 9.1 (26-27) | D₂ = D₃ = 0 | OK | five observations, then closure of Ω₀ ∪ Ω₁ under R₀-steps. |
| L 9.2 (27) | F regular, all cards F − v (v ≠ r) pairwise isomorphic ⇒ F − r ≅ F − v | OK | Tested. |
| T 9.3 (27-28) | D₂ = D₃ = 0 is impossible | OK | "alt(r)", "alt(t)" should be alt(v). p = d + 1 from L 5.2. |

## 3. Repairs and remarks (own)

- **R1 (Prop 2.3(i)).** State it as: a non-reconstructible G with t(G) ≤ 2 has exactly the
  degrees d, d + 1 and one card type per degree. In our library: a graph with at most two
  degrees that are equal or not consecutive has a pure degree class (bit law), so the checked
  `pure_degree_class` applies.
- **R2 (Prop 2.3(ii)) is dead weight.** Drop it.
- **R3 (Lemma 4.3 from Lemma 3.4 alone).** Let v be low and K₁ ≠ K₂ in C_G(v) ∖ {G}. Apply
  Lemma 3.4 with *base K₁* and its extensions G and K₂: z[K₁, G; v] = −z_{K₁} and
  z[K₁, K₂; v] = z_{K₂} − z_{K₁} agree on L_{K₁}. A vertex x ∈ S(K₁) is low in K₁, so
  −1 = z_{K₂}(x) − 1 and z_{K₂}(x) = 0. Hence S(K₁) ∩ S(K₂) = ∅. This removes Lemma 4.2(a)(b)
  from the dependencies of Thm 4.4.
- **R4 (what "one card type per class" is used for).** Only (1) Lemma 2.4, (2) Cor 3.5(b),
  (3) Cor 4.5. Section 3 up to Cor 3.5(a) uses only: degrees d, d + 1 and constant b, e
  (a deck-recognizable condition). It stops there for the wider class: Cor 3.5(b) fails.
- **R5 (dependency order).** §2 → §3 → §4 (Thm 4.4, Cor 4.5) → §5 → {§6.1-6.4 independent} →
  §6.5-6.8 → §7 → §8 → §9. Lemma 4.2(b) is used only in Thm 7.2.

## 4. The corrected argument, builder-ready

Standing: n ≥ 3, (G, H) a counterexample in NF(d), 𝒦 as in §1. All sums are finite sums over
V = `Fin n`; values in ℤ until Stage E, then ℚ.

### Stage A (paper §2-§3): the eigen-relation

- **A0.** For K ∈ 𝒦 with hypomorphism σ: deg_K σx = deg_G x. Hence K has degrees in {d, d + 1},
  |U_K| = q, |L_K| = p, and K − y ≅ G − x whenever deg_K y = deg_G x. Also K ~ K′ for
  K, K′ ∈ 𝒦 (checked `found_hypomorphic_symm`, `_trans`).
- **A1 (L 2.4).** There are b, e with h_K(x) := |N_K(x) ∩ U_K| = b + θ χ_K(x) for all K ∈ 𝒦, x.
  Argument: in K − x the vertices of card-degree d + 1 are exactly U_K ∖ N_K[x] (card-degree =
  deg − [adjacent to x]), so there are q − χ_K(x) − h_K(x) of them; this number is preserved by
  card isomorphisms, and by A0 the card type depends only on deg_K x.
- **A2 (L 3.1).** K₁, K₂ ∈ 𝒦 agree off u; z, k as in §1; s = χ_{K₁}(u).
  (a) e(K₁) = e(K₂) and K₁ − u = K₂ − u give deg_{K₁} u = deg_{K₂} u, so Σ_x z(x) = 0 and
  #{z = −1} = k. For x ≠ u, deg_{K₁} x − deg_{K₂} x = z(x), so χ_{K₁} − χ_{K₂} = z (also at u).
  (b) z(x) = 1 ⇒ x ∈ U_{K₁} ∩ L_{K₂}; z(x) = −1 ⇒ x ∈ L_{K₁} ∩ U_{K₂}.
  (c) for x ≠ u: Σ_{y ~_{K₁} x} z(y) = (θ − s) z(x); and Σ_{y ~_{K₁} u} z(y) = k.
  Argument for x ≠ u: θ z(x) = h_{K₁}(x) − h_{K₂}(x)
  = Σ_y [x ~₁ y](χ₁ − χ₂)(y) + Σ_y ([x ~₁ y] − [x ~₂ y]) χ₂(y) = (A_{K₁} z)(x) + z(x) s,
  because rows x of K₁, K₂ differ only in column u, by z(x), and χ₂(u) = s.
  At u: a K₁-neighbour y of u has z(y) ∈ {0, 1}, and z(y) = 1 exactly for the k lost ones.
  (d) k = 0 ⇒ z = 0 ⇒ K₁ = K₂.
- **A3 (L 3.2).** For K ∈ 𝒦, u, and X ∈ {G, H}: K − u ≅ X − x for some x; re-attach u to the
  preimage of N_X(x). The result K_X agrees with K off u and K_X ≅ X, so K_X ∈ C_K(u). As
  G ≇ H, C_K(u) has a member ≠ K.
- **A4 (L 3.3).** K ∈ 𝒦, f : V → ℚ with A_K f = (θ − s) f, χ_K(u) = s ⇒ f(u) = 0.
  Argument: pick K′ ≠ K in C_K(u), z = z[K, K′; u], k ≥ 1. Then
  k f(u) = ⟨f, (A_K − (θ − s)) z⟩ = ⟨(A_K − (θ − s)) f, z⟩ = 0. (Symmetry: `Finset.sum_comm`
  and `G.Adj` symmetric.)
- **A5 (L 3.4, C 3.5(a)).** K₁, K₂ ∈ C_K(u) ∖ {K}, zᵢ = z[K, Kᵢ; u]: y := k₂z₁ − k₁z₂ satisfies
  A_K y = (θ − s) y by A2(c), so y = 0 on the class s of K by A4. If s = 0 pick x₀ with
  z₁(x₀) = −1 (exists by A2(a)(d); low in K by A2(b)); if s = 1 pick x₀ with z₁(x₀) = 1.
  k₂ z₁(x₀) = k₁ z₂(x₀) with z₂(x₀) ∈ {−1, 0, 1} forces z₂(x₀) = z₁(x₀) and k₁ = k₂; then
  z₁ = z₂ on the class. Hence k[X, Y; u] =: κ(u) for all X ≠ Y in C_G(u).
- **A6 (C 3.5(b)).** deg u = deg u′: an isomorphism G − u → G − u′ extended by u ↦ u′ is a
  permutation π; X ↦ X^π maps C_G(u) onto C_G(u′) and preserves k. So κ = k₀ on L, k₁ on U.

### Stage B (paper §4): exactly two extensions

For v and K ∈ C_G(v) ∖ {G} write z_K = z[G, K; v]; (∗): (A_G − λ_v) z_K = κ(v) ε_v.
By A5 the same-class part of z_K does not depend on K: for v low the gained set is one set
R₀(v) ⊆ L; for w high the lost set is one set R₁(w) ⊆ U.

- **B1 (L 4.1).** (a) v low, K at v, w high, K′ at w: compute z_Kᵀ A_G z_K′ both ways:
  ⟨z_K, z_K′⟩ = k₁ z_K(w) − k₀ z_K′(v). (b) v ≠ v′ of equal degree: z_K(v′) = z_K′(v); so
  x ∈ R₁(w) ⇔ w ∈ R₁(x), and the same for R₀.
- **B2 (L 4.2(c)).** A_G f = θ f and f = 0 on L ⇒ f(x) = f(w) for w high, x ∈ R₁(w).
  Argument: pairing (∗) at w with f: k₁ f(w) = ⟨f, z_K′⟩ = Σ_{x ∈ R₁(w)} f(x) (the gained part
  lies in L). Then Σ_{w ∈ U} Σ_{x ∈ R₁(w)} (f(x) − f(w))² = k₁Σf² − 2k₁Σf² + k₁Σf² = 0 by B1(b).
- **B3 (L 4.3; own route R3).** v low, K₁ ≠ K₂ in C_G(v) ∖ {G} ⇒ S(K₁) ∩ S(K₂) = ∅.
- **B4 (T 4.4, low case).** Suppose K₁ ≠ K₂ in C_G(v) ∖ {G}, v low. f := z_{K₁} − z_{K₂} =
  1_{S(K₁)} − 1_{S(K₂)} satisfies A_G f = θ f and f = 0 on L.
  Step 1: w ∈ S(K₁) has f(w) = 1; by B2, f = 1 on R₁(w), so R₁(w) ⊆ S(K₁) ∖ {w}: k₁ ≤ k₀ − 1.
  Step 2: pick K′ at w and let Γ := {z_K′ = −1} be the set gained by w in K′ (|Γ| = k₁,
  Γ ⊆ L ∖ N(w)); pick v′ ∈ Γ. By A6, C_G(v′) has two members M₁ ≠ M₂ other than G. z_{Mᵢ}(w) = 0. R₁(w) ∩ S(M₁) = ∅: for x in both,
  f′ := z_{M₁} − z_{M₂} has f′(x) = 1 (B3) and f′(w) = f′(x) by B2, but f′(w) = 0.
  B1(a): ⟨z_{M₁}, z_K′⟩ = k₀. Termwise the high terms vanish and the low terms are ≤ 1, nonzero
  only on Γ ∖ {v′} (z_{M₁}(v′) = 0): k₀ ≤ k₁ − 1. Contradiction with Step 1.
- **B5 (T 4.4, high case).** Apply B4 to (Ḡ, H̄): NF(n − 2 − d), low/high swapped, and
  C_Ḡ(v) = {K̄ : K ∈ C_G(v)}.
- **B6 (C 4.5).** C_G(u) = {G, alt(u)}, alt(u) ≅ H. For any isomorphism α : G − u → G − u′
  the permutation π = α ∪ {u ↦ u′} has G^π ∈ C_G(u′), G^π ≅ G ≇ alt(u′), so G^π = G:
  **every card isomorphism extends to an automorphism.** Hence Aut(G) is transitive on L and
  on U, alt(πu) = alt(u)^π and z_{πu}(πx) = z_u(x).

### Stage C (paper §5): identities for z_u

- **C1 (L 5.1).** (a) R₀, R₁ symmetric (B1(b)). (b) z_v z_w ≥ 0 pointwise, so
  |S₀(v) ∩ R₁(w)| + |R₀(v) ∩ S₁(w)| = ⟨z_v, z_w⟩ = k₁[w ∈ S₀(v)] + k₀[v ∈ S₁(w)].
  (c) column sums γ of D₀ and row sums δ of D₁ are constant by B6; pk₀ = qγ, qk₁ = pδ,
  γδ = k₀k₁, δ ≥ 1.
- **C2 (L 5.2).** k₁ − k₀ = θ. (≥) w high, v ∈ S₁(w): ⟨z_v, z_w⟩ = k₀, (A_G z_w)(v) = 1 − θ,
  so ⟨a_G(v) − z_v, z_w⟩ = 1 − θ − k₀ ≥ −(k₁ − 1) (the vector a_G(v) − z_v is 0/1 and vanishes
  at v ∈ S₁(w)). (≤) v low, w ∈ S₀(v): ⟨z_v, z_w⟩ = k₁, (A_G z_v)(w) = θ, so
  ⟨a_G(w) − z_w, z_v⟩ = θ − k₁ ≥ −k₀.
- **C3 (P 5.3).** With σ₀ = [w ∈ S₀(v)], σ₁ = [v ∈ S₁(w)]:
  (R₀D₃ + D₀E₁)(v,w) = k₀ − |R₀(v) ∩ N(w)| − |R₀(v) ∩ S₁(w)| + |S₀(v) ∩ N(w)| − |S₀(v) ∩ R₁(w)|
  = k₀ + θσ₀ − (k₁σ₀ + k₀σ₁) = k₀(1 − σ₀ − σ₁), using (A_G z_v)(w) = θσ₀, C1(b), C2.
  (E₀D₁ + D₂R₁)(v,w) = k₁ − σ₁ − (θ − 1)σ₁ − (k₁σ₀ + k₀σ₁) = k₁(1 − σ₀ − σ₁), using
  (A_G z_w)(v) = −(θ − 1)σ₁.

### Stage D (paper §6.1-6.4): module switch, independent of everything above

- **D1 (T 6.4).** G ~ K on n vertices, B ⊊ V a module of G, G and K agree on every pair not
  inside B ⇒ G ≅ K.
  Lean-friendly form of the paper's induction (own rewording, unlabelled): for m < n and F on
  m vertices, N_G(F) := #{T ⊆ B : G[T] ≅ F} equals N_K(F). Induction on m: split the copies S
  of F in G by S′ = S ∖ B. For S′ = ∅ the count is N_G(F). For S′ ≠ ∅ the type of G[T ∪ S′]
  depends only on the type of G[T], on S′ and on G off B (B is a module), |T| < m, and by the
  induction hypothesis there is a type-preserving bijection T ↦ T′ between the |T|-subsets
  of B for G and for K. Kelly's lemma equates the totals. With F = G[B]: K[B] ≅ G[B] by φ;
  φ ∪ id is an isomorphism G → K.

### Stage E (paper §6.5-6.8): the switching graph is connected

- **E1 (L 6.5).** Σ_u f(u) z_u = 0. Apply A_G − θ and (∗∗): Σ_{u ∈ U} f(u) z_u(y) = k_y f(y) and
  Σ_{u ∈ L} f(u) z_u(y) = −k_y f(y). Read off the four identities.
- **E2 (L 6.7).** φ = f_L, h = −(δ/k₀) f_U: D₁h = δφ, D₀ᵀφ = γh, R₀φ = k₀φ, R₁h = k₁h.
  E_{D₀} = k₀‖φ‖² − γ‖h‖², E_{D₁} = k₁‖h‖² − δ‖φ‖², δE_{D₀} + k₀E_{D₁} = 0, both ≥ 0, so
  g = (φ, h) is equal across D₀- and D₁-edges; R₀-, R₁-edges by the second quadratic form.
- **E3 (T 6.8).** Let B be a T-component (Lean: a minimal nonempty T-closed set, so that a
  function constant across T-edges is constant on B), B ≠ V. Z_B := (z_u(x))_{x,u ∈ B}.
  Right kernel ⊆ ℚξ by E2. Hence the left kernel has dimension ≤ 1 and contains 1_B
  (Σ_x z_u(x) = 0, supp z_u ⊆ B), so it is ℚ1_B. For i ∉ B, u ∈ B: (A_G z_u)(i) = 0, so the row
  (A_G(i, x))_{x ∈ B} is in the left kernel, hence constant: B is a module. G and alt(u) agree
  off B, so D1 gives alt(u) ≅ G, contradicting alt(u) ≅ H.

### Stage F (paper §7-§8)

WLOG θ ≤ 0 (else pass to (Ḡ, H̄)); then k₁ ≤ k₀.

- **F1 (L 4.2(a)(b)).** A_G f = θ f ⇒ f = 0 on L (A4 with K = G), and f is constant on S₀(v):
  with K = alt(v), z = z_v, C = ⟨z, f⟩: (A_K − θ) f = −C ε_v (rows x ≠ v change by −z(x) f(v) = 0)
  and (A_K − θ)(−z) = k₀ ε_v, so g = k₀ f − C z is a θ-eigenvector of A_K, zero on L_K ⊇ S₀(v)
  by A4 for K. So f = C/k₀ on S₀(v).
- **F2 (L 7.1).** v ∈ S₁(w) ⇒ S₀(v) ∩ R₁(w) ≠ ∅ (else k₀ = |R₀(v) ∩ S₁(w)| ≤ k₁ − 1).
- **F3 (T 7.2).** A_G f = θ f ⇒ f = 0. val := f on U, f(s(v)) on L for a chosen s(v) ∈ S₀(v).
  val is equal across each T-edge type: D₀ (F1), R₁ (B2), D₁ (F2 with F1, B2), R₀ (c ∈ R₀(v):
  pick w with c ∈ S₁(w) by δ ≥ 1; ⟨z_v, z_w⟩ ≥ 1, so w ∈ S₀(v) or v ∈ S₁(w)). E3: f ≡ C on U,
  0 on L; at a low vertex 0 = bC with b ≥ k₀ ≥ 1.
- **F4 (L 8.1).** R₁g = k₁g ⇒ W := Σ_{u ∈ U} g(u) z_u − (1/k₀) Σ_{u ∈ L} (D₁g)(u) z_u satisfies
  (A_G − θ) W = 0, so W = 0 (F3), and E1 gives D₀ᵀD₁g = k₀k₁g, R₀D₁g = k₀D₁g.
- **F5 (T 8.2).** R₁ is connected: for a component C, φ_C := D₁1_C; X := {φ_C > 0};
  (i) φ_C(u) > 0 ⇒ S₀(u) ⊆ C (from D₀ᵀφ_C = k₀k₁1_C); (ii) φ_C constant across R₀-edges.
  C ∪ X is T-closed (four cases, using (i), (ii) for C and for U ∖ C); E3 gives C = U.
- **F6 (T 8.3).** L_i an R₀-component, φ(y) := #{u ∈ L_i : y ∈ S₀(u)}. Summing C1(b) over
  u ∈ L_i: R₁φ = k₁φ, so φ is constant (F5) and positive (Σφ = k₀|L_i|).

### Stage G (paper §9)

- **G1 (T 9.1).** Ωᵢ = supp Dᵢ. Steps: (v,w) → (v′,w), v′ ∈ R₀(v); (v,w) → (v,w′), w′ ∈ R₁(w).
  O1: Ω₁ --R₀→ Ω₀ ∪ Ω₁ (C1(b)). O2: Ω₀ --R₀→ not Ω₃ (C3(a)). O3: Ω₀ --R₁→ Ω₀ ∪ Ω₁ (C1(b)).
  O4: Ω₂ --R₁→ not Ω₀ (C1(b)). O5: Ω₂ --R₁→ not Ω₁ (C3(b)). Claim: Ω₀ --R₀→ Ω₀ ∪ Ω₁: otherwise
  (v′,w) ∈ Ω₂; walk w = x₀, …, x_m = w₀ in R₁ (F5) to some (v′,w₀) ∈ Ω₀, keeping
  (v,xᵢ) ∈ Ω₀, (v′,xᵢ) ∈ Ω₂ by O1-O5; contradiction at i = m. F6 then puts every (v,w) in
  Ω₀ ∪ Ω₁.
- **G2 (L 9.2).** F m-regular, cards F − v (v ≠ r) pairwise isomorphic. A card isomorphism
  F − v → F − w maps the vertices of card-degree m − 1 onto each other, so it extends to an
  automorphism π, πv = w. If some π moves r, F − r ≅ F − πr. Otherwise r ~ v ⇔ r ~ w for all
  v, w ≠ r, F is complete or empty, and all cards are isomorphic.
- **G3 (T 9.3).** D₂ = 0: S₀(v) = N(v) ∩ U, k₀ = b. D₃ = 0: S₁(w) = L ∖ N(w), k₁ = p − c.
  C2: p = c + e = d + 1. Then R₀(v) = L ∖ N[v] and R₁(w) = N(w) ∩ U by cardinality, so in
  alt(u) the vertex u is joined exactly to L ∖ {u}. F := G plus a new vertex r joined to L is
  (d + 1)-regular, F − r = G, F − v ≅ alt(v) ≅ H for all v ∈ V. G2: G ≅ H. Contradiction.

## 5. What breaks outside finite simple graphs

- **Tournaments / digraphs (Stockmeyer 1977, 1981; bibliographic details UNVERIFIED here).**
  1. *Lemma 2.1.* e(D) − e(D − v) is the total degree; for a tournament it is n − 1 for every
     v. The card does not determine the score. Tested (`debe_zinchenko_tournament_check.py`,
     exhaustive n = 4, 5, 6): the deck classes with non-isomorphic members are 1, 1, 4; the
     only one with t = 2 is the n = 4 pair "3-cycle plus a source / plus a sink", with score
     sequences (1,1,1,3) and (0,2,2,2); every n = 5, 6 class has a member with two isomorphic
     cards at vertices of different scores. Stockmeyer's B_k, C_k have t = 3, 9, 17 for
     k = 2, 3, 4, so the audit by "a Stockmeyer pair with t = 2" proposed in D1 has no instance
     there.
  2. *Lemma 3.3 / 3.4.* For a tournament with scores d, d + 1 and constant numbers of high
     out-neighbours, the relation (A − (θ − s)) z = k ε_u still holds (own computation, with
     A(x, y) = [x → y] and z the difference of the out-rows at u; the scores then change by
     −z). Lemma 3.3 then gives f(u) = 0 only for *left*
     eigenvectors; Lemma 3.4 applies it to the *right* kernel vector k₂z₁ − k₁z₂. This is the
     first place where the paper's conclusion is lost. Symbolic only: no tournament with an
     extension of this kind exists for n ≤ 6 (Part 3 of the script is vacuous).
  3. *Lemma 4.1, 4.2(c)* use z_Kᵀ A z_K′ = z_K′ᵀ A z_K.
- **3-uniform hypergraphs (Kocay 1987; UNVERIFIED here).** Degrees are still recognizable,
  but the card-degree of x drops by the codegree of {x, v}, not by a bit; Lemma 2.2 and the
  normal form fail, and there is no symmetric 0/1 matrix with A χ = b·1 + θ χ.
- **Infinite graphs.** Lemma 2.1 (edge counting), Kelly's lemma in Lemma 6.1 and the rank step
  of Thm 6.8 are finite.

## 6. Reformulation and Lean statements (all bodies below elaborate)

Scratch file: `lean/Recon/Scratch/conj_kelly_ulam__connected_dominating_or_diam2/debe_zinchenko_stmt.lean`.

**A, the paper's theorem (t ≤ 2).**
```lean
Recon.ClassReconstructible (fun n G => ∃ a b : Fin n, ∀ x : Fin n, Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({a}ᶜ : Set (Fin n))) ∨ Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({b}ᶜ : Set (Fin n))))
```
**B, normal form** (A follows from B and the checked `pure_degree_class`, about 100-150 lines).
```lean
Recon.ClassReconstructible (fun n G => (∃ d : ℕ, ∀ x : Fin n, (G.neighborSet x).ncard = d ∨ (G.neighborSet x).ncard = d + 1) ∧ ∀ x y : Fin n, (G.neighborSet x).ncard = (G.neighborSet y).ncard → Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({y}ᶜ : Set (Fin n))))
```
**N, the cheaper narrow class (own; Stages A-B only).** Normal form plus a card isomorphism
that does not extend:
```lean
Recon.ClassReconstructible (fun n G => (∃ d : ℕ, ∀ x : Fin n, (G.neighborSet x).ncard = d ∨ (G.neighborSet x).ncard = d + 1) ∧ (∀ x y : Fin n, (G.neighborSet x).ncard = (G.neighborSet y).ncard → Nonempty (G.induce ({x}ᶜ : Set (Fin n)) ≃g G.induce ({y}ᶜ : Set (Fin n)))) ∧ ∃ u u' : Fin n, ∃ α : G.induce ({u}ᶜ : Set (Fin n)) ≃g G.induce ({u'}ᶜ : Set (Fin n)), ∃ x : ({u}ᶜ : Set (Fin n)), G.Adj u x.1 ∧ ¬ G.Adj u' (α x).1)
```
Paper argument for N from B4/B5: let H ~ G, H ≇ G. X := G − u′ with u′ re-attached to
α(N(u)) is isomorphic to G, lies in C_G(u′), and X ≠ G because α(x) ∉ N(u′). alt ≅ H is a
third member of C_G(u′). This contradicts |C_G(u′)| = 2.
**E, the complement of N inside B** (same as N with the last clause replaced by
`∀ u u' α x, G.Adj u x.1 → G.Adj u' (α x).1`). B is N ∪ E by excluded middle.
**M, module switch (T 6.4), holds for every n:**
```lean
∀ n : ℕ, ∀ G K : SimpleGraph (Fin n), Recon.Hypomorphic G K → ∀ B : Set (Fin n), B ≠ Set.univ → (∀ x : Fin n, x ∉ B → ∀ b b' : Fin n, b ∈ B → b' ∈ B → (G.Adj x b ↔ G.Adj x b')) → (∀ x y : Fin n, ¬ (x ∈ B ∧ y ∈ B) → (G.Adj x y ↔ K.Adj x y)) → Nonempty (G ≃g K)
```
**R, regular graphs with all cards but one isomorphic (L 9.2), holds for every n:**
```lean
∀ n : ℕ, ∀ F : SimpleGraph (Fin n), ∀ m : ℕ, (∀ x : Fin n, (F.neighborSet x).ncard = m) → ∀ r : Fin n, (∀ v w : Fin n, v ≠ r → w ≠ r → Nonempty (F.induce ({v}ᶜ : Set (Fin n)) ≃g F.induce ({w}ᶜ : Set (Fin n)))) → ∀ v : Fin n, Nonempty (F.induce ({r}ᶜ : Set (Fin n)) ≃g F.induce ({v}ᶜ : Set (Fin n)))
```

Suggested tree (for the reducer; names are placeholders): a step with body A (or B) reduced to
{N, E}; E later reduced to {M, R, core}, where the proof of the core imports the helpers of the
checked N file (Stage A-B lemmas), which the gate allows. N is the tracer bullet.

**Is a class restricted to the residual's shape cheaper?** No. Connectedness, the dominating
edge, diameter 2 and "no gluing pair" are not used anywhere in Stages A-G; "no pure degree
class" only replaces Prop 2.3(i), the cheapest part. The saving comes from N, not from the
residual's shape.

**How much of the residual this covers (tested, evidence only).** The three known D2 members
with t = 2 are in B, have Aut(G) transitive on both degree classes, and |Aut(G − v)| /
|Aut(G)_v| = 4/2, 2/1, 2/1, so they are in N. Each has exactly one re-attachment K ≠ G at each
vertex with the same (d, b, e), and it is isomorphic to G. The other three known members have
t = 5, 5, 6 and are untouched. Class sizes, exhaustive (`debe_zinchenko_stats.py`): n = 7:
A 42, B 12, N 10, E 2 of 1044; n = 6: A 36, B 12, N 10, E 2 of 156. With G and Ḡ connected:
B has 4 graphs at n = 6 and none at n = 7. The class is thin, like the regular graphs.

## 7. Lean route

Checked lemmas that carry it:
- T0: `L_kelly_edge_count`, `L_kelly_card_edges_add_degree`, helpers `card_add_deg`, `ncard_iso`
  (in `L_…__pure_degree_class`).
- card-degree: `deg_in_card`, `bit_law`; re-attachment: `iso_of_nbhd` (returns `Nonempty`; for
  B6 the explicit map is needed: `extE`, `extE_adj` in `L_…__unique_copy_gluing`).
- 𝒦: `L_found_hypomorphic_symm`, `_trans`, `_iso_invariant`, `L_found_iso_hypomorphic`.
- complement (B5 and the WLOG of Stage F): `L_found_hypomorphic_compl`, helpers `iso_compl`,
  `card_compl_iso` (in `L_found_reconstructible_compl`); Mathlib `SimpleGraph.degree_compl`.
- Stage D: `L_conj_kelly_ulam__disconnected__kelly_induced_count`; `match_fibres`
  (in `L_…__iso_of_component_counts`) for the type-preserving bijection.
- degenerate cases of A: `L_…__pure_degree_class` itself.

Mathlib (found by grep in the pinned tree): `SimpleGraph.induce`, `SimpleGraph.neighborSet`,
`SimpleGraph.ncard_neighborSet`, `SimpleGraph.degree_compl`,
`SimpleGraph.card_edgeFinset_induce_compl_singleton`, `SimpleGraph.adjMatrix`,
`SimpleGraph.adjMatrix_mulVec_apply`, `SimpleGraph.isSymm_adjMatrix`,
`SimpleGraph.transpose_adjMatrix`, `SimpleGraph.dotProduct_mulVec_adjMatrix`,
`Matrix.dotProduct_mulVec`, `Matrix.mulVec_transpose`, `dotProduct_comm`,
`Matrix.rank_transpose`, `LinearMap.finrank_range_add_finrank_ker`, `finrank_le_one_iff`,
`SimpleGraph.Reachable`, `SimpleGraph.comap` / `SimpleGraph.map`. `Finset.sum_comm` and a
`sum_boole`-style lemma were not located by exact name; the builder should grep.

Design advice:
- Write A_K f as `∑ y, if K.Adj x y then f y else 0` over `Fin n → ℚ` (or ℤ in Stages A-C) and
  use `adjMatrix` only for the rank step E3. Lemma A4 is then `Finset.sum_comm` plus `K.symm`.
- 𝒦 as `{K : SimpleGraph (Fin n) | Recon.Hypomorphic G K}`; "agree off u" as
  `∀ x y, x ≠ u → y ≠ u → (K.Adj x y ↔ K'.Adj x y)`.
- Do the low case for an arbitrary counterexample pair and transfer by complement once.
- T-connectedness as "the only nonempty T-closed set is V"; this is the form F3 and F5 use.
- G3: build F on `Option (Fin n)`; state G2 for a general `Fintype`.

Estimated size (lines of Lean, wide error bars):

| Stage | Content | Lines |
|---|---|---|
| A | A0-A6, incl. Lemma 2.4 for every K ∈ 𝒦 | 700-1000 |
| B | B1-B6, incl. the complement transfer | 700-1100 |
| reduction of class A/N to B4-B5 | | 100-150 |
| **N total** | | **1500-2200** |
| C | C1-C3 | 400-600 |
| D | module switch | 500-800 |
| E | E1-E3 with the rank step | 400-600 |
| F | F1-F6 | 400-600 |
| G | G1 200-300; G2-G3 with F 350-550 | 550-850 |
| **full total** | | **3700-5600** |

Main difficulty: no single hard step. (1) Lemma 2.4 for all K ∈ 𝒦 needs degree counts in
cards transported along card isomorphisms on subtypes. (2) The module switch needs a count
over subsets split by a module. (3) B6 needs explicit automorphisms and the equivariance of
z_u. (4) Two complement transfers. The earlier guess of 1500-3000 lines in D1 fits N, not the
full theorem.

## 8. Extensions

- **t(G) = 3: no argument.** Three sub-cases: three degrees with one card type each; two
  degrees with one class carrying two card types (then b or e is not constant and Lemma 2.4
  fails); regular with three types (regular graphs fall under the checked `pure_degree_class`
  by the bit law). Nothing in the paper handles the first two.
- **One card type per degree class, r ≥ 3 degrees: no argument.** What I can derive (own):
  1. *Equitable.* For v of degree dᵢ the card G − v has n_m − [dᵢ = m] − β_m(v) + β_{m+1}(v)
     vertices of degree m, β_m(v) = number of neighbours of degree m. Equal card types and
     downward induction on m give β_m constant on each degree class, with the same quotient
     matrix B = (b_{ij}) for every K ~ G.
  2. *Relation off u.* For K₁, K₂ agreeing off u and c ∈ ℚ^r put ζ_c(x) = c(deg_{K₁} x) −
     c(deg_{K₂} x). Then for x ≠ u: (A_{K₁} ζ_c)(x) = ζ_{M_u c}(x), M_u c := B(c − c(deg u)·1).
     For r = 2 the space of ζ_c is a line and this is Lemma 3.1(c).
  3. *Where it stops.* For r ≥ 3, M_u acts on an (r − 1)-dimensional space; its eigenvalues
     need not be rational; the coefficient at u, Σ_{y lost} (c(deg y) − c(deg y − 1)), can
     vanish; and Lemma 3.4's sign argument (lost vertices high, gained vertices low, so the
     class of u carries a nonzero entry of z) has no analogue. I do not have a replacement.
- **Two degrees d, d + 1 with constant b, e but several card types per class.** Stage A up to
  A5 goes through verbatim (R4). A6 fails, and with it B4. No argument beyond A5.

## 9. Where this could break

- The audit is a paper reading by one agent. The paper is unrefereed and I found no second
  source. Every step was recomputed, and the identities of §§3-5 were also tested on real
  graphs, but the later stages (E-G) are statements about a hypothetical counterexample and
  cannot be tested: they rest on the reading alone.
- Stage D: I reworded the paper's labelled-embedding induction into an unlabelled count. The
  census form was tested (n ≤ 6), the rewording itself was not formalized.
- R3 (Lemma 4.3 from 3.4) is my shortcut; if a builder doubts it, the paper's route through
  Lemma 4.2(a)(b) is available.
- The WLOG θ ≤ 0 and the high case of Thm 4.4 both go through the complement. A builder must
  transfer the *whole* counterexample structure (NF, 𝒦, extensions), not only hypomorphism.
- The three t = 2 residual members lie in N by a computation on three graphs; "t = 2 residual
  members are always in N" is not claimed.
- Thm 6.4 looks like a known kind of statement (modules and reconstruction: Brignall-Georgiou-
  Waters 2012, item D2 of `options_logic_topology.md`), but I did not find it stated there;
  relation UNVERIFIED.

## 10. Tests run (evidence only; all in this directory)

- `debe_zinchenko_claims.py` via `tools/search/small_graphs.py counterexample`: relaxed
  single-graph forms of L 2.4, L 3.1(c), L 3.3, L 3.4, L 9.2 and the endgame T 9.3.
  NO WITNESS, exhaustive n = 3..7 (1249 graphs; 35 two-degree equitable graphs, 31 with an
  extension, 122 pairs of extensions, 314 instances of the L 3.4 vanishing, 113 (F, r)
  instances of L 9.2, 23 of T 9.3), plus 496 random two-degree equitable graphs on 8-12
  vertices (292 with an extension) for L 3.1(c), 3.3, 3.4.
- `debe_zinchenko_model_check.py`: L 4.1(a)(b), L 5.1(a)(b), L 5.2, P 5.3 on the 6 graphs
  found that carry an extension at every vertex: the three residual members, Petersen − v,
  Paley(13) − v, and P₄ = C₅ − v (the only such graph with n ≤ 7). All hold. These identities
  use the counterexample only through the relation (∗∗), which is why real graphs can carry
  them.
- `debe_zinchenko_module_check.py`: census form of L 6.3(b), exhaustive n = 4, 5, 6
  (118544 triples (G, B, K) at n = 6). NO WITNESS.
- `debe_zinchenko_tournament_check.py`: §5.
- `debe_zinchenko_stats.py`: class sizes of §6.
