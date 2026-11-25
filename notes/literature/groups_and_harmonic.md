# Groups, representations and harmonic analysis: literature sweep

Librarian sweep, 2026-11-25. Angle: reconstruction as a problem about S_n-orbits; group-action
reconstruction (Nash-Williams lemma, Alon–Caro–Krasikov–Roditty, Mnukhin, Maynard–Siemons);
abelian Fourier methods (Radcliffe–Scott, Pebody); linear-algebra/Fourier methods (Stanley's
switching, Gottlieb–Kantor inclusion matrices); invariant theory (Pouzet, Thiéry, Dufresne et
al. 2026); linear-algebraic equivalents (Oliveira–Thatte).

Vocabulary: nothing here is checked. Statements quoted from papers are literature; my own
derivations are marked **[derived]** with the small-graph evidence I ran (evidence, not results).
"Verified" means I read the statement in the paper's own text (PDF/scan) during this sweep.

## Summary

1. Group-action reconstruction theory (Nash-Williams lemma; ACKR 1989; Mnukhin 1992; Maynard–Siemons 2002/05) is a complete framework for **edge** reconstruction: ERC is exactly "S_n acting on 2-subsets has reconstruction index ≤ 4". Lovász (m > N/2) is its linear part and Müller (2^{m−1} > n!) its counting part. Both arguments hold for **every** finite group action.
2. **Vertex** reconstruction is not a subset-deck problem for one fixed action. Its exact S_n-formulation (**[derived]**, evidence n ≤ 5) says the deck is the pushforward of the uniform measure on the orbit O_G along "delete vertex n", up to scalar. The linear map behind it has a large kernel (g(n) > Σ_{k<n} g(k)), so no Lovász/Stanley-type linear injectivity can work. Any proof must use the fact that the input is a single orbit (point mass).
3. Known exact algebraic equivalents: (a) Oliveira–Thatte: RC at order n ⇔ some Kocay covering-number matrix has rank ψ(n); (b) Kelly-count separation. One invariant-theoretic sufficient condition, Pouzet's generation conjecture, is false for 11 ≤ n ≤ 18 (Thiéry, as reported). The weaker separating-set version is open.
4. Abelian harmonic analysis (Radcliffe–Scott; Pebody: every subset of Z_n is determined by its 6-deck; Stanley switching for n ≢ 0 mod 4) succeeds because the relevant operator is diagonal in characters. Nothing comparable exists for S_n, and these methods generalize to settings where vertex reconstruction fails. They are tools, not routes.
5. Best formalizable payload: an abstract Nash-Williams/ACKR engine for finite `MulAction`s, the induced-subset Kelly lemma (k-deck), and the orbit-pushforward equivalence. All three Props elaborate against `Recon.Basic` (probe only, not a submission).

## Sources

Format: citation; statement; proof idea; verification; failing settings (T = tournaments/digraphs,
H = k-uniform hypergraphs k ≥ 3, I = infinite graphs); Lean difficulty.

### S1. Alon, Caro, Krasikov, Roditty, "Combinatorial reconstruction problems"
J. Combin. Theory Ser. B 47 (1989) 153–161. doi:10.1016/0095-8956(89)90016-6.
Verified from the scanned paper: <https://www.tau.ac.il/~nogaa/PDFS/Publications2/Combinatorial%20reconstruction%20problems.pdf>.

- **Setting.**
  - A group G (finite or infinite) acts on a set X.
  - For Y ⊆ X with |Y| = m > k, the *k-deck* d_{Y,k}(r) counts the (m−k)-subsets of Y that are G-equivalent to r. Note: k counts the deleted elements.
- **Theorem 2.1.** Let Y (|Y| = m) be non-reconstructible from its k-deck, and let S ⊆ Y with |S| = t and |G_S| < ∞, where m − k ≥ t. Then there are a T with S ⊆ T ⊆ Y, |T| ≥ m − k + 1, and an ε ∈ {0,1} such that: for every K with S ⊆ K ⊆ T and |K| ≡ ε (mod 2), there is a g ∈ G with T ∩ gY = K.
- **Corollary 2.4.** Let G be finite. If 2^{m−k} > |G|/|G_Y|, then Y is reconstructible from its k-deck. In particular, if 2^{m−k} > |G|, every m-subset is.
- **Corollary 2.5.** A refinement using a subset S with finite stabilizer: if 2^{m−k−t} > |Y^{G_S}|·C(m,t), then Y is reconstructible.
- **Applications (§3).**
  - With t = 1, Corollary 2.5 gives a graph with m edges edge-reconstructible if 2^{m−2} > m·2·(n−2)!, slightly better than Müller.
  - Prop 3.1: a connected graph is k-edge-reconstructible if 2^{m−k−n+1} > n·Δ!(Δ−1)^{n−Δ−1}, using spanning trees.
  - Hypergraphs: every hypergraph with 2^{m−1} > n! is edge-reconstructible.
  - **A vertex-reconstruction application** (p. 158). Let G be 2-connected bipartite with classes A and B, where |B| ≥ 1 + log₂(|A|!) and the vertices of B have distinct neighbourhoods. Then G is vertex-reconstructible, via edge reconstruction of the hypergraph H(G) on A whose edges are the neighbourhoods of B ("one can easily check" the recognition step; I did not check it).
  - Cycle colourings.
  - Plane point sets: m > 8 points are determined by their vertex-deleted subpolygons.
- **Proof idea.**
  - Let f(A) = f₁(A) − f₂(A), where f_i(A) counts the images of Y and of Y′ that contain A.
  - f vanishes on all sets with |A| ≤ m − k, by the deck plus a Kelly-type count.
  - Take T minimal with f(T) ≠ 0. Inclusion–exclusion over S ⊆ K ⊆ T gives #{g : gY ∩ T = K} − #{g : gY′ ∩ T = K} = (−1)^{|T−K|}·b, so every K of one parity is realized.
  - Counting those realizations against |G| gives the corollaries.
- **Failing settings.**
  - Valid for **every** group action, including S_n on ordered pairs (digraph edge reconstruction) and on k-sets (hypergraph edge reconstruction).
  - There is no conflict with Stockmeyer or Kocay, which are *vertex* counterexamples.
  - I: needs |G_S| < ∞, so it says nothing about infinite graphs with infinite stabilizers.
  - Consequence: this tool cannot by itself separate graphs from hypergraphs. It is a size/automorphism-count bound, not a structural route to vertex reconstruction.
- **Lean.** Medium–hard (300–700 lines). Needs Finset inclusion–exclusion and Finset images under `MulAction`. See candidate C.

### S2. C. St. J. A. Nash-Williams, "The reconstruction problem"
In: Beineke & Wilson (eds.), *Selected Topics in Graph Theory*, Academic Press 1978, pp. 205–236. Citation verified from the ACKR and Maynard–Siemons reference lists. The text was not read: **UNVERIFIED** beyond the lemma below.

- **Nash-Williams lemma, group form**, as stated in Maynard–Siemons 2005, Lemma 2.1 (verified there). G acts on Ω of any cardinality. Suppose Δ ⊂ Ω is not reconstructible (one-element-deleted deck) and S ⊆ Δ has finite setwise stabilizer. Then for every K with S ⊆ K ⊆ Δ and |K| ≡ |Δ| (mod 2), some g ∈ G has Δ ∩ Δg = K.
- For graphs (Ω = pairs, G = S_n) this is the classical lemma behind Müller's bound.
- **Lean.** As for S1. It is the same engine.

### S3. L. Lovász, "A note on the line reconstruction problem"
J. Combin. Theory Ser. B 13 (1972) 309–310. V. Müller, "The edge reconstruction hypothesis is true for graphs with more than n·log₂n edges", J. Combin. Theory Ser. B 22 (1977) 281–283.

- Citations verified via the ACKR and Thatte reference lists. ACKR p. 154 restates both results (verified there):
  - **Lovász:** ERC holds for m > ½·C(n,2).
  - **Müller:** ERC holds when 2^{m−1} > n!.
- This settles the CLAUDE.md §3 UNVERIFIED flag for both statements (secondary source: ACKR's own text). The originals were not read.
- **Group view [derived, standard].**
  - Let N = C(n,2) and let W be the inclusion matrix between (m−1)-subsets and m-subsets of the N pairs.
  - By Gottlieb–Kantor (S10) and complementation, Wᵀ is injective on functions of m-subsets iff m ≥ (N+1)/2, i.e. m > N/2. It is then injective on S_n-invariant functions too.
  - So Lovász's bound is **exactly the linear-injectivity threshold** for any group.
  - Müller's bound is the counting (Nash-Williams) part, and it depends on |Γ| = n!.
- **Failing settings.** Both hold verbatim for hypergraph and digraph *edge* reconstruction.
- **Lean.** Lovász via inclusion–exclusion: medium (Mathlib `Finset.inclusion_exclusion_*`). Müller: corollary of candidate C plus |Perm (Fin n)| = n!.
- **Repo gap:** `Basic.lean` has no edge deck (see Open gaps).

### S4. V. B. Mnukhin
- "Reconstruction of k-orbits of a permutation group", Mat. Zametki 42(6) (1987) 863–872 (Russian). Citation from mathnet/geodesic; content **UNVERIFIED**. A search summary says it gives a sufficient condition generalizing Lovász and Müller.
- "The k-orbit reconstruction and the orbit algebra", Acta Appl. Math. 29 (1992) 83–117, doi:10.1007/BF00053380. Statement from the zbMATH review (via MaRDI), not the paper:
  - The orbit (k-orbit) reconstruction problem for (G, Ω) contains ERC as the case "pair symmetric group".
  - The reconstruction index ρ(G) is defined.
  - The orbit algebra C^G is commutative with the orbit sums as a basis.
  - A co-orbit algebra A^G is introduced, and a set of invariants is complete iff it generates A^G.
  - The review says the conjectured value for the pair group is ρ = 3 (Mnukhin's convention: all k-orbits with k > ρ are reconstructible).
- **Failing settings.** General framework; it contains reconstructible and non-reconstructible actions alike.
- **Lean.** Framework only. The orbit algebra needs `MonoidAlgebra` plus invariants, which Mathlib has in pieces (`RepresentationTheory/Invariants.lean`). Hard and unmotivated without a target theorem.

### S5. P. Maynard, J. Siemons
- "On the reconstruction index of permutation groups: general bounds", Aequationes Math. 70 (2005) 225–239, doi:10.1007/s00010-005-2799-1. Verified from the full text (UEA eprint 17486).
- Companion: "... semiregular groups", Aequationes Math. 64 (2002) 218–231 (citation from that paper; content **UNVERIFIED**).
- **Definitions (verified).**
  - Δ, Δ′ ⊆ Ω are *hypomorphic* if some bijection h : Δ → Δ′ has Δ∖{δ} ≈ Δ′∖{h(δ)} under G.
  - ρ(G, Ω) is the least r such that every set of ≥ r elements is reconstructible.
- **Lemma 2.2.** If Δ is non-reconstructible and S ⊆ Δ, then 2^{|Δ|−|S|−1}·|G_{Δ}| ≤ C(|Δ|,|S|)·|S|!·|G_S|.
- **Theorem 2.6.** If some S ⊆ Δ has β(|S|) ≤ |Δ|, |G_S| < ∞ and |G_S| ≤ |G_{Δ}|, then Δ is reconstructible. Here β(s) is the least b > s with 2^{b−s−1} > C(b,s)·s!, so β(1) = 5, β(2) = 10, β(3) = 16, and β(s) ~ s(1 + log₂ s).
- **Corollary 2.7.** Any set containing a base B with |Δ| ≥ β(|B|) is reconstructible.
- **Consequences.**
  - Semiregular actions have ρ ∈ {3, 4, 5}.
  - Groups with trivial two-point stabilizers have ρ ≤ 6.
  - The text says ρ "lies between 2 and about half of the degree", and imprimitive wreath products attain the upper extreme.
- **Failing settings / significance.**
  - Some permutation groups have non-reconstructible sets of size ≈ |Ω|/2. So **no argument that uses only "Γ is a finite permutation group" can beat Lovász's N/2**: any ERC proof must use the specific action of S_n on pairs.
  - The authors note it "would be extremely useful to dispose of the condition |G_S| < ∞". Infinite stabilizers are exactly where Fisher and Bowler et al. live (I).
- **Lean.** Lemma 2.2 / Theorem 2.6 follow from candidate C plus orbit–stabilizer. Medium on top of C.

### S6. B. D. Thatte, "G-reconstruction of graphs"
Ars Combin. 54 (2000) 293–299; arXiv:math/0608071. Verified from the arXiv text.

- **Lemma 1** (a general Nash-Williams lemma). If X and Y are G-edge-hypomorphic but not G-isomorphic, then for every spanning F ⊆ X: |X →_G X|_F − |Y →_G X|_F = (−1)^{m−|E(F)|}·|G ∩ Aut X|.
- **Prop 2.** A 2-edge-connected bipartite graph with parts s and t is edge-reconstructible if m > st/2 or 2^{m−1} > |Aut K_{s,t}|.
- **Key negative fact (verified).** "A 2k-vertex path, k ≥ 2, is not A_{2k}-edge reconstructible."
  - So G-edge reconstruction **fails for some subgroups G ≤ S_n**, even for paths.
  - Any argument that would work for every subgroup of S_n is broken.
- Thatte, "On the Nash-Williams' lemma in graph reconstruction theory", JCTB 58 (1993) 280–290. Citation from Thatte's reference list; content **UNVERIFIED**.
- **Lean.** Edge deck again; it reduces to candidate C with Γ ≤ Perm.

### S7. B. D. Thatte, "A reconstruction problem related to balance equations I"
Discrete Math. 176 (1997) 279–284; arXiv:math/0608080. Abstract only (verified):
- Krasikov–Roditty's modified k-decks give an independent proof of Müller.
- Thatte answers the k = 1 question (per the abstract).
- Two new proofs of Lovász, one via eigenvalues of Johnson graphs.

Related: I. Krasikov, Y. Roditty, "Balance equations for reconstruction problems", Arch. Math. 48 (1987) 458–464. Citation from ACKR; content **UNVERIFIED**.

### S8. A. J. Radcliffe, A. D. Scott
- "Reconstructing subsets of Z_n", J. Combin. Theory Ser. A 83 (1998) 169–187, doi:10.1006/jcta.1998.2870.
  - The DOI comes from Wikipedia. The pages and the bounds below come from secondary sources: **UNVERIFIED**.
  - Every subset of Z_p (p prime) is determined up to translation by its 3-deck.
  - In general a bound of roughly 9·ln n/ln ln n. The secondary sources disagree on its exact form.
- "Reconstructing under group actions", Graphs Combin. 22 (2006) 399–419, doi:10.1007/s00373-006-0675-y. ORA abstract, paraphrased (verified):
  - The reconstructibility of an action of G is bounded in terms of a normal subgroup N's action and of G/N.
  - For locally finite actions it is bounded by that of G itself.
  - The paper ends with geometric applications.
- **Proof idea (Z_n, standard bispectrum; [derived]).**
  - The 3-deck of A determines the triple correlation Σ_x 1_A(x)1_A(x+a)1_A(x+b), hence the bispectrum Â(ξ)Â(η)Â(−ξ−η).
  - If every Â(ξ) ≠ 0 (automatic for many A when n = p), the phases of Â are determined up to a character, i.e. up to translation.
- **Failing settings.**
  - Here k-decks are *small* subsets (k ≪ |A|), while vertex reconstruction uses near-full cards.
  - The method is specific to abelian groups (one-dimensional characters). S_n has no analogue.
  - It does not speak to T, H or I at all.
- **Lean.** Finite abelian Fourier exists (`Analysis/Fourier/ZMod.lean`, `FiniteAbelian/PontryaginDuality.lean`). A Z_p 3-deck theorem would be medium–hard, and irrelevant to RC.

### S9. L. Pebody
- "The reconstructibility of finite abelian groups", Combin. Probab. Comput. 13 (2004) 867–892, doi:10.1017/S0963548303005807.
  - Abstract (via the Cambridge listing and search): it gives the exact multiset-reconstruction number r(G) for every finite abelian group, and deduces r_set(Z_n) ≤ 6.
  - Abstract-level only; the theorem's exact formula is **UNVERIFIED**.
- "Set reconstruction on the hypercube", Discrete Analysis 2017:17, doi:10.19086/da.2108, arXiv:1607.05675. The reconstruction number of Z_2^n is ⌊n + 1 − log₂(n + 1 − log₂ n)⌋ (abstract, verified).
- **Failing settings / Lean.** As S8. Abelian only; not a route to RC.

### S10. Inclusion matrices
D. H. Gottlieb, "A certain class of incidence matrices", Proc. AMS 17 (1966) 1233–1237; W. M. Kantor, "On incidence matrices of finite projective and affine spaces", Math. Z. 124 (1972) 315–318.

- **Statement** (verified via secondary sources; originals not read). For t ≤ min(k, v−k), the inclusion matrix W_{t,k} (t-subsets × k-subsets of a v-set) has full rank C(v,t) over ℚ.
- Livingstone–Wagner, "Transitivity of finite permutation groups on unordered sets", Math. Z. 90 (1965). Pages **UNVERIFIED**. It says the number of orbits of a finite group on k-sets is non-decreasing for k ≤ v/2; Gottlieb–Kantor gives this as a corollary (**[derived]**, standard).
- **Role.** This is the linear-algebra core of Lovász, Kelly-type "k-deck determines t-deck" (Pouzet), and Mnukhin's orbit algebra.
- **Failing settings.** Pure linear algebra on subsets, so it is valid for every action (T, H): never sufficient alone.
- **Lean.** Not in Mathlib (no inclusion/Kneser rank theorem; grep found none). The full-rank theorem is medium–hard (300+ lines; Wilson's diagonal form or the Johnson-scheme eigenvalues).

### S11. R. P. Stanley, "Reconstruction from vertex-switching"
J. Combin. Theory Ser. B 38 (1985) 132–138. Verified from the scanned paper (pp. 132–133).

- **Theorem.** If n ≢ 0 (mod 4), X is determined by its unlabelled vertex-switched graphs X_1, ..., X_n.
- **Counterexample.** n = 4: 4K₁ vs C₄.
- **Lemma 2.1.** For f on Z_2^k and Γ ⊆ Z_2^k, the map f ↦ Σ_{X∈Γ+Y} f(X) is invertible iff χ̂_Γ(X) ≠ 0 for all X.
- **Lemma 2.2.** The map φ(X) = X_1 + ... + X_n on ℝ[graphs on [n]] is invertible iff n ≢ 0 (mod 4).
- **Idea.**
  - φ is a convolution on Z_2^{C(n,2)}; its eigenvalues are Krawtchouk-type character sums.
  - φ commutes with S_n, so invertibility passes to S_n-invariant vectors, where the switching deck lives.
  - It is "an alternative proof of a result of Lovász" (the paper says so).
- **Recent:** Cavaleri, Donno, Spessato, "Switching reconstruction of signed graphs: net-degree and balance", arXiv:2611.13901 (Nov 2026), abstract only. It extends the result to signed graphs with constant-sign net degrees (n ≠ 4) and some balanced cases.
- **Significance for RC.**
  - This is the model of a "harmonic analysis on the hypercube + S_n-averaging" success. It works because switching maps n-vertex graphs to n-vertex graphs, so the operator is square.
  - Vertex deletion maps to (n−1)-vertex graphs, and the corresponding operator has a big kernel (see E2). The method does not transfer.
- **Lean.** Lemma 2.1 is medium given `AddChar` duality on (ZMod 2)^k. The full theorem is hard (Krawtchouk zeros). Off-route.

### S12. Pouzet / Thiéry invariant theory, via Dufresne et al.
E. Dufresne, G. Jeronimo, J. Kenkel, H. Lindo, N. Villamizar, "Shuffling the deck: invariant theory and the graph reconstruction conjecture", arXiv:2604.16567 (Apr 2026; expository). Verified from the arXiv text.

- **Framework.**
  - V_n = k^{C(n,2)} (weighted graphs), with S_n permuting coordinates.
  - Orbit sums OS(x_M) of monomials form a k-basis of k[V_n]^{S_n}.
  - For a 0/1 point G, OS(x_{G′})(G) = s(G′, G), the number of copies of G′ in G.
- **Thm 7.3 ([Thi99, Thm 14.3.7]).** Two k-weighted graphs have the same deck iff OS(x_{M*})(G) = OS(x_{M*})(G′) for every multigraph M* on n vertices with at least one isolated vertex.
- **Pouzet's conjecture (1977).** These orbit sums generate k[V_n]^{S_n}. It would imply the *weighted* reconstruction conjecture, which is stronger than RC.
  - It is **false in general**: Thiéry (thesis, Lyon 1999) found failures for 11 ≤ n ≤ 18 (computational, non-constructive), as reported in the survey.
  - Also reported: for n ≥ 5 there is a degree-4 invariant not generated by orbit sums of simple graphs [Thi99, Thm 11.2.5].
  - Separation (rather than generation) would suffice and is **open**.
- **Thm 7.5.** A dense open set of weighted graphs (pairwise distinct weights) is reconstructible from any 3 cards. It contains no simple graphs, so it does not recover Bollobás.
- Primary sources:
  - M. Pouzet, Publ. Dép. Math. Lyon 14(2) (1977) 1–8;
  - N. Thiéry, PhD thesis, Lyon 1999, and SIGSAM Bull. 34 (2000) 9–20.
  - These are **UNVERIFIED** beyond the survey's account.
- **Failing settings.**
  - The same framework exists for digraphs (S_n on ordered pairs) and 3-uniform hypergraphs (S_n on triples). There the analogous isolated-vertex orbit sums **do not separate** (Stockmeyer, Kocay).
  - So any proof of separation that never uses "unordered pairs" is broken.
- **Lean.** Mathlib has `MvPolynomial`, `MulAction`, invariants. Stating separation is easy; anything beyond n = 3 is research.

### S13. I. C. Oliveira, B. D. Thatte, "An algebraic formulation of the graph reconstruction conjecture"
arXiv:1301.4121 (v2 2014; no journal ref listed). Verified from the arXiv text (§§2–3).

- **Kocay's lemma** (their Lemma 2.11). For F = (F_1, ..., F_m) with v(F_i) < n, Σ_H c(F,H)·s(H,G) is reconstructible. Here c(F,H) counts covers of H by copies of the F_i.
- **Thm 3.2.** For a finite recognizable class C_n satisfying Kocay's lemma and any family F of sequences, the number of decks |C_n/∼| ≥ rank_ℝ M_{F,C_n}.
- **Cor 3.3.** Full rank ψ(n) implies every graph in C_n is reconstructible.
- **Thm 3.4.** Some F (all sequences of length ≤ n of (n−1)-vertex graphs) attains rank = |C_n/∼|.
- **Hence (C_n = all graphs):** RC at order n ⇔ there is a covering matrix of rank ψ(n). This is an **exact linear-algebraic equivalent**.
- **Proof idea.** The vectors w_{ij}(H) = s(H,G_{ij}) − s(H,G_{i1}) lie in the kernel and are independent: order by edge count, and use s(G,G′) = 0 for non-isomorphic G, G′ with equal edge counts.
- **Failing settings.** The digraph and hypergraph analogues of the framework hold, and there the rank is deficient. So it is a reformulation, not a route.
- **Lean.**
  - Thm 3.2's kernel argument: medium–hard (subgraph counts on isomorphism classes, `Matrix.rank`).
  - The step "s(G,H) ≥ 1 with equal edge counts ⇒ G ≅ H" is easy: candidate E. It overlaps `hom_counts_and_logic.md` candidate E.

### S14. Other items checked for this angle
- **B. Bollobás**, "Almost every graph has reconstruction number three", J. Graph Theory 14 (1990) 1–4.
  - Citation verified via the Dufresne et al. reference list.
  - The proof idea is from memory, **UNVERIFIED**: G(n, ½) is asymmetric, its cards are pairwise non-isomorphic and asymmetric, and any 3 cards pin down G.
  - Lean: hard (probabilistic).
  - T: almost every tournament is reconstructible too (**UNVERIFIED**), so asymmetry-based routes don't separate graphs from tournaments. They only cover "almost all".
- **Y. Yang**, J. Graph Theory 12 (1988) 237–243. RC reduces to 2-connected graphs. Citation verified via the survey's reference list.
- **D. Greenwell**, Proc. AMS 30 (1971) 431–433: vertex-reconstructibility implies edge-reconstructibility for graphs with no isolated vertices and ≥ 4 edges. As reported in the Dufresne et al. survey. So group methods, which are strongest for ERC, attack the *weaker* conjecture.
- **J. Lauri, R. Scapellato**, *Topics in Graph Automorphisms and Reconstruction*, 2nd ed., LMS LNS 432, CUP 2016, doi:10.1017/CBO9781316669846.
  - Chapters 8–11 (verified TOC): The Reconstruction Conjectures; Reconstructing from Subdecks; Counting Arguments in Vertex-Reconstruction; Counting Arguments in Edge-Reconstruction.
  - Chapter 5 covers pseudosimilarity.
  - Chapter contents are **UNVERIFIED** (only the ch. 1 excerpt was available).
- **Dammak, Lopez, Pouzet, Si Kaddour**, "Hypomorphy of graphs up to complementation", arXiv:math/0601118. Labelled k-hypomorphy (G[U] ≅ H[U] for all k-sets U); reconstructible up to complement for 4 ≤ k ≤ n−4. Abstract only.
- **Ben Amira, Dammak, Si Kaddour**, arXiv:1302.4249. Kelly's lemma generalized (Pouzet) to families of t-subsets, mod p. Abstract only.
- **Calle, Gould**, "A combinatorial K-theory perspective on the Edge Reconstruction Conjecture", arXiv:2402.14986, Homology Homotopy Appl. 27 (2025), doi:10.4310/HHA.2025.v27.n1.a16. Abstract only: a reformulation framework, no new cases.
- **Failure anchors** (citations verified as listed; contents not re-read):
  - Stockmeyer, J. Graph Theory 1 (1977) 19–25;
  - Kocay, JCTB 42 (1987) 46–63 (infinite family of non-reconstructible 3-hypergraphs);
  - Fisher, J. Combin. Theory 7 (1969) 364–365;
  - Bowler, Erde, Heinig, Lehner, Pitz, arXiv:1606.02926 (locally finite trees) and arXiv:1611.04370 (bounded degree, one end / countably many ends). The journal venue of 1611.04370 is **UNVERIFIED**.
- **Not found:** any paper deriving vertex reconstruction from Fourier analysis on S_n (Specht/Young-module decomposition). Search terms: "reconstruction conjecture" with "representation theory", "symmetric group", "Fourier", "Young module". The invariant-theory survey (S12) is the closest.

## Equivalent reformulations

**E1. Labelled hypomorphy [derived, easy].**
- Hypomorphic G H ⇔ some H′ ≅ H has G − x ≅ H′ − x for every x (take H′ = H.comap σ).
- So the hypomorphism class is S_n-stable and one may assume σ = id.
- Candidate A.

**E2. Orbit pushforward / marginal formulation [derived; brute-force evidence n = 3, 4, 5, every pair of classes].**
- **Setup.**
  - Let X_n be the labelled graphs on [n], with S_n acting, and O_G the orbit of G.
  - Let r : X_n → X_{n−1} delete vertex n (restrict to [n−1]). It is S_{n−1}-equivariant.
  - Let F_G(K) = #{G′ ∈ O_G : r(G′) = K} for labelled K.
- **Fibre identity:** F_G(K) = m_G([K])·|Aut K| / |Aut G|, where m_G is the deck multiplicity.
  - Proof: Aut G acts freely on the pairs (v, iso G−v → K).
- **Hence** Hypomorphic G H ⇔ |Aut H|·F_G = |Aut G|·F_H, i.e. the deck is the projectivized pushforward r_*(1_{O_G}).
- **RC ⇔** for n ≥ 3, distinct extreme points of the simplex of S_n-invariant probability measures on X_n (the uniform orbit measures) have distinct images under the marginal map M_n to X_{n−1}.
- **What is known.**
  - M_n is far from injective. Its domain has dimension g(n), the number of graphs: 1, 2, 4, 11, 34, 156, ... Kelly gives all k-marginals k < n, but Σ_{k<n} g(k) < g(n) already for n = 4 (8 < 11).
  - So ker M_n ≠ 0, and RC says only that ker M_n contains no difference e_G − e_H of orbit indicators.
  - This is why every linear method (Lovász-type, Stanley-type, Gottlieb–Kantor) must fail for vertex reconstruction. A proof must use positivity or integrality of point masses, as Nash-Williams and Kocay do.
- Candidate D.

**E3. Separation by Kelly counts [derived; standard].**
- RC at order n ⇔ the functions s(F, ·) (copy counts) with |V(F)| ≤ n−1 separate isomorphism classes of n-vertex graphs.
- ⇐: Kelly.
- ⇒: the (n−1)-vertex subgraph counts determine the deck by triangular Möbius inversion over graphs on n−1 vertices.
- The algebra they generate contains Kocay's products. This is the 0/1-point shadow of S12's separating-set question.

**E4. Oliveira–Thatte rank equivalent (S13).** RC at order n ⇔ some covering matrix has rank ψ(n).

**E5. Edge version as group-action reconstruction (S4, S5).**
- ERC ⇔ ρ(S_n acting on pairs) ≤ 4 (Maynard–Siemons convention) for all n.
- Known: every edge set with m > N/2 (Lovász) or 2^{m−1} > n! (Müller), or 2^{m−2} > 2m(n−2)! (ACKR), is reconstructible.
- Generic permutation groups can have non-reconstructible sets near |Ω|/2 (S5), so the specific action matters.

**E6. Weighted / invariant-theoretic strengthening (S12).**
- Weighted RC ⇐ the isolated-vertex orbit sums separate S_n-orbits on k^{C(n,2)}.
- The stronger "generate" version is false for 11 ≤ n ≤ 18 (Thiéry, as reported).

**Which part is "known" representation-theoretically.**
- The linear part (marginals / Kelly) is exactly the part that an inclusion-matrix or Young's-rule analysis controls. It is provably insufficient by the dimension count in E2.
- No representation-theoretic statement *equivalent* to RC that avoids the nonlinear (single-orbit) constraint is known to me.
- The literature's exact equivalents (E2, E3, E4) all encode that constraint combinatorially.

## What breaks in the failing settings

| Ingredient | T: digraphs/tournaments (Stockmeyer) | H: 3-uniform hypergraphs (Kocay) | I: infinite (Fisher; Bowler et al.) | Verdict |
|---|---|---|---|---|
| Nash-Williams / ACKR counting (S1, S2, S5) | holds (S_n on ordered pairs) | holds (S_n on triples) | needs finite stabilizer; fails | sound tool; never separates graphs from T/H; size-bounded |
| Lovász linear injectivity (S3, S10) | holds | holds | n/a | linear; impossible for vertex decks (E2) |
| Kelly / k-deck / inclusion matrices | holds | holds | Kelly counts can be infinite | necessary, not sufficient |
| Kocay covering products, Oliveira–Thatte rank (S13) | holds; rank deficient for some n | holds; rank deficient | n/a | a reformulation; the rank must be computed per n |
| Orbit-sum separation (S12) | analogue fails | analogue fails | n/a | a proof must use the *unordered-pair* structure |
| Abelian Fourier (S8, S9, S11) | n/a | n/a | n/a | wrong group; not a route |
| "works for any subgroup Γ ≤ S_n" | — | — | — | **broken**: P_{2k} is not A_{2k}-edge-reconstructible (S6) |
| "works for any finite permutation group" | — | — | — | **broken** beyond ~|Ω|/2 (S5: wreath products) |

**Representation-theoretic check [derived from Young's rule, standard; James, LNM 682 (1978), citation UNVERIFIED].**
- The permutation module on 2-subsets is S^{(n)} ⊕ S^{(n−1,1)} ⊕ S^{(n−2,2)}, which is multiplicity-free.
- On ordered pairs it is S^{(n)} ⊕ 2S^{(n−1,1)} ⊕ S^{(n−2,2)} ⊕ S^{(n−2,1,1)}, which is not multiplicity-free.
- On 3-subsets (n ≥ 6) it is S^{(n)} ⊕ S^{(n−1,1)} ⊕ S^{(n−2,2)} ⊕ S^{(n−3,3)}, which is multiplicity-free again.
- So "the edge module is multiplicity-free" separates graphs from digraphs but **not** from 3-hypergraphs. It cannot be the key property by itself.
- A plausible structural difference: for pairs, the top Specht constituent has depth 2 ≤ the number of vertices a card retains information about. This is only a heuristic, not a lemma.

## Formalizable candidate steps

I did not run `desk.py propose`. Every Prop below elaborated against `import Mathlib` +
`import Recon.Basic` in the gitignored probe
`lean/Recon/Scratch/librarian_groups/probe.lean` (about 4 s; not a submission, not a result).
Statement bodies avoid `open`, `instance`, `end`, `#`, and the scoped `Pointwise` smul. They
use `Finset.image (fun x => g • x)` and `Set.ncard`.

**A. `found_hypomorphic_relabel_id`** (found). Easy, about 40–80 lines.
- **English.** G, H on Fin n are hypomorphic iff some graph H′ isomorphic to H has every card G − x isomorphic to H′ − x.
- **Lean.**
  ```lean
  ∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H ↔
    ∃ H' : SimpleGraph (Fin n), Nonempty (H ≃g H') ∧
      ∀ x : Fin n, Nonempty (Recon.card G x ≃g Recon.card H' x)
  ```
- **Route.**
  - (⇒) H′ := H.comap σ, using `Iso.comap` (Maps.lean:807) and `Iso.induce` (Maps.lean:870).
  - (⇐) σ := the iso's underlying equiv, composed with the card isos.

**B. `kelly_induced_subset_count`** (kelly). The k-deck from the deck. Medium, about 200–400 lines.
- **English.** If G, H on n vertices are hypomorphic, then for every k < n and every F on k vertices, G and H have equally many k-vertex subsets inducing a copy of F.
- **Lean.**
  ```lean
  ∀ n k : ℕ, k < n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H →
    ∀ F : SimpleGraph (Fin k),
      {U : Finset (Fin n) | Nonempty (G.induce (U : Set (Fin n)) ≃g F)}.ncard =
      {U : Finset (Fin n) | Nonempty (H.induce (U : Set (Fin n)) ≃g F)}.ncard
  ```
- **Natural reduction child** (also elaborates):
  `∑ x, #{U ⊆ {x}ᶜ | (card G x)[U] ≅ F} = (n − k)·#{U | G[U] ≅ F}`.
- **Route.**
  - Double counting: `Finset.sum_comm`, or `sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` (DoubleCounting.lean:87).
  - Plus the subset bijection Finset {x}ᶜ ≃ {U : Finset (Fin n) // x ∉ U}, and induce-of-induce ≅ induce.
- **Status.** Evidence: brute force n ≤ 5, every k, all hypomorphic pairs.
- **Note.** This is the *induced* version. `hom_counts_and_logic.md` A′ is the non-induced `labelledCopyCount` version; both are wanted.

**C. `groups_nash_williams_action`** (needs a program: `edge`, or a new `groups`; human opens it). Medium–hard, 300–700 lines. ACKR Cor 2.4 with k = 1: the engine for Lovász/Müller-type results and for Maynard–Siemons.
- **English.** Let a finite group Γ act on a type X, and let Y, Z be finite subsets of the same size m with |Γ| < 2^{m−1}. If every (m−1)-subset T of X has equally many Γ-translates among the (m−1)-subsets of Y as among those of Z, then Z is a Γ-translate of Y.
- **Lean.**
  ```lean
  ∀ (Γ X : Type) [Group Γ] [Fintype Γ] [MulAction Γ X] [DecidableEq X] (Y Z : Finset X),
    Y.card = Z.card → Fintype.card Γ < 2 ^ (Y.card - 1) →
    (∀ T : Finset X,
      {T' : Finset X | T' ⊆ Y ∧ T'.card + 1 = Y.card ∧ ∃ g : Γ, T'.image (fun x => g • x) = T}.ncard =
      {T' : Finset X | T' ⊆ Z ∧ T'.card + 1 = Z.card ∧ ∃ g : Γ, T'.image (fun x => g • x) = T}.ncard) →
    ∃ g : Γ, Y.image (fun x => g • x) = Z
  ```
- **Route** (ACKR Thm 2.1 with S = ∅).
  - Let f(A) = #{g : A ⊆ gY} − #{g : A ⊆ gZ}. It is zero for |A| ≤ m−1 (by the deck, plus the Kelly identity for subsets).
  - Take a minimal T with f(T) ≠ 0. Inclusion–exclusion (`Finset.sum_powerset_neg_one_pow_card`, Data/Nat/Choose/Sum.lean:210) gives 2^{|T|−1} ≥ 2^{m−1} elements g, contradicting |Γ|.
- **Status.** Evidence: no violation for Z_n and D_n acting on Z_n, n ≤ 14.
- **Uses.**
  - Müller, once `Basic.lean` gets an edge deck.
  - Maynard–Siemons Thm 2.6.
  - ACKR's bipartite vertex application.

**D. `found_hypomorphic_iff_orbit_fibre`** (found). The exact S_n-orbit formulation, E2. Hard, about 600+ lines: orbit–stabilizer for relabelling graphs, which has no `MulAction (Perm V) (SimpleGraph V)` instance in Mathlib (use `comap`).
- **English.** G, H on n+1 vertices are hypomorphic iff, for every graph K on the first n vertices, |Aut H| times the number of relabellings of G that restrict to K equals |Aut G| times the same count for H.
- **Lean.**
  ```lean
  ∀ n : ℕ, ∀ G H : SimpleGraph (Fin (n + 1)), Recon.Hypomorphic G H ↔
    ∀ K : SimpleGraph (Fin n),
      Nat.card (H ≃g H) *
        {G' : SimpleGraph (Fin (n + 1)) | Nonempty (G ≃g G') ∧ G'.comap Fin.castSucc = K}.ncard =
      Nat.card (G ≃g G) *
        {H' : SimpleGraph (Fin (n + 1)) | Nonempty (H ≃g H') ∧ H'.comap Fin.castSucc = K}.ncard
  ```
- **Status.** Evidence: n + 1 ∈ {3, 4, 5}, all pairs, no mismatch.
- **Value.** It opens the marginal/measure and representation route, and it is the precise answer to "is there an equivalent group-theoretic statement". There is no immediate downstream theorem.

**E. `found_iso_of_hypomorphic_spanning_copy`** (found). Easy–medium given `kelly_edge_count`. It overlaps `hom_counts_and_logic.md` E; prefer one of the two.
- **Lean.**
  ```lean
  ∀ n : ℕ, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H →
    (Nonempty (G ≃g H) ↔ ∃ e : Fin n ≃ Fin n, G ≤ H.comap e)
  ```

### Mathlib map for this angle
Paths are under `lean/.lake/packages/mathlib/Mathlib/`.

**Present.**
- `MulAction.orbit` (`GroupTheory/GroupAction/Defs.lean:48`), `stabilizer` (:514), `fixedBy` (:121), `orbitRel` (:286).
- `orbitEquivQuotientStabilizer` and `card_orbit_mul_card_stabilizer_eq_card_group` (`GroupTheory/GroupAction/Quotient.lean:169,184`).
- Burnside `sum_card_fixedBy_eq_card_orbits_mul_card_group` (Quotient.lean:267). Class formula: `GroupTheory/GroupAction/CardCommute.lean:48,63`.
- `Group (r ≃r r)` (`Algebra/Order/Group/End.lean:73`), so `G ≃g G` is a group (automorphism group); use `Nat.card`.
- `SimpleGraph.comap` (Maps.lean:132) and `Iso.comap` (Maps.lean:807): relabelling. `Iso.induce` (Maps.lean:870).
- `labelledCopyCount` and `copyCount` (`Combinatorics/SimpleGraph/Copy.lean:506,527`). Note that `copyCount` counts non-induced copies.
- Inclusion–exclusion (`Combinatorics/Enumerative/InclusionExclusion.lean:117–183`), `Finset.sum_powerset_neg_one_pow_card` (`Data/Nat/Choose/Sum.lean:210`), `moebius_inversion_top/bot` (`Combinatorics/Enumerative/IncidenceAlgebra.lean:540,576`), double counting (`Combinatorics/Enumerative/DoubleCounting.lean:87`).
- `Finset.card_powersetCard` (`Data/Finset/Powerset.lean:211`).
- Representations: `Representation` (`RepresentationTheory/Basic.lean:48`), `ofMulAction` (:395), characters `char_orthonormal` (`RepresentationTheory/Character.lean:144,248`), Maschke, `Invariants`.
- Young diagrams (`Combinatorics/Young/YoungDiagram.lean`, `SemistandardTableau.lean`): combinatorics only.
- Finite abelian Fourier: `ZMod.dft` (`Analysis/Fourier/ZMod.lean:87`, `dft_dft` :176) and `AddChar` duality (`Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean`).
- `Matrix.rank` (`LinearAlgebra/Matrix/Rank.lean`).

**Gaps.**
- No `MulAction (Equiv.Perm V) (SimpleGraph V)` instance. A trusted-file definition would be needed to state orbit facts natively; until then, `comap`.
- No Specht modules or Young's rule (no S_n irreducibles).
- No inclusion-matrix (Gottlieb–Kantor/Wilson) rank theorem.
- No edge deck / edge hypomorphism in `Recon.Basic`.

## Open gaps

1. **Edge deck definition (human, trusted).** Lovász, Müller, ACKR graph corollaries, Greenwell and Thatte all need `EdgeHypomorphic` in `Basic.lean`. Until then they cannot be phrased with `Recon.*`. Candidate C can be checked as an abstract lemma now.
2. **Primary texts not read:** Nash-Williams 1978; Lovász 1972; Müller 1977; Mnukhin 1987/1992; Radcliffe–Scott 1998/2006; Pebody 2004 (main theorem); Pouzet 1977; Thiéry 1999; Lauri–Scapellato chs. 8–11; Livingstone–Wagner 1965; Krasikov–Roditty 1987; Cameron, "Stories from the age of reconstruction", Congr. Numer. 113 (1996) 31–41 (citation from a search summary; **UNVERIFIED**, not found).
3. **Is |Aut G| reconstructible?** E2 does not determine it: the fibre identity is consistent with any ratio. I did not find the status in a source (**UNVERIFIED**). If it were recognizable, E2 would become "deck = r_*(1_{O_G})" exactly.
4. **No vertex analogue of Müller** (a bound like 2^{f(G)} > g(n) ⇒ reconstructible) was found. The obstruction: a card deletes a variable set of pairs, so the ACKR k-deck framework does not apply directly. ACKR's bipartite trick (S1) is the only vertex application I found.
5. **Representation-theoretic separation.** The open question in this language: do the restrictions of the S_n-orbit measure to S_{n−1} (E2) separate orbits? Any argument must fail for S_n on ordered pairs and on triples. Multiplicity-freeness does not distinguish pairs from triples.
6. Thiéry's counterexamples to Pouzet's generation conjecture are reported second-hand only (n range 11–18).
