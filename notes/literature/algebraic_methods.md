# Algebraic and counting methods: Kelly, Kocay, Whitney, Tutte, Lovász–Müller–Nash-Williams, inclusion matrices, invariant theory

Librarian sweep, 2026-11-25. Angle: Möbius inversion, inclusion–exclusion, inclusion
matrices, graph polynomials. Working hypothesis given by the caller: the conjecture is true,
and we look for proof routes. Nothing in this file is a result. The only results are steps
that are **checked** on `main`. Companion API map: `notes/mathlib/algebraic_methods.md`.
Kelly's lemma itself (statement variants, Lean bodies) is already mapped in
`notes/literature/kelly_recognizable_invariants.md` §3 and §7. This file
does not repeat those bodies. It builds on them.

Verification legend:
- **[V-text]**: I read the statement in the paper's own text (PDF converted to text).
- **[V-sec]**: I read it in a secondary source that quotes or restates it (source named).
- **[V-abs]**: I verified it from the arXiv abstract page or a repository record only.
- **UNVERIFIED**: I did not see it in any source this session.

## Summary

1. Kelly's lemma (counts of all subgraphs with < n vertices) and Kocay's lemma (some linear
   combinations of counts of *spanning* subgraphs) generate the whole classical list of
   recognizable invariants: the characteristic, chromatic and Tutte polynomials, the
   number of spanning trees, Hamiltonian cycles and perfect matchings (Tutte 1979, Kocay
   1981; recast by Thatte 2005).
2. **Obstruction:** Oliveira–Thatte (arXiv:1301.4121) give an argument that the Kocay
   equations have rank *exactly* the number of distinct decks d(n). Their framework also
   holds verbatim for digraphs and hypergraphs, where reconstruction fails. So Kelly and
   Kocay identities alone cannot prove the conjecture, and any proof must add input
   specific to graphs. Thiéry (1999) refuted Pouzet's "orbit sums generate the invariant
   ring" for 11 ≤ n ≤ 18, so the generating version of the invariant-theory route is dead.
   The weaker "separating" version is still open.
3. The **characteristic polynomial** is recognizable for graphs (Tutte) but not for
   3-uniform hypergraphs (Cooper–Okur, arXiv:2312.16152). Our own brute-force run also
   finds it not recognizable for tournaments at n = 5. So it is a genuinely graph-specific
   recognizable invariant. It is still far from complete: cospectral graphs exist.
4. **Edge reconstruction:** Lovász (m > ½·C(n,2)) and Müller (2^(m−1) > n!) both follow
   from the inclusion–exclusion lemma of Nash-Williams (1978), in the general group-action
   form of Alon–Caro–Krasikov–Roditty (1989). Stanley (1984) gives the linear-algebra
   (Peck poset) proof of Lovász's theorem. These methods do not apply to vertex
   reconstruction: the vertex deck is not an instance of their "delete one element of a
   set under a group" setting.
5. Best Lean targets from this angle:
   - generalized Kelly sums over deleted vertex sets;
   - the perfect-matching count by labelled inclusion–exclusion (a Kocay-type spanning
     count that needs no enumeration of isomorphism classes);
   - P′(G) = Σᵥ P(G − v) for the characteristic polynomial.
   All three are finite counting or linear-algebra statements with good Mathlib support.

## Sources

Each entry gives: citation, what it claims, verification status, behaviour in failing
settings, and Lean difficulty. "Failing settings" means tournaments and digraphs
(Stockmeyer), k-uniform hypergraphs with k ≥ 3 (Kocay), and infinite graphs.

### A1. Kelly's lemma: Kelly 1957
- P. J. Kelly, *A congruence theorem for trees*, Pacific J. Math. 7 (1957) 961–968.
  DOI 10.2140/pjm.1957.7.961 (DOI pattern not opened; citation [V-sec] via Thatte 2005
  and Oliveira–Thatte).
- **Statement** [V-sec, Thatte 2005 Lemma 1.2]: if v(F) < v(G), then
  s(F, G) = (1/(n − v(F))) · Σᵥ s(F, G − v). This holds for subgraph counts and for
  induced-subgraph counts. Hence s(F, G) is recognizable.
- **Proof idea:** double count the pairs (copy of F, vertex not in the copy). Each copy
  misses exactly n − v(F) vertices.
- **Failing settings:** it holds verbatim for digraphs, tournaments and hypergraphs (the
  counting never uses that edges are 2-sets). Oliveira–Thatte state it for general
  hypergraphs and digraphs [V-text]. It fails for infinite graphs, because the division by
  n − v(F) is meaningless there. So Kelly's lemma alone can never close the conjecture.
- **Lean:** easy to moderate. The bodies are in the Kelly note §7 (`kelly_copy_sum`,
  `kelly_lemma_labelled`, `kelly_lemma_induced`). Mathlib has `labelledCopyCount`,
  `copyCount` and `Copy` (`Combinatorics/SimpleGraph/Copy.lean`).

### A2. Kocay's lemma: Kocay 1981
- W. L. Kocay, *On reconstructing spanning subgraphs*, Ars Combin. 11 (1981) 301–313.
  This citation is used by Thatte 2005 and Stark 2025 [V-sec].
  Oliveira–Thatte instead cite W. L. Kocay, *An extension of Kelly's lemma to spanning
  subgraphs*, Congr. Numer. 31 (Proc. 10th Manitoba Conf., 1980), 109–120, 1981 [V-sec].
  **Citation conflict:** both may exist. The original paper was not opened. Also
  W. L. Kocay, *Some new methods in reconstruction theory*, Combinatorial Mathematics IX,
  LNM 952, Springer 1982, 89–114 [V-sec].
- **Statement** [V-text, Thatte 2005 Lemma 1.3; Oliveira–Thatte Lemma 2.11]:
  - For a family S = (F₁,…,F_k), let c(S, X) be the number of tuples (X₁,…,X_k) of
    subgraphs of X with Xᵢ ≅ Fᵢ and ⋃Xᵢ = X.
  - Then Πᵢ s(Fᵢ, G) = Σ_X c(S, X) · s(X, G), summed over the isomorphism types X.
  - If every v(Fᵢ) < n, then Σ over the spanning X of c(S, X) · s(X, G) is recognizable.
- **Proof idea:** expand the product as tuples of copies and group the tuples by their
  union. Every non-spanning union has fewer than n vertices, so Kelly handles it.
- **Standard consequences** [V-sec, Thatte 2005 §3 outline]:
  1. Take the Fᵢ with Σ v(Fᵢ) = n. This gives the count of every disconnected spanning
     subgraph type, so disconnected graphs are reconstructible.
  2. Take k = n − 1 copies of K₂. This gives the number of spanning trees.
  3. Take k = n copies of K₂. This gives the number of Hamiltonian cycles, and from those
     the characteristic and rank polynomials.
- **Failing settings:** it holds verbatim for digraphs and hypergraphs [V-text,
  Oliveira–Thatte §2, "stated in full generality"].
- **Lean:** the counting identity is moderate, but the isomorphism-type bookkeeping
  (sums over unlabelled X) is hard in Lean. Recommended route: the *labelled*
  inclusion–exclusion form in §"Formalizable candidate steps" (C3/C4). It replaces "sum
  over spanning unions" by Σ_{S ⊆ V} (−1)^|S| Πᵢ s(Fᵢ, G − S). This form is **derived
  here, not quoted from a source**. It is ordinary inclusion–exclusion over the set of
  uncovered vertices, and I checked it numerically for Fᵢ = K₂ (300 random graphs,
  n ≤ 8, 0 failures).

### A3. Tutte 1979: "All the king's horses"
- W. T. Tutte, *All the king's horses. A guide to reconstruction*, in: Bondy & Murty
  (eds.), *Graph Theory and Related Topics*, Academic Press, 1979, 15–33 [V-sec, Thatte
  2005 bibliography].
- **Claims** [V-sec, Thatte 2005 §1.2, Oliveira–Thatte §1, Kotek 2009 abstract]: the
  characteristic polynomial, the chromatic polynomial, the Tutte (rank) polynomial, the
  number of spanning trees, the number of Hamiltonian cycles and the number of perfect
  matchings are recognizable. Li–Shi–Trinks attribute the perfect-matching count to
  "Tutte, Statement 6.9" [V-sec via search snippet of EJGTA 3(1) 2015, 27–34].
- **Proof idea:** count the spanning subgraphs of each "elementary" type. Tutte's original
  route goes through his theory of V-functions (Thatte says the original proofs use
  "actual subgraphs"). Kocay's lemma gives the simpler route.
- **Failing settings:** see A10 and A11. The characteristic polynomial is not
  recognizable for 3-uniform hypergraphs, nor (by our computation) for tournaments. So
  Tutte's charpoly argument uses graph-specific structure: Sachs' formula with
  elementary subgraphs made of K₂'s and cycles.
- **Lean:** hard to very hard. Mathlib has no chromatic polynomial, no Tutte polynomial,
  no matrix-tree theorem and no Sachs theorem (see the Mathlib note).
- Tutte, *Graph Theory* (Encyclopedia of Math. and its Applications 21, Addison-Wesley,
  1984). Thatte cites pp. 123–124 for Tutte's proposed generalizations [V-sec].
- Tutte, *Graph Theory As I Have Known It*, Oxford Univ. Press, 1998. Oliveira–Thatte cite
  ch. 9, p. 113 for Tutte's *pessimism* about how far the Kelly/Kocay methods reach
  [V-sec]. The book's content is otherwise UNVERIFIED (not opened).

### A4. Whitney's subgraph expansion (Whitney 1932) and Thatte 2005
- H. Whitney, *A logical expansion in mathematics*, Bull. AMS 38 (1932) 572–579 [V-sec].
- B. D. Thatte, *Kocay's lemma, Whitney's theorem, and some polynomial invariant
  reconstruction problems*, Electron. J. Combin. 12 (2005) #R63, arXiv:math/0507375
  [V-text].
- **Statements** [V-text]:
  - *Whitney (Thatte Thm 5.1):* the number of subgraphs of a "type" S₀ (a multiset of
    blocks) is an explicit alternating sum over chains Sq ≺ … ≺ S₀ of products of
    p(S) = Π s(Fᵢ, G), with coefficients built from covering numbers. This is an explicit
    Möbius inversion on the poset of types.
  - *Thatte Cor 5.2:* the characteristic polynomial is recognizable, through Whitney's
    theorem and Kelly's lemma.
  - *Thatte Thm 2.12:* Ulam's conjecture holds iff the disconnected graphs on ≥ 3
    vertices are N-matrix reconstructible.
  - *Thatte Thm 2.13:* Ulam's conjecture holds iff the edge-labelled poset of induced
    subgraphs of every graph has only the trivial automorphism.
  - *Thatte Thm 3.12:* the following are all recoverable from the unlabelled N-matrix
    (a weaker input than the deck): the number of spanning trees, the number of cycles of
    each length, the number of unicyclic spanning subgraphs with a given cycle length,
    the number of Hamiltonian cycles, and P(G; λ).
  - *Thatte Thm 4.4:* if G has a vertex of degree 1, then P(G) is recognizable from the
    complete polynomial deck {P(G − S)}.
  - *Lemma 1.7 (from Biggs, Note 2d):* P′(G; λ) = Σᵥ P(G − v; λ).
  - *Lemma 1.6 (Biggs Prop 7.3, Sachs):* (−1)^i cᵢ(G) = Σ (−1)^{r(F)} 2^{s(F)} over the
    elementary subgraphs F on i vertices, where r is the rank and s the co-rank.
  - Thatte states that Gutman–Cvetković's polynomial-deck question "remains open".
- **Failing settings:** Thms 2.12 and 2.13 are equivalences, so they carry no
  graph-specific proof power. Lemma 1.7 holds for *every* square matrix: it is the Jacobi
  formula for the principal minors. So the derivative part is recognizable for digraphs
  and tournaments too, and only the constant term is graph-specific (consistent with our
  tournament computation in A11).
- **Lean:**
  - Lemma 1.7: moderate. No Jacobi/derivative-of-charpoly lemma exists in Mathlib, but
    `det_apply`, `derivative_prod_finset`, `charpoly_reindex` and
    `Embedding.submatrix_adjMatrix` exist. This makes a good upstreamable lemma.
  - Lemma 1.6 (Sachs): hard.
  - Thm 5.1: hard (posets of isomorphism types).

### A5. Lovász 1972: edge reconstruction for dense graphs
- L. Lovász, *A note on the line reconstruction problem*, J. Combin. Theory Ser. B 13
  (1972) 309–310 [V-sec: ACKR, Stanley, Thatte bibliographies].
- **Statement** [V-text, as restated and re-proved in Stanley 1984, Thm 3]: if a graph Γ
  on {1,…,n} has q > ½·C(n,2) edges, then its edge-deleted deck determines Γ up to
  isomorphism. This **confirms** the CLAUDE.md claim "Lovász (1972): m > n(n−1)/4".
- **Proof idea (original):** inclusion–exclusion over the edge subsets. It is a special
  case of the Nash-Williams lemma (A7) with F = ∅: two m-edge graphs with m > ½·C(n,2)
  always share an edge, so the count for F = ∅ is 0 on both sides, which contradicts the
  lemma's nonzero right-hand side. The original text was not opened. The route is
  [V-text] via ACKR Thm 2.1 and Remark 2.3.
- **Failing settings:** edge reconstruction for hypergraphs with many edges goes through
  the same way (ACKR §3.1 [V-text]). That is consistent, not a warning, because edge
  reconstruction is not known to fail there. The method says nothing about vertex
  reconstruction.
- **Lean:** hard (about 800–1500 lines). It needs an edge-deck notion, which `Basic.lean`
  lacks. An inline definition works (C9). Formalizing it is a human decision for the
  `edge` program.

### A6. Müller 1977
- V. Müller, *The edge reconstruction hypothesis is true for graphs with more than
  n·log₂ n edges*, J. Combin. Theory Ser. B 22 (1977) 281–283 [V-sec].
- **Statement** [V-text via ACKR §1 and Cor 2.4]: graphs with m > 1 + log₂(n!) edges, that
  is 2^(m−1) > n!, are edge-reconstructible. This **confirms** the CLAUDE.md claim.
- **Proof idea** [V-text, ACKR Cor 2.4 with k = 1, G = S_n]: if Y is not reconstructible
  from its 1-deck, then by ACKR Thm 2.1 some set T ⊆ E(G) with |T| ≥ m has at least
  2^(|T|−1) distinct traces gY ∩ T. So n! ≥ |orbit| ≥ 2^(m−1).
- **Failing settings:** the same as A5.
- **Lean:** hard, but slightly easier than Lovász once ACKR Thm 2.1 is in place (it is a
  pure counting argument over `Equiv.Perm (Fin n)`).

### A7. Nash-Williams 1978 lemma; ACKR 1989 general form
- C. St. J. A. Nash-Williams, *The reconstruction problem*, in Beineke & Wilson (eds.),
  *Selected Topics in Graph Theory*, Academic Press 1978, 205–236 [V-sec]. Not opened.
- N. Alon, Y. Caro, I. Krasikov, Y. Roditty, *Combinatorial reconstruction problems*,
  J. Combin. Theory Ser. B 47 (1989) 153–161 [V-text, full PDF read].
- **ACKR Theorem 2.1** [V-text]:
  - Setting: a group G acts on a set X, and Y ⊆ X with |Y| = m is not reconstructible
    from its k-deck (the multiset of orbits of its (m−k)-subsets). Let S ⊆ Y with
    |S| = t ≤ m − k have a finite stabiliser.
  - Then there are a T with S ⊆ T ⊆ Y and |T| ≥ m − k + 1, and an ε ∈ {0,1}, such that for
    every K with S ⊆ K ⊆ T and |K| ≡ ε (mod 2) some g ∈ G has T ∩ gY = K.
  - Proof: let f(A) = #{members of Y^G containing A} − #{members of Y′^G containing A}.
    This vanishes for |A| ≤ m − k (a Kelly-type count). Take a minimal T with f(T) ≠ 0.
    Inclusion–exclusion then gives #{g : gY ∩ T = K} − #{g : gY′ ∩ T = K} =
    (−1)^{|T−K|} f(T).
- **Remark 2.3** [V-text]: with X = E(Kₙ), G = Sₙ, S = ∅ and k = 1, Thm 2.1 "is just the
  result of Nash-Williams".
- **Thatte's form** [V-sec, Thatte, *G-reconstruction of graphs*, Ars Combin. 54 (2000)
  293–299, arXiv:math/0608071, Lemma 1]: if X and Y are G-edge-hypomorphic but not
  G-isomorphic, then for every spanning F ⊆ X,
  |X →_G X|_F − |Y →_G X|_F = (−1)^{m−|E(F)|} |G ∩ Aut X|.
  Here |Y →_G X|_F is the number of g ∈ G with g(Y) ∩ X = F.
- **Other corollaries** [V-text]:
  - ACKR Cor 2.5 (t = 1) gives edge reconstruction when 2^(m−2) > m·(n−2)!.
  - Prop 3.1 extends a theorem of Caunter–Nash-Williams on the average degree.
  - Hypergraphs: 2^(m−1) > n! suffices.
  - Vertex reconstruction of 2-connected bipartite graphs with |B| ≥ 1 + log₂(|A|!) and
    distinct B-neighbourhoods, through hypergraph edge reconstruction.
- **ACKR's own verdict** [V-text, §4]: "It does not seem that the general approach
  considered here will be very fruitful in tackling [edge reconstruction]."
- **Godsil–Krasikov–Roditty** [V-sec via ACKR]: C. D. Godsil, I. Krasikov, Y. Roditty,
  *Reconstructing graphs from their k-edge deleted subgraphs*, JCTB 43 (1987) 360–363.
  Reconstruction holds for m > k + log₂(n!) or m > ½(C(n,2) + k).
- **Lean:** moderate to hard. The core is finite inclusion–exclusion on `Finset.powerset`
  (Mathlib `Finset.inclusion_exclusion_*`, `Combinatorics/Enumerative/InclusionExclusion.lean`),
  plus a group action of `Equiv.Perm (Fin n)` on `Sym2`. A generic ACKR Thm 2.1 over a
  finite group action on `Finset X` would be a clean library lemma.

### A8. Inclusion matrices: Gottlieb 1966, Kantor 1972, Pouzet 1976
- D. H. Gottlieb, *A certain class of incidence matrices*, Proc. AMS 17 (1966) 1233–1237
  [V-sec].
  - Claim [V-sec, Ben Amira–Dammak–Si Kaddour arXiv:1302.4249]: over ℚ the inclusion
    matrix W_{t,k} of the t-subsets versus the k-subsets of a v-set has rank C(v,t), for
    t ≤ min(k, v−k).
- W. M. Kantor, *On incidence matrices of finite projective and affine spaces*, Math. Z.
  124 (1972) 315–318, DOI 10.1007/BF01113923 [V-text].
  - Main theorem: for subspaces of PG(d,q)/AG(d,q).
  - Remark: "the same proof shows that, if −1 ≤ e < f ≤ d − e, an incidence matrix of all
    e-sets vs. all f-sets of a set of d points has rank C(d,e)."
  - Proof: a dependence among the rows is averaged over the stabiliser of one row, and
    then over its orbits.
- M. Pouzet, *Application d'une propriété combinatoire des parties d'un ensemble aux
  groupes et aux relations*, Math. Z. 150 (1976) 117–134 [V-sec].
  - Pouzet's lemma [V-sec, arXiv:1302.4249 Lemma 1.2]: let U, U′ be families of t-subsets
    of a v-set with t ≤ min(k, v−k). If every k-subset contains as many members of U as of
    U′, then U = U′.
  - Orbit version [V-text via Stanley 1984]: for a group G acting, there are maps
    ψ_{ij}: V_i/G → V_j/G of rank min(|P_i/G|, |P_j/G|).
- M. Pouzet, *Relations non reconstructibles par leurs restrictions*, JCTB 26 (1979)
  22–34 [V-sec, citation only]. Content UNVERIFIED.
- **Relevance:** the labelled statement "edge sets of size m > ½·C(n,2) are determined by
  their (m−1)-subsets" is Gottlieb–Kantor. The orbit (isomorphism) version is Lovász's
  theorem (A9).
- **Failing settings:** these are pure set-system facts with no graph structure, so they
  apply equally to hypergraph edge reconstruction.
- **Lean:** moderate to hard (about 400 lines). Mathlib has neither inclusion-matrix rank
  nor Gottlieb's theorem. C10 is a Finset-only statement.

### A9. Stanley 1984: quotients of Peck posets
- R. P. Stanley, *Quotients of Peck posets*, Order 1 (1984) 29–34 [V-text, full PDF read].
- **Theorem 1:** if P is unitary Peck, then P/G is Peck for every group G of
  automorphisms.
- **Theorem 3:** an elementary, linear-algebraic proof of Lovász's theorem.
  - Let ψ_q: V_q → V_{q−1} send a labelled graph to the sum of its edge-deleted graphs.
  - ψ_q is injective for q > ½·C(n,2), because Boolean algebras are unitary Peck.
  - It commutes with S_n, so it stays injective on the Sₙ-invariants (whose basis is the
    orbit sums, that is, the unlabelled graphs).
- Stanley [V-text]: "We don't know whether the above argument can be extended in some way
  for q < ½·C(n,2). In particular, we are unable to obtain Müller's extension."
- **The "kernel of an incidence map" view:**
  - Edge reconstruction for q-edge graphs is exactly the statement that ψ_q restricted to
    the orbit sums separates basis vectors (0/1 orbit indicators).
  - Injectivity of the whole linear map is sufficient. It holds for q > ½·C(n,2), and it
    fails for smaller q simply by counting dimensions.
- **Vertex analogue (our elementary observation, not from a source):**
  - The linear extension of G ↦ Σᵥ [G − v], from ℚ^{ψ(n)} to ℚ^{ψ(n−1)} (ψ is the number
    of graph classes: 1, 2, 4, 11, 34, 156, …), has a kernel of dimension at least
    ψ(n) − ψ(n−1) > 0.
  - So a "whole map is injective" argument can never work for vertex reconstruction. One
    has to use that the decks of two graphs differ by an element [G] − [H] of a special
    shape, i.e. nonlinear or integrality information.
  - This is the same lesson as Oliveira–Thatte's rank theorem (A10).
- **Lean:** hard. Peck/Sperner theory is not in Mathlib.

### A10. Oliveira–Thatte 2013/2014: Kocay's lemma has exactly the power of the deck
- I. C. Oliveira, B. D. Thatte, *An algebraic formulation of the graph reconstruction
  conjecture*, arXiv:1301.4121 (v2, Sep 2014). No journal reference on the arXiv page
  [V-text].
- **Setting:** for a family F of sequences of graphs on ≤ n − 1 vertices, let M be the
  matrix of covering numbers c(F, H), with F ∈ F and H ranging over the n-vertex graphs.
- **Thm 3.2:** for a finite recognizable class Cₙ satisfying Kocay's lemma,
  #(reconstruction classes) ≥ rank_ℝ M.
- **Cor 3.3:** if rank M = |Cₙ/≅|, then every graph in Cₙ is reconstructible.
- **Thm 3.4:** some family F (all sequences of length ≤ n of (n−1)-vertex graphs) attains
  rank M = d(n), the number of decks.
- Their framework is stated for undirected graphs, digraphs and hypergraphs alike.
  Figure 2 illustrates it on digraphs with 3 vertices.
- **Authors' conclusion** [V-text]: "our results may also be viewed as a limitation of the
  lemmas of Kelly and Kocay … it seems unlikely that applications of Kelly's lemma and
  Kocay's lemma will shed light on these difficulties."
- **Lean:** Cor 3.3 is moderate (rank–nullity, `Matrix.rank`). For n ≤ 13 it is a
  decision procedure rather than a proof route.

### A11. Characteristic polynomial: polynomial-deck problem, hypergraphs, tournaments
- I. Gutman, D. M. Cvetković, *The reconstruction problem for characteristic polynomials
  of graphs*, Univ. Beograd Publ. Elektrotehn. Fak. Ser. Mat. Fiz. 498–541 (1975) 45–48
  [V-sec, Thatte bibliography].
- The **polynomial reconstruction problem** (PRP): is P(G) determined by {P(G − v)}? Its
  status is **open** per:
  - I. Sciriha, Z. Stanić, *The polynomial reconstruction problem: the first 50 years*,
    Discrete Math. 346(6) (2023) 113349, DOI 10.1016/j.disc.2023.113349 [V-abs,
    repository record: "no counterexample has been found"].
  - Thatte 2005 [V-text].
- Partial results:
  - E. M. Hagos, Electron. J. Combin. 7 (2000) #R12: P(G) is recognizable from the deck of
    pairs (P(G−v), P(complement of G−v)) [V-sec, title].
  - I. Sciriha, *Polynomial reconstruction and terminal vertices*, Linear Algebra Appl.
    356 (2002) 145–156 [V-sec, citation].
  - T. J. Spier, *Efficient reconstruction of the characteristic polynomial*,
    arXiv:2503.17853 (2025) [V-abs]: P(G) mod 4 is recognizable from the polynomial deck
    when n is even, or when the 𝔽₂-rank of the walk matrix is < ⌈n/2⌉. P(Ḡ) mod 4 can be
    computed from P(G) mod 4.
- **Hypergraphs:** J. Cooper, U. Okur, *Polynomial reconstruction problem for hypergraphs*,
  arXiv:2312.16152 (2023/24) [V-abs]. Kocay's hypomorphic non-isomorphic 3-uniform pairs
  have *different* characteristic polynomials. Because the pairs share the full deck,
  the hypergraph characteristic polynomial is **not recognizable** at all.
- **Tournaments (our computation, not a literature result):**
  - Script: `scratchpad/scripts/tourn.py` (session scratchpad, not committed).
  - It enumerates all labelled tournaments on 5 and 6 vertices (12 and 56 classes, which
    matches the known counts) and groups them by deck.
  - n = 5: one hypomorphic non-isomorphic pair (12 classes, 11 decks). The adjacency
    charpolys are x⁵ − 4x² − 3x − 3 and x⁵ − 4x² − 3x − 2. They differ **only in the
    constant term**.
  - n = 6: four pairs (56 classes, 52 decks), all with equal charpolys.
  - Conclusion: the characteristic polynomial is not recognizable for tournaments.
    Combined with A4, the derivative part is universal and the determinant is the
    graph-specific part.
  - A red-team agent may re-run this to confirm it. It is not checked.
- **Matching polynomial:** X. Li, Y. Shi, M. Trinks, *Polynomial reconstruction of the
  matching polynomial*, arXiv:1404.3469 [V-abs]. They disprove polynomial
  reconstructibility for some graphs, and prove it for graphs with pendant edges. It is
  nevertheless recognizable from the *deck*: the number of perfect matchings is
  recognizable (Tutte) and the other coefficients follow from Kelly.

### A12. Further reconstructible graph polynomials
- T. Kotek, *On the reconstruction of graph invariants*, Electron. Notes Discrete Math. 34
  (2009) 375–379, DOI 10.1016/j.endm.2009.07.062, arXiv:0905.1915 [V-abs]. The interlace
  polynomial, the U-polynomial, the universal edge elimination polynomial ξ and the
  coloured versions of the last two are recognizable.
- P. Stark, *Generalization and power of Kocay's lemma in graph reconstruction*,
  arXiv:2509.02604 (Aug 2025, unrefereed) [V-text, skimmed].
  - Theorem 3: for any tree T, at least one of s(T,G), s(T,G) + s(T,Ḡ) or
    s(T,G) − s(T,Ḡ) is recognizable.
  - The proof uses a 2-edge-coloured Kₙ refinement of Kocay.
  - The proof is sketchy. Treat it as a claim, not a source fact.

### A13. Invariant theory: Pouzet 1977, Thiéry 1999/2000, Dufresne et al. 2026
- M. Pouzet, *Quelques remarques sur les résultats de Tutte concernant le problème de
  Ulam*, Publ. Dép. Math. Lyon 14(2) (1977) 1–8 [V-sec, Dufresne et al. bibliography].
- N. M. Thiéry, PhD thesis, Lyon 1999; *Algebraic invariants of graphs; a study based on
  computer exploration*, SIGSAM Bull. 34 (2000) 9–20. M. Pouzet, N. M. Thiéry, C. R. Acad.
  Sci. Paris 333(9) (2001) 821–826, arXiv:0812.3079 [V-abs].
- E. Dufresne, G. Jeronimo, J. Kenkel, H. Lindo, N. Villamizar, *Shuffling the deck:
  invariant theory and the graph reconstruction conjecture*, arXiv:2604.16567 (Apr 2026,
  expository) [V-text].
- **Statements** [V-text, Dufresne et al. §7]:
  - Orbit sums OSₙ(x^M) of multigraph monomials count subgraphs.
  - Thiéry Thm 14.3.7: two k-weighted graphs have the same deck iff they agree on every
    OSₙ(x^{M*}) with M* a multigraph with at least one isolated vertex.
  - *Pouzet's conjecture:* these orbit sums generate the invariant ring k[Vₙ]^{Sₙ}. If
    true, it would imply reconstruction for k-weighted graphs.
  - **It is false for 11 ≤ n ≤ 18** (Thiéry, computational, non-constructive). This does
    not give a counterexample to reconstruction, because a *separating* set suffices.
- **Obstruction value:** the "generation" route is dead. The "separating" route is open
  and is equivalent to the weighted reconstruction conjecture.
- **Lean:** very hard (invariant rings of Sₙ acting on polynomial rings). Not
  recommended.

### A14. Mnukhin; Krasikov–Roditty (not opened)
- V. B. Mnukhin, *The k-orbit reconstruction and the orbit algebra*, Acta Appl. Math. 29
  (1992) 83–117 [V-sec, citation]. Per Oliveira–Thatte, it formulates Ulam's conjecture as
  whether the graph algebra is generated by disconnected graphs. Content UNVERIFIED.
- I. Krasikov, Y. Roditty, *Balance equations for reconstruction problems*, Arch. Math. 48
  (1987) 458–464 [V-sec, citation]. Content UNVERIFIED.
- **Thomassé:** I found no reconstruction result by Thomassé that relates to this angle.
  UNVERIFIED / not located. The caller may have meant Thomassen (Reid–Thomassen 1976 on
  tournaments appears in Kostochka–West's bibliography) or Thiéry (A13).

### A15. Small-deck obstructions: Nýdl; Kostochka–West survey
- A. V. Kostochka, D. B. West, *On reconstruction of graphs from the multiset of subgraphs
  obtained by deleting ℓ vertices*, IEEE Trans. Inform. Theory 67(6) (2021) 3278–3286,
  arXiv:2004.05527 [V-text].
- **Nýdl** (V. Nýdl, Discrete Math. 108 (1992) 373–377) [V-sec, Kostochka–West §1]: for
  every n₀ and 0 < q < 1, there are non-isomorphic n-vertex graphs with n > n₀ and the
  same ⌊qn⌋-deck.
- **Consequence for counting routes:** counts of induced subgraphs on at most qn vertices,
  for any fixed q < 1, never determine G. A Kelly-style argument has to use cards of size
  n − o(n).
- Observation 1.3 [V-text]: the k-deck determines the (k−1)-deck. This is the "deleted
  set" lemma C3 below.

### A16. Reference points (citations only)
- B. Bollobás, *Almost every graph has reconstruction number three*, J. Graph Theory 14
  (1990) 1–4 [V-sec].
- B. D. McKay, *Reconstruction of small graphs and digraphs*, Australas. J. Combin. 83
  (2022) 448–457, arXiv:2102.01942 [V-abs]: graphs with ≤ 13 vertices are
  reconstructible. It also covers tournaments up to 13 vertices, digraphs up to 9 and
  posets up to 13.
- P. K. Stockmeyer, *The falsity of the reconstruction conjecture for tournaments*,
  J. Graph Theory 1 (1977) 19–25, DOI 10.1002/jgt.3190010108 [V-sec]. It gives
  non-reconstructible tournaments on 2^t + 1 and 2^t + 2 vertices; t = 2 gives n = 5, 6,
  which matches our computation.
- W. L. Kocay, *A family of nonreconstructible hypergraphs*, JCTB 42 (1987) 46–63 [V-sec].
- Not consulted this session: Bondy 1991 (*A graph reconstructor's manual*, LMS Lecture
  Notes 166, 221–252; citation [V-sec]), Harary 1974, Nash-Williams 1978 (text),
  Lauri–Scapellato, and Bondy–Hemminger 1977. Their content is UNVERIFIED here.

## Known reconstructible invariants

"Recognizable" here means the same value on hypomorphic graphs with n ≥ 3. Every row is a
literature claim, and none is checked.

| Invariant | Source | Method | Graph-specific? |
|---|---|---|---|
| order n, edge count m | Kelly 1957; folklore | Kelly double count | no (holds for hypergraphs and digraphs) |
| degree sequence, and degrees matched to cards | Kelly 1957 | m − e(G−v) | no |
| s(F, G) and induced s(F, G) for v(F) < n | Kelly 1957 [V-sec] | double count | no |
| the k-deck for every k < n | Kelly; Kostochka–West Obs 1.3 [V-text] | double count | no |
| counts of disconnected spanning subgraphs; disconnected graphs reconstructible | Kocay 1981 [V-sec Thatte, Oliveira–Thatte] | Kocay's lemma | no |
| connectedness | Kelly 1957 | ≥ 2 connected cards | partly |
| number of perfect matchings | Tutte 1979 [V-sec via Li–Shi–Trinks, Oliveira–Thatte] | Kocay with n/2 copies of K₂ (our labelled IE form C4) | no (the same IE works for hypergraph perfect matchings) |
| number of spanning trees | Tutte 1979; Kocay [V-text Thatte Thm 3.12] | Kocay with n−1 copies of K₂ | UNVERIFIED for hypergraphs |
| number of Hamiltonian cycles, Hamiltonicity | Tutte 1979 [V-text Thatte Cor 5.2] | Kocay/Whitney with n copies of K₂ | UNVERIFIED |
| cycles of each length; unicyclic spanning subgraphs by cycle length | Thatte 2005 Thm 3.12 [V-text] | Kocay reductions | UNVERIFIED |
| characteristic polynomial P(G) | Tutte 1979; Kocay; Thatte Cor 5.2 [V-text] | Sachs + Kocay/Whitney | **yes**: fails for 3-uniform hypergraphs (Cooper–Okur) and for tournaments (our n = 5 computation) |
| P′(G) | Biggs Note 2d via Thatte Lemma 1.7 [V-text] | Jacobi principal-minor formula | no (any matrix) |
| chromatic polynomial | Tutte 1979 [V-sec Thatte §1.2]; Whitney/Biggs Thm 12.5 | Whitney expansion over non-quasi-separable induced subgraphs | UNVERIFIED |
| Tutte / rank polynomial | Tutte 1979; Thatte Thm 3.15 [V-text] | Kocay/Whitney | UNVERIFIED |
| matching polynomial | via the perfect-matching count plus Kelly | — | no |
| interlace, U-, ξ-polynomials | Kotek 2009 [V-abs] | Tutte–Kocay style | UNVERIFIED |
| P(G) mod 4 from the polynomial deck (n even) | Spier 2025 [V-abs] | walk matrix over 𝔽₂ | UNVERIFIED |
| planarity | Bilinski–Kwon–Yu, JCTB 97 (2007) 745–756 [V-sec Oliveira–Thatte Ex 2.8] | structural | yes |

**How close is this to a complete invariant?**
- G is determined by the vector (s(F, G))_F over all F with n vertices. In fact s(F, G) for
  the single F ≅ G with e(F) = m already detects G.
- Kelly gives every coordinate with v(F) < n. Kocay gives the disconnected spanning
  coordinates and some linear combinations of the connected spanning ones.
- The gap is exactly the connected spanning subgraph counts. Oliveira–Thatte make it
  precise: the Kocay system has rank d(n), the number of decks. Closing the gap is
  therefore *equivalent* to the conjecture, not a step towards it.
- No known list of algebraic invariants is isomorphism-complete. Cospectral and
  chromatically equivalent non-isomorphic graphs abound, so no single polynomial suffices.

## Obstructions

1. **Generality obstruction:** Kelly, Kocay, Oliveira–Thatte, and ACKR's Thm 2.1 all hold
   for digraphs and for k-uniform hypergraphs. Reconstruction fails in both settings
   (Stockmeyer 1977/81; Kocay 1987). So no proof can consist only of these identities plus
   linear algebra that is agnostic to edge arity or symmetry. *Status: a logical
   consequence of the sources; not itself a paper's theorem.*
2. **Rank-equals-decks** (Oliveira–Thatte Thm 3.4) [V-text]: the Kocay matrix can never
   certify more than the true number of decks. Using it as a proof is equivalent to the
   conjecture for that n.
3. **Pouzet's generation conjecture is false** for 11 ≤ n ≤ 18 (Thiéry) [V-text, via
   Dufresne et al.]. The invariants coming from the deck do not generate the
   Sₙ-invariant ring.
4. **Dimension obstruction for linear deck maps** (our observation, see A9): the linear
   map [G] ↦ Σᵥ[G − v] has a nontrivial kernel. Injectivity has to come from the 0/1
   structure of [G] − [H], not from linear algebra on the whole space. Stanley's and
   Lovász's arguments work for edges only because the edge-deletion map is injective in
   the dense range.
5. **Small cards are not enough** (Nýdl 1992) [V-sec]: for every q < 1, the ⌊qn⌋-deck
   fails to determine G infinitely often.
6. **Polynomial decks are weaker than decks:**
   - The matching polynomial is not polynomial-reconstructible in general (Li–Shi–Trinks)
     [V-abs].
   - The PRP for the characteristic polynomial is open [V-abs].
   - The hypergraph PRP is false (Cooper–Okur) [V-abs].
   So routes through "deck of polynomials" must keep more than the polynomials.

## What breaks in failing settings

| Ingredient | Tournaments / digraphs | k-uniform hypergraphs, k ≥ 3 | Infinite graphs | Verdict |
|---|---|---|---|---|
| Kelly's lemma | holds | holds | fails (no division by n − v(F)) | cannot alone prove the conjecture |
| Kocay's lemma | holds | holds | fails | cannot alone prove the conjecture |
| ACKR / Nash-Williams | holds (any group action) | holds (edge version) | can hold (ACKR allow infinite X, finite stabiliser) | edge reconstruction only; not a vertex route |
| P′ = Σ P(G − v) | holds (any matrix) | n/a | n/a | universal; carries no graph-specific power |
| P(G) recognizable | **fails** (n = 5 pair, constant term differs; our computation) | **fails** (Cooper–Okur) | n/a | **graph-specific**; a candidate ingredient of a real proof, but not complete |
| Sachs elementary subgraphs (K₂ and cycles) | the digraph analogue (linear subdigraphs) does not reconstruct det | different (Veblen hypergraphs) | n/a | this is where graph symmetry enters |
| perfect-matching count via IE | n/a | holds | fails | universal invariant, a foundation lemma only |

Rule of thumb for this fleet:
- A route to the *full* conjecture must use some ingredient in the "graph-specific" rows:
  the symmetry of the adjacency matrix, or edges being 2-sets in a way that hypergraphs
  break.
- Candidate lemmas about recognizable *invariants* may be universal. That is harmless,
  because they are true facts.

## Formalizable candidate steps

All of these bodies elaborate against `Recon.Basic` with `open SimpleGraph`. I ran
`lake env lean` on a throwaway file in the session scratchpad: no errors, and a deliberate
error was reported, so the check was live. This is not a submission and not a result.
**desk.py propose was not run.** Steps that need `DecidableRel` quantify over the instance.
`Nat.card` and `ncard` avoid `Fintype` instances.

Kelly's lemma bodies (`kelly_copy_sum`, `kelly_lemma_labelled`, `kelly_lemma_induced`,
`kelly_lemma_rooted`) are already in the Kelly note. C1/C2 below are the induced-embedding
variants, listed only for completeness.

```lean
-- C1 kelly_embedding_count_sum (pure counting; all n, k)
∀ (n k : ℕ) (F : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n)),
  (n - k) * Nat.card (F ↪g G) = ∑ v : Fin n, Nat.card (F ↪g Recon.card G v)

-- C3 kelly_deleted_edge_power_sum  (generalized Kelly: k-deck data from the deck; any n)
∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Recon.Hypomorphic G H → ∀ s k : ℕ, 1 ≤ s →
  ∑ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
      (G.induce ((↑S : Set (Fin n))ᶜ)).edgeSet.ncard ^ k =
    ∑ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
      (H.induce ((↑S : Set (Fin n))ᶜ)).edgeSet.ncard ^ k

-- C4 kelly_perfect_matching_incl_excl  (pure counting identity; every G, every n)
∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  (((n / 2).factorial * Nat.card {M : G.Subgraph // M.IsPerfectMatching} : ℕ) : ℤ) =
    ∑ S : Finset (Fin n), (-1 : ℤ) ^ S.card *
      ((G.induce ((↑S : Set (Fin n))ᶜ)).edgeSet.ncard : ℤ) ^ (n / 2)

-- C5 kelly_perfect_matching_count  (Tutte 1979)
∀ n : ℕ, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H →
  Nat.card {M : G.Subgraph // M.IsPerfectMatching} =
    Nat.card {M : H.Subgraph // M.IsPerfectMatching}

-- C6 kelly_charpoly_derivative_sum  (Biggs Note 2d / Jacobi; every G)
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  Polynomial.derivative (G.adjMatrix ℤ).charpoly =
    ∑ v : Fin n, ((Recon.card G v).adjMatrix ℤ).charpoly

-- C7 kelly_charpoly_derivative  (recognizable)
∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
  Recon.Hypomorphic G H →
    Polynomial.derivative (G.adjMatrix ℤ).charpoly =
      Polynomial.derivative (H.adjMatrix ℤ).charpoly

-- C8 kelly_charpoly  (Tutte 1979; long-term; graph-specific)
∀ n : ℕ, 3 ≤ n → ∀ (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
  Recon.Hypomorphic G H → (G.adjMatrix ℤ).charpoly = (H.adjMatrix ℤ).charpoly

-- C9 edge_lovasz  (edge program; edge-hypomorphism inlined because Basic.lean lacks it)
∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
  (∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet,
      Nonempty (G.deleteEdges {e.1} ≃g H.deleteEdges {(σ e).1})) →
  n * (n - 1) < 4 * G.edgeSet.ncard → Nonempty (G ≃g H)

-- C9' edge_muller
∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
  (∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet,
      Nonempty (G.deleteEdges {e.1} ≃g H.deleteEdges {(σ e).1})) →
  n.factorial < 2 ^ (G.edgeSet.ncard - 1) → Nonempty (G ≃g H)

-- C10 Pouzet / Gottlieb set lemma (no Recon.*; a library lemma for the edge program)
∀ (v t k : ℕ) (U U' : Finset (Finset (Fin v))),
  (∀ A ∈ U, A.card = t) → (∀ A ∈ U', A.card = t) → t ≤ k → k + t ≤ v →
  (∀ K : Finset (Fin v), K.card = k →
      (U.filter (fun A => A ⊆ K)).card = (U'.filter (fun A => A ⊆ K)).card) →
  U = U'

-- C11 kelly_matching_count  (k-matchings with 2k < n; Kelly-type double count)
∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Recon.Hypomorphic G H → ∀ k : ℕ, 2 * k < n →
  Nat.card {M : Finset (Sym2 (Fin n)) // M.card = k ∧ (∀ e ∈ M, e ∈ G.edgeSet) ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x, x ∈ e → x ∉ f)} =
  Nat.card {M : Finset (Sym2 (Fin n)) // M.card = k ∧ (∀ e ∈ M, e ∈ H.edgeSet) ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x, x ∈ e → x ∉ f)}
```

### Notes for fidelity reviewers and builders

- **C3** holds for every n. The double count reads
  s · Σ_{|S|=s} f(G − S) = Σᵥ Σ_{S′ ⊆ V∖{v}, |S′|=s−1} f((G − v) − S′),
  and the inner sum is an isomorphism invariant of the card. I checked the identity
  numerically (200 random cases, 0 failures). The hypothesis `1 ≤ s` is essential: at
  s = 0 the claim is the edge count raised to the power k, which fails at n = 2 (K₂ versus
  2K₁).
- **C4** is the labelled Kocay/inclusion–exclusion identity:
  - Let k = ⌊n/2⌋ and count the k-tuples of edges whose endpoints cover V.
  - By inclusion–exclusion over the uncovered set S, this count is
    Σ_S (−1)^|S| e(G − S)^k.
  - A covering tuple with 2k = n endpoints must be an ordered perfect matching, giving
    k! · pm(G).
  - For odd n, both sides are 0. For n = 0, both sides are 1 (the empty matching).
  - I checked it numerically (300 random graphs, n ≤ 8, 0 failures). It is **derived
    here**; the source for the invariant itself is Tutte.
- **C5 should be a reduction:** C4 (for G and for H), C3 with k = n/2 for every s ≥ 1,
  and `kelly_edge_count` for the S = ∅ term together give C5. The reduction proof is
  short: rewrite both sides with C4 and split the sum by |S|. This is a natural `reduce`
  target.
- **C6** was checked numerically (60 random graphs, n ≤ 7, sympy, 0 failures). It holds
  for every matrix, not only adjacency matrices.
  - C7 = C6 + `Iso.reindex_adjMatrix` + `Matrix.charpoly_reindex`.
  - C6 does not need `3 ≤ n`, and neither does C7 (at n ≤ 2 it is still a true identity).
- **C8** at n ≤ 13 follows from McKay, but that is not a Lean proof. It is a long-term
  target. Do not attack it before Sachs' theorem and a Hamiltonian-cycle count exist.
- **C9/C9′** need a human decision on the edge-deck definition before they can be
  proposed (the `edge` program is not opened). The inline form uses `deleteEdges`.
  Fidelity check: on n = 4, K₁,₃ and K₃ + K₁ are edge-hypomorphic with m = 3, and
  4·3 < 4·3 is false, so the hypothesis correctly excludes them.
- **C10** does not mention `Recon.*`. It is a set-system lemma (Gottlieb/Pouzet). Propose
  it only if a program wants library lemmas.
- **C11** formalizes matchings as Finsets of `Sym2` so that it avoids `Subgraph`. The
  disjointness clause is pairwise vertex-disjointness. Proof: each k-matching of G avoids
  exactly n − 2k vertices, and the matchings of G avoiding v correspond to the matchings
  of `card G v`. Crossing the subtype is the fiddly part.

### Suggested ids and programs
- `kelly`: `kelly_deleted_edge_power_sum` (C3), `kelly_perfect_matching_incl_excl` (C4),
  `kelly_perfect_matching_count` (C5), `kelly_charpoly_derivative_sum` (C6),
  `kelly_charpoly_derivative` (C7), `kelly_matching_count` (C11), and long-term
  `kelly_charpoly` (C8).
- `edge` (when opened): `edge_lovasz` (C9), `edge_muller` (C9′), and a library lemma
  `edge_pouzet_set_lemma` (C10).

### Lean difficulty estimates

| Step | Estimate | Main work |
|---|---|---|
| C1 | easy–moderate (100–200 lines) | sigma-type bijection; `Finset.card_compl` of the range |
| C3 | moderate (200–350) | double counting (v, S) with v ∈ S; iso `G.induce Sᶜ ≅ (card G v).induce …` across subtypes |
| C4 | moderate–hard (300–500) | `Finset.inclusion_exclusion_card_inf_compl`; bijection between covering tuples and ordered perfect matchings |
| C5 | easy given C3 and C4 (reduction) | regroup `∑ S : Finset` by card (`Finset.sum_powerset` / `powersetCard`) |
| C6 | moderate–hard (300–600) | Jacobi formula for d/dX det(X·1 − A) via `det_apply` + `derivative_prod_finset`; principal submatrix = card adjacency (`Embedding.submatrix_adjMatrix`, reindex `Fin` vs subtype) |
| C7 | easy given C6 | `Iso.reindex_adjMatrix`, `charpoly_reindex` |
| C8 | very hard (thousands) | Sachs theorem, Kocay chains, Hamiltonian cycle count |
| C9/C9′ | hard (800–1500) | Nash-Williams inclusion–exclusion over `Equiv.Perm (Fin n)` |
| C10 | moderate–hard (~400) | Gottlieb rank or a direct Pouzet counting induction |
| C11 | moderate (250–400) | Kelly double count on Finset matchings across the card subtype |

## Open gaps

1. Kocay 1981: which paper is the primary source (Ars Combin. 11 or Congr. Numer. 31)?
   Neither was opened.
2. Nash-Williams 1978, Bondy 1991, Lauri–Scapellato, Harary 1974 and Tutte 1979/1998 were
   not opened. Every claim attributed to them comes from secondary sources, so a reader
   with library access should confirm them.
3. Recognizability of P(G) for **digraphs in general**: our n = 5 tournament computation
   shows failure for tournaments. A red-team re-run, and a check against McKay's
   tournament list, would make this solid. It is not in the literature as far as I found.
4. Is the number of spanning trees or Hamiltonian cycles recognizable for tournaments or
   3-uniform hypergraphs (with the appropriate notions)? UNVERIFIED. If it is not, those
   invariants are also graph-specific, which is useful for routes.
5. A labelled inclusion–exclusion form of the *full* Kocay lemma for arbitrary F₁,…,F_k
   (generalizing C4) would give disconnected-graph reconstruction and spanning-tree counts
   without isomorphism-class bookkeeping. Its exact statement still needs to be designed.
   The candidate is Πᵢ-tuples covering V = Σ_S (−1)^|S| Πᵢ s(Fᵢ, G − S).
6. Mathlib lacks: the chromatic polynomial, the Tutte polynomial, the matching polynomial,
   the matrix-tree theorem, Sachs' theorem, the Jacobi derivative formula for charpoly,
   and inclusion-matrix rank (Gottlieb). See `notes/mathlib/algebraic_methods.md`.
7. Pouzet's *separating* version (A13) is open and equivalent to the weighted conjecture.
   No route is known.
8. Thomassé: no relevant result located (A14).
