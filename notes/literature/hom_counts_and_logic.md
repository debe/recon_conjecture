# Homomorphism counts, counting logics and the deck

Librarian sweep, 2026-11-25. Angle: homomorphism counts, homomorphism indistinguishability,
finite model theory (counting logics, Weisfeiler–Leman, game comonads) as a semantics for the
deck. Working hypothesis of the sweep: the conjecture is true; we look for proof routes.

Verification tags used below:
- **[text]**: the statement was read in the paper's own text during this sweep (PDF extracted).
- **[abstract]**: only the arXiv abstract or listing was read.
- **[secondary]**: read in another paper's text that cites it.
- **UNVERIFIED**: from memory or from a search snippet only. Do not build on it without checking.

Nothing in this note is a result of this repository. The only result here is
`found_iso_hypomorphic` (checked). Everything else is literature, sketch or candidate.

## Summary

1. For n-vertex graphs, having the same deck is the same as being homomorphism
   indistinguishable over all graphs on at most n − 1 vertices. Kelly's lemma and Möbius
   inversion give this, and it is stated in this form by van Dobben de Bruyn et al. (2026,
   Lemma 3.5) [text]. So the conjecture says: for n ≥ 3, hom counts from graphs with fewer
   than n vertices determine an n-vertex graph.
2. Lovász (1967) needs hom counts from graphs on at most n vertices for n-vertex targets. The
   whole gap is the top layer: counts of spanning (surjective-on-vertices) homomorphisms. The
   hom-count language does not shrink this gap. It is the classical Kocay/Tutte "spanning
   subgraph" core under another name.
3. The general theory cannot close the gap by itself. Every componental class that is
   essentially finite, including "connected graphs on ≤ n − 1 vertices", is homomorphism
   distinguishing closed over all targets (van Dobben de Bruyn et al. 2026, Prop. 4.6)
   [text]. The separating pairs it builds have far more than n vertices, so a proof must use
   the fact that the target has exactly n vertices. Nýdl (1992) gives non-isomorphic n-vertex
   graphs with the same counts from ≤ αn vertices for any α < 1 [secondary].
4. Lovász's theorem, Kelly's lemma and the whole hom/WL/comonad machinery are signature
   generic: they hold for digraphs and k-uniform hypergraphs. There, reconstruction fails
   (Stockmeyer 1977; Kocay 1987). Any route built only from this machinery is broken. A real
   route needs an ingredient specific to undirected graphs, such as the spectral theory of the
   symmetric adjacency matrix (Tutte's characteristic-polynomial theorem).
5. Formalizable now: a stratified "Kelly lemma for homomorphisms" (elementary double count,
   numerically sanity-checked here), the deck ⇔ hom-counts-below-order reduction, and two
   published equivalent reformulations of RC (isolated vertex, surjective homs). These need
   only edge-count and degree recognizability. All Props below elaborate against
   `Recon.Basic` in a throwaway probe. That is not a result.

## Sources

### S1. van Dobben de Bruyn, Marquès, Roberson, Seppelt, Spitzer, Zeman (2026). The one paper that makes the connection explicit.
- **Citation.** "Topological and Geometric Perspectives on Homomorphism Indistinguishability",
  arXiv:2610.07927v1 (6 Oct 2026), math.CO / cs.DM / cs.LO. Preprint, not refereed.
- **[text] Lemma 3.5.** Stated for looped graphs G°. For ℓ ≥ 1, the following are equivalent:
  (ii) hom(F,G) = hom(F,H) for all F on at most ℓ vertices; (iii) there is a bijection π
  between the vertex subsets of size ≤ ℓ of G and of H with |S| = |π(S)| and
  G[S] ≅ H[π(S)]. In the proof, the same equivalence covers sub(F,·) and indsub(F,·) counts
  for F on ≤ ℓ vertices, via Curticapean–Dell–Marx (S6). For simple graphs and ℓ = n − 1 with
  |V(G)| = |V(H)| = n, (iii) is hypomorphism plus Kelly's lemma. This is our reduction
  (Section "The reduction").
- **[text] Example 3.8.** The following are equivalent:
  (i) the Ulam–Kelly conjecture;
  (ii) hypomorphicity is a homomorphism indistinguishability relation over a componental class;
  (iii) G ≈ H ⇒ K ⊗ G ≈ K ⊗ H for every K (⊗ = categorical/tensor product);
  (iv) G ≈ H ⇒ K + G ≈ K + H (+ = disjoint union).
  Their hypomorphism includes "same number of edges". This only matters for n ≤ 2 (their
  footnote 2).
  - (iv) ⇒ (i) is elementary. If G ≈ H then G + K₁ ≈ H + K₁ via some σ. Degrees are
    recognizable, so σ maps the added isolated vertex to an isolated vertex, and deleting an
    isolated vertex of H + K₁ gives H.
  - (iii) ⇒ (i) uses Lemma 6.38: Σ_v hom(F, G − v) is a graph motif parameter with non-zero
    coefficient on F + K₁. It also uses Seppelt's interpolation Lemma 6.39 ([33, Lemma 6]):
    if ≈ is closed under K ⊗ · and respects Σ η_F hom(F,·), it respects each hom(F,·) with
    η_F ≠ 0. Together they give hom(F + K₁, ·), hence hom(F, ·), for all F. Lovász finishes.
- **[text] Definition 4.1 / Prop. 4.6.** cl(F) = {F′ : ∀ G,H, G ≡_F H ⇒ hom(F′,G) = hom(F′,H)}.
  "Every essentially finite componental graph class is homomorphism distinguishing closed."
  To separate a connected K from a connected F, the proof takes a graph G with
  hom(F,G) ≠ hom(K,G) (Lovász) and builds X = G ⊗ K and Y = hom(F,G)·K. Both are much
  larger than n.
- **[text] Theorems 3.6/3.7.** These give an axiomatisation of homomorphism
  indistinguishability relations (closure under ⊗K, +K, cancellation of +K and of n·, an
  approximation axiom (v), and a ⊗K_n axiom for simple graphs).
- **Failing settings.** The algebra is over the semiring of graphs. The authors say most of it
  applies to any countable commutative cancellative semiring (Thm 6.27, [text], conclusion).
  So it is signature generic. Example 3.8 is an equivalence, so it is not at risk. Any claimed
  proof of (iii) or (iv) must fail for digraphs.
- **Lean.**
  - (iv) ⇒ (i): low to medium. It needs `SimpleGraph.sum`, cards of a sum, and degree
    recognizability on a general Fintype.
  - (iii) ⇒ (i): hard. It needs motif parameters, a Vandermonde-type interpolation, and
    Lovász's theorem in full generality.
  - Prop 4.6: hard, and not useful for us.

### S2. Lovász (1967), "Operations with structures".
- **Citation.** Acta Math. Acad. Sci. Hungar. 18 (1967) 321–328, doi:10.1007/BF02280291
  [secondary: reference list of S1].
- **Statement [secondary, S1 Thm 9.4].** Two finite graphs (in the original, finite relational
  structures) F, K are isomorphic iff hom(F,G) = hom(K,G) for all G. The dual form, iso iff
  hom(F,G) = hom(F,H) for all F, is the one used throughout S1 and S3–S8.
- **Proof idea (standard; the original was not read).**
  - hom(F,G) = Σ_P inj(F/P, G) over partitions P of V(F) with no edge inside a block.
  - Möbius inversion on the partition lattice gives inj(F,·) from hom(F/P,·), and every F/P
    has ≤ |V(F)| vertices.
  - Then inj(G,H) > 0 and inj(H,G) > 0 give G ≅ H.
  - **Order-restricted corollary.** For n-vertex G, H, hom counts from F on ≤ n vertices
    suffice. (Elementary from the proof; I did not find it stated in a source.)
- **Failing settings.** It holds for digraphs and hypergraphs (relational structures), so it
  carries no graph-specific information. It fails for infinite targets: the counts are
  infinite.
- **Lean.** Medium to hard. Mathlib has the Möbius function of a locally finite poset
  (`IncidenceAlgebra.mu`, `moebius_inversion_top/bot`) and `Finpartition`. It has neither the
  partition-lattice Möbius values nor graph quotients `F/P` packaged; `SimpleGraph.map` along
  the quotient map is the natural encoding. An order-n variant via injective copies is easy
  (candidate C).

### S3. Dvořák (2010), "On recognizing graphs by numbers of homomorphisms".
- **Citation.** J. Graph Theory 64(4) (2010) 330–342, doi:10.1002/jgt.20461 [secondary: S1
  references; journal page paywalled].
- **Statement.** Homomorphism indistinguishability over graphs of treewidth ≤ k is equivalent
  to k-WL equivalence. Also, 2-degenerate graphs already determine a graph up to isomorphism.
  This is [secondary] via S4, the Dawar–Jakl–Reggio abstract, and a LICS 2026 citation; the
  theorem numbers are UNVERIFIED.
- **Relevance.** Every F on ≤ n − 1 vertices has treewidth ≤ n − 2. So for n-vertex graphs,
  C^{n−1} equivalence (equivalently (n−2)-WL) implies hypomorphism. The converse is open
  exactly as far as RC is: it holds if RC holds.
- **Failing settings.** WL and C^k are defined for every relational signature.
- **Lean.** Hard. Mathlib has no WL algorithm, no counting logic and no treewidth.

### S4. Dell, Grohe, Rattan (2018), "Lovász Meets Weisfeiler and Leman".
- **Citation.** ICALP 2018, LIPIcs 107; arXiv:1802.08876 [abstract].
- **Statement [abstract].** Colour refinement fails to distinguish G, H iff they have equal hom
  counts from all trees. With non-negativity dropped, this becomes equality of walk counts.
  The results extend to bounded treewidth and k-WL, and to Sherali–Adams.
- **Relevance.** Two RC consequences are natural weaker targets: "hypomorphic ⇒
  colour-refinement equivalent" and "hypomorphic ⇒ same walk counts". Neither status was
  found in any source read here; see Open gaps.
- **Lean.** Hard for the full theorem. Walk counts are easy to state:
  `adjMatrix_pow_apply_eq_card_walk`.

### S5. Grohe (2020), "Counting Bounded Tree Depth Homomorphisms".
- **Citation.** LICS 2020; arXiv:2003.08164 [abstract].
- **Statement [abstract].** C equivalence at quantifier rank ≤ k iff homomorphism
  indistinguishability over graphs of tree depth ≤ k.
- **Relevance.** F on ≤ n − 1 vertices have tree depth ≤ n − 1. So for n-vertex graphs,
  C-equivalence at quantifier rank n − 1 implies hypomorphism. This is a logic-side
  sufficient condition, not a route to RC.
- **Lean.** Hard (no logic in Mathlib).

### S6. Curticapean, Dell, Marx (2017), "Homomorphisms Are a Good Basis for Counting Small Subgraphs".
- **Citation.** STOC 2017, 210–223, doi:10.1145/3055399.3055502 [secondary: S1 references].
- **Statement [secondary, as used in S1 Lemma 3.5].** For graphs on ≤ ℓ vertices, the
  functions hom(F,·), sub(F,·) and indsub(F,·) span the same vector space. The bases are
  related by triangular transforms: hom ↔ inj through quotients, and inj ↔ indsub through
  edge supersets on the same vertex set.
- **Lean.** Medium. These are two finite triangular inversions, and Mathlib has
  `inclusion_exclusion_*` and `IncidenceAlgebra.mu`.

### S7. Roberson (2022/2026), "Oddomorphisms and homomorphism indistinguishability over graphs of bounded degree".
- **Citation.** arXiv:2206.10321 [abstract]. Published as JCTB 181 (2026) 1–61,
  doi:10.1016/j.jctb.2026.07.003 [secondary: S1 references].
- **Statement [abstract].**
  - Homomorphism indistinguishability over bounded-degree graphs is not isomorphism.
  - Classes closed under disjoint unions, under restriction to components and under weak
    oddomorphisms are homomorphism distinguishing closed.
  - Roberson conjectures that every class closed under minors and disjoint unions is
    homomorphism distinguishing closed. S1 cites counterexamples to a "Strong Roberson
    Conjecture" (Kristjánsson, arXiv:2610.03550) [secondary, UNVERIFIED content].
- **Relevance.** It introduces the closure cl(·) and the notion of an h.d.c. class. Both
  quantify over all targets.
- **Lean.** Hard.

### S8. Neuen (2024), "Homomorphism-Distinguishing Closedness for Graphs of Bounded Tree-Width".
- **Citation.** STACS 2024, LIPIcs 289, 53:1–53:12, doi:10.4230/LIPIcs.STACS.2024.53
  [secondary: S1 references]; arXiv:2304.07011 [abstract].
- **Statement [abstract].** The class T_k of graphs of treewidth ≤ k is h.d.c. for every k.
  Corollary in S1 (Cor. 4.4) [text]: {F : tw(F) ≤ k or Δ(F) ≤ d} is h.d.c.
- **Lean.** Hard. Not needed.

### S9. Seppelt (2023/2024), "Logical equivalences, homomorphism indistinguishability, and forbidden minors".
- **Citation.** MFCS 2023, doi:10.4230/LIPIcs.MFCS.2023.82; journal version Inf. Comput. 301
  (2024) 105224, doi:10.1016/j.ic.2024.105224 [secondary: S1]; arXiv:2302.11290 [abstract].
- **Statement [abstract].**
  - Self-complementary logics with a hom-indistinguishability characterisation are
    characterised by minor-closed classes.
  - It classifies essentially finite classes that are h.d.c.
  - Lemma 6 (the interpolation lemma) and Theorem 7 (closure under +K forces a componental
    class) are used in S1 [secondary].
- **Lean.** Hard.

### S10. Mančinska, Roberson (2020), "Quantum isomorphism is equivalent to equality of homomorphism counts from planar graphs".
- **Citation.** FOCS 2020, 661–672, doi:10.1109/FOCS46700.2020.00067 [secondary: S1];
  arXiv:1910.06958 [abstract].
- **Statement [abstract].** Quantum isomorphic ⇔ hom-indistinguishable over planar graphs.
  Quantum isomorphic non-isomorphic pairs exist.
- **Relevance.** This is a warning shape: an infinite, natural, minor-closed class (planar)
  does not determine graphs. A class of "small" patterns needs the order restriction.
- **Lean.** Very hard.

### S11. Dawar, Jakl, Reggio (2021), "Lovász-Type Theorems and Game Comonads"; Abramsky, Dawar, Wang (2017), "The pebbling comonad in finite model theory".
- **Citations.** LICS 2021, doi:10.1109/LICS52264.2021.9470609, arXiv:2105.03274 [abstract].
  LICS 2017, arXiv:1704.05124 [abstract].
- **Statement [abstract].**
  - DJR give a categorical Lovász theorem in any locally finite category with pushouts and a
    proper factorisation system, and recover Dvořák (treewidth / k-WL) and Grohe (tree depth
    / C_k) via game comonads.
  - ADW present the existential k-pebble game as a comonad.
- **Relevance.** This is the most signature-generic setting of all. A deck-comonad, if
  someone defined one, would live in the same category for digraphs. So it cannot by itself
  give RC. I found no paper that defines a "deck comonad": open gap, UNVERIFIED negative.
- **Lean.** Very hard. Mathlib has category theory, but nothing connecting it to SimpleGraph
  counting.

### S12. ℓ-deck (small cards) literature. This gives the exact hom-count meaning of "n − 1 is needed".
- **Groenland, Johnston, Scott, Tan, "Reconstruction from smaller cards".** arXiv:2103.13359.
  The PDF was read [text].
  - **Lemma 8.** The ℓ-deck determines sub(H,G) and indsub(H,G) for |V(H)| ≤ ℓ.
    Proof: each copy of H lies in exactly C(n−|H|, ℓ−|H|) of the ℓ-cards.
  - **Theorem 4.** Trees are reconstructible from the (n − r)-deck for r up to about n/9.
  - **Theorem 5.** Connectedness is recognizable from the ℓ-deck once ℓ ≥ 9n/10.
  - **Theorem 7.** The degree sequence is recognizable from the ℓ-deck once
    ℓ ≥ √(2n log 2n).
- **Nýdl (1992).** "Finite undirected graphs which are not reconstructible from their large
  cardinality subgraphs", Discrete Math. 108 (1992) 373–377 [secondary: GJST Theorem 2]. For
  every n₀ and 0 < α < 1 there are n > n₀ and two non-isomorphic n-vertex graphs with the same
  multiset of subgraphs of order ≤ αn.
  - **In hom language.** Hom counts from F_{≤αn} do not determine n-vertex graphs.
- **Kostochka, West (2021).** Survey, IEEE Trans. Inf. Theory 67(6) 3278–3286 [secondary:
  GJST refs]; arXiv:2004.05527 [abstract].
- **Spinoza, West (2019).** J. Graph Theory 90(4) 497–522 [secondary]. Pₙ and
  C_{⌈n/2⌉+1} + P_{⌊n/2⌋−1} have equal ℓ-decks for ℓ ≤ ⌊n/2⌋ [secondary: GJST p. 3].
- **Lean.** Kelly's lemma for ℓ-decks is medium. Nýdl's construction is hard and not needed.

### S13. Kocay / Tutte, the spanning-subgraph core.
- **Kocay's lemma.** For a sequence F₁..F_k, Π s(F_i, G) = Σ_X c(F,X)·s(X,G), where c counts
  covers of X by the F_i [abstract: Stark, "Generalization and Power of Kocay's Lemma in Graph
  Reconstruction", arXiv:2509.02604]. Consequence (Kocay 1981): counts of disconnected
  spanning subgraphs of each type are reconstructible. UNVERIFIED from Kocay's own text.
  Source: W. L. Kocay, "Some new methods in reconstruction theory", 1981 (venue UNVERIFIED).
- **Tutte (1979).** "All the king's horses" (in Bondy–Murty eds., Graph Theory and Related
  Topics, Academic Press) [secondary: GJST ref 36]. It is said to show that the characteristic
  polynomial, the number of Hamiltonian cycles and the Tutte polynomial are reconstructible
  (content UNVERIFIED).
  - **In hom language.** hom(C_k, G) = tr(A^k) for every k, so cycles lie in the
    target-restricted closure (see below).
- **Godsil–McKay walk counts.** Reconstructing the complement's characteristic polynomial
  gives walk counts, hence hom(P_k, ·) for all k. UNVERIFIED: memory of Godsil & McKay, JCTB
  30 (1981).

### S14. Prior Lean work (external, unaudited)
- **Repository.** `SamuelSchlesinger/reconstruction-conjecture` on GitHub, Lean v4.28.0
  (README read 2026-11-25). No licence file, so **do not copy code**. Use it as a roadmap
  only. Its `SameDeck` uses one vertex type V with σ : V ≃ V; our `Hypomorphic` is
  heterogeneous.
- **README claims (not audited).**
  - Kelly's lemma for induced copies.
  - `SameDeck.injHomCount_eq`: injective-hom counts for patterns on < |V| vertices
    (`HomCount.lean`).
  - Kocay host cover counts (`KocayHost.lean`).
  - tr(A^k) for k < |V|.
  - The constant term of the characteristic polynomial, reduced to Hamiltonian-cycle counts
    (staged hypothesis).
  - Disconnected and regular graphs reconstructible.
- **sorry check.** `grep sorry` on the files fetched found one, in the conjecture statement
  itself (`Basic.lean`). No other file was checked.

## The reduction in precise terms

Notation for finite simple graphs:
- hom(F,G) is the number of homomorphisms F → G;
- inj(F,G) is the number of injective homomorphisms (Mathlib `labelledCopyCount G F`);
- ind(F,G) is the number of vertex subsets S with G[S] ≅ F;
- h_j(F,G) is the number of homomorphisms F → G whose image has exactly j vertices.

**Proposition R (equivalence).** For every n and graphs G, H on n vertices, the following are
equivalent:
- (a) G and H are hypomorphic (`Recon.Hypomorphic`);
- (b) ind(F,G) = ind(F,H) for every F on exactly n − 1 vertices (equal card multiplicities);
- (c) ind(F,G) = ind(F,H) for every F on ≤ n − 1 vertices;
- (d) inj(F,G) = inj(F,H) for every F on ≤ n − 1 vertices;
- (e) hom(F,G) = hom(F,H) for every F on ≤ n − 1 vertices.

Proof sketch (paper only):
- (a) ⇔ (b): group the cards by isomorphism class.
- (b) ⇒ (c): Kelly's lemma, Σ_v ind(F, G − v) = (n − |F|)·ind(F,G).
- (c) ⇔ (d): inj(F,G) = Σ_K ind(K,G)·inj(F,K) over K on |V(F)| vertices. This is triangular
  in the edge-superset order (S6).
- (d) ⇔ (e): hom = Σ over quotients of inj, and quotients have ≤ |V(F)| vertices. This is
  triangular in the vertex count (S2, S6).
- No hypothesis n ≥ 3 is needed. At n = 2, K₂ and 2K₁ satisfy (a)–(e) and are not
  isomorphic, which is consistent.
- S1 Lemma 3.5 is the published form of (c) ⇔ (e), for looped graphs [text].

**Stratified Kelly lemma for homomorphisms (direct route to (a) ⇒ (e)).** For any finite F,
any j and n-vertex G:

  Σ_{v ∈ V(G)} h_j(F, G − v) = (n − j)·h_j(F, G).

Proof:
- A hom F → G − v is a hom F → G that misses v.
- A hom with j-vertex image misses exactly n − j vertices.
- Isomorphic cards have equal h_j.

So h_j(F,·) is recognizable for every j < n and every F, of any size. When |V(F)| < n, every
hom has image size < n, so hom(F,·) = Σ_{j<n} h_j(F,·) is recognizable. With j = |V(F)|, the
same identity gives inj(F,·). This avoids Möbius inversion for the (a) ⇒ (e) direction.
Numerical sanity check: 200 random (F, G) with n ≤ 6 and |F| ≤ 5, with no violation (script in
the session scratchpad; not a result).

**Corollary (the gap).**
- RC ⇔ for n ≥ 3, (e) ⇒ G ≅ H.
- By Lovász at order n, hom from F on ≤ n vertices forces G ≅ H. Hence:

  RC ⇔ for every n ≥ 3 and every F, the surjective-on-vertices count h_n(F,·) is recognizable.

- In fact F = G alone suffices. If h_n(G,H) = h_n(G,G) ≥ 1, a surjective hom Fin n → Fin n is
  a bijection, and with equal edge counts it is an isomorphism. This is candidate E: an exact
  and elementary equivalence. It is also why the hom language adds no leverage by itself. The
  missing information is exactly the spanning layer, which is Kocay's and Tutte's
  "spanning-subgraph" problem.

**Target-restricted closure (the right notion; not found in the literature).**

  cl_n(F) := {F′ : ∀ G,H on n vertices, G ≡_F H ⇒ hom(F′,G) = hom(F′,H)}.

- RC at order n ⇔ cl_n(F_{≤n−1}) contains every n-vertex graph. Equivalently, it contains G
  for each G.
- Known members beyond F_{≤n−1}:
  - disjoint unions of members (trivially);
  - all cycles C_k (Tutte, UNVERIFIED);
  - all paths P_k (Godsil–McKay, UNVERIFIED);
  - every F all of whose n-vertex quotients are disconnected (Kocay, UNVERIFIED).
- The all-targets closure cl(·) is useless here: S1 Prop 4.6 says F_{≤n−1} (componentally
  closed) is already closed over all targets.

## What breaks in the failing settings

| Ingredient | Digraphs / tournaments (fails: Stockmeyer 1977, J. Graph Theory 1(1) 19–25, doi:10.1002/jgt.3190010108; erratum doi:10.1002/jgt.20398) | k-uniform hypergraphs, k ≥ 3 (fails: Kocay 1987, JCTB 42, 46–63) | Infinite graphs (fails: Fisher 1969; locally finite trees: Bowler et al. 2017) |
|---|---|---|---|
| Kelly's lemma, stratified hom Kelly | holds (same double count) | holds | division by n − j meaningless; counts infinite |
| Proposition R (deck ⇔ hom counts below order) | holds (relational structures) | holds | meaningless |
| Lovász 1967 | holds (stated for relational structures) | holds | fails / not defined |
| WL / C^k / game comonads | defined and work for any signature | same | partially (infinite structures), no counting |
| h.d.c. theory (S1, S7–S9) | analogous algebra (S1: any cancellative semiring) | same | n/a |
| Example 3.8 equivalences | analogue presumably holds and both sides are false | same | n/a |

Consequences:
1. A route that uses only Kelly/Kocay counting, Lovász-style linear algebra over hom counts, WL
   or C^k, or comonads proves too much. It would reconstruct Stockmeyer's tournaments and
   Kocay's 3-graphs, so it is **broken**.
2. A valid route must use something only undirected binary simple graphs have. Candidates:
   - the symmetric adjacency matrix (real spectrum, Tutte's characteristic-polynomial
     theorem, and Godsil–McKay via the complement);
   - Sym2-specific double counting: Σ deg = 2|E|, i.e., the edge-count formula uses that each
     edge has exactly 2 endpoints;
   - planarity- or structure-specific arguments.
   The k-uniform version of the edge-count formula still works (divide by n − k), so that alone
   is not graph-specific. Ask of every sketch: which step uses symmetry of the relation and
   binary arity?
3. Nýdl's theorem is a second filter. If the argument would also work from the (αn)-deck for a
   fixed α < 1, it is wrong.
4. The h.d.c. filter. An argument whose separating examples are allowed to have more than n
   vertices is about the wrong closure (S1 Prop 4.6).

## Formalizable candidate steps

Do NOT propose without fidelity review. I did not run `desk.py propose`. Every Prop below
elaborated against `import Mathlib` and `import Recon.Basic` in a throwaway file outside the
repo (`lake env lean`, 5 s). That is not a result. Suggested ids follow §5; `hom` would be a
new program (human opens it), or the steps can sit in `kelly` and `found`.

**A. `kelly_hom_image_count`.** Stratified Kelly lemma for homomorphisms. Easy to medium; this
is the foundation of the angle.
- **English.** If G and H on n vertices are hypomorphic, then for every graph F (any finite
  order) and every j < n, G and H have equally many homomorphisms from F whose image has
  exactly j vertices.
- **Lean.**
  ```lean
  ∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H →
    ∀ m : ℕ, ∀ F : SimpleGraph (Fin m), ∀ j : ℕ, j < n →
      Nat.card {f : F →g G // (Finset.univ.image f).card = j} =
        Nat.card {f : F →g H // (Finset.univ.image f).card = j}
  ```
- **Route.** There is a bijection between Σ v, {f : F →g card G v // image card j} and
  {(f, v) : (F →g G) × Fin n // image card j ∧ v ∉ image}. Count the fibres (n − j each).
  Transport along card isos: post-composition with `Iso`, and image size is preserved because
  the iso is injective. Divide by n − j > 0. The Mathlib pieces are listed in
  `notes/mathlib/hom_counts_and_logic.md`.
- **Corollaries (also elaborate).** A′ is `kelly_labelled_copy_count`:
  `∀ n G H, Hypomorphic G H → ∀ k < n, ∀ F : SimpleGraph (Fin k), G.labelledCopyCount F = H.labelledCopyCount F`.
  A″ is `kelly_hom_count_below_order`: the same with `Nat.card (F →g G) = Nat.card (F →g H)`.

**B. `found_hypomorphic_iff_hom_below_order`.** The precise reduction, Proposition R (a) ⇔ (e).
(⇒) is A″, easy given A. (⇐) is medium to hard: two triangular inversions plus building σ
from equal card multiplicities. It is a natural `reduce` target with children
- (a) ⇔ (b) card multiplicities;
- (c) ⇒ (b);
- (d) ⇒ (c) (inclusion–exclusion on edge supersets);
- (e) ⇒ (d) (partition Möbius).
```lean
∀ n : ℕ, ∀ G H : SimpleGraph (Fin n),
  Recon.Hypomorphic G H ↔
    ∀ k : ℕ, k < n → ∀ F : SimpleGraph (Fin k), Nat.card (F →g G) = Nat.card (F →g H)
```
Variant B′ `found_recon_iff_hom_below_order`: `Recon.ReconstructionConjecture ↔ ∀ n, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), (∀ k < n, ∀ F : SimpleGraph (Fin k), Nat.card (F →g G) = Nat.card (F →g H)) → Nonempty (G ≃g H)`.

**C. `found_lovasz_at_order`.** Lovász for n-vertex targets. Medium if done through injective
counts; the hom version needs the partition Möbius.
```lean
∀ n : ℕ, ∀ G H : SimpleGraph (Fin n),
  (∀ k : ℕ, k ≤ n → ∀ F : SimpleGraph (Fin k), Nat.card (F →g G) = Nat.card (F →g H)) →
    Nonempty (G ≃g H)
```

**D. `found_recon_iff_isolated_vertex`.** S1 Example 3.8 (i) ⇔ (iv), restricted to K = K₁.
Easy to medium, given edge-count and degree recognizability on a general Fintype. It is a
reformulation of RC, not progress on RC.
```lean
Recon.ReconstructionConjecture ↔
  ∀ n : ℕ, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H →
    Recon.Hypomorphic (G ⊕g (⊥ : SimpleGraph Unit)) (H ⊕g (⊥ : SimpleGraph Unit))
```
- **Route (⇐).**
  1. The card of G ⊕g ⊥ at `inr ()` is isomorphic to G.
  2. σ maps `inr ()` to a degree-0 vertex w.
  3. If w = `inr ()`, done. If w = `inl u`, then u is isolated in H, and
     (H ⊕g ⊥) − inl u ≅ H by swapping u with `inr ()`.
- **Route (⇒).** Iso ⇒ hypomorphic. Note: the checked `found_iso_hypomorphic` is for `Fin n`
  only, so a general-type version is needed, via `Iso.induce`.

**E. `found_recon_iff_surj_hom`.** RC ⇔ surjective-hom counts recognizable. Easy to medium,
given edge-count recognizability. This is the cleanest statement of "the gap is the spanning
layer".
```lean
Recon.ReconstructionConjecture ↔
  ∀ n : ℕ, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H →
    ∀ m : ℕ, ∀ F : SimpleGraph (Fin m),
      Nat.card {f : F →g G // Function.Surjective f} =
        Nat.card {f : F →g H // Function.Surjective f}
```
- **Route (⇐).** Take F = G. The identity is surjective, so there is a surjective hom
  f : G →g H. It is bijective on `Fin n`. With equal edge counts, the edge map is a bijection,
  so f is an iso.

**F (hard, real content).** `kelly_closed_walk_count`: hypomorphic ⇒ equal closed-walk counts
of every length, i.e., `Matrix.trace (G.adjMatrix ℤ ^ k)` equal for all k (Tutte 1979,
UNVERIFIED). For k < n it is a corollary of A″. The k = n layer is Tutte's
Hamiltonian-cycle theorem: graph specific, and it survives the digraph filter only through
symmetry. The external repo staged it as a hypothesis.

## Open gaps

1. **Target-restricted closure.** No source found that studies cl_n(F_{≤n−1}) (closure with
   targets restricted to n vertices), or that asks which spanning patterns it contains beyond
   cycles, paths and Kocay's disconnected ones. This is the hom-count formulation of the open
   core.
2. **Hypomorphic ⇒ colour-refinement (1-WL) equivalence?** In hom terms: are hom(T,·) for
   trees T with ≥ n vertices recognizable? This is a consequence of RC, but I found its status
   in no source. Paths are covered via walk counts (UNVERIFIED). General trees need surjective
   counts onto connected n-vertex quotients. A weaker milestone worth a red-team check on small
   graphs is only meaningful above n = 13. Below that, RC is verified (McKay), so small n
   cannot refute it.
3. **WL dimension of n-vertex graphs** versus n − 2. If C^{k} with k ≪ n identified n-vertex
   graphs, the question "hypomorphic ⇒ C^k-equivalent" would be an RC-equivalent target in
   logic language. I could not verify any bound on WL dimension in terms of n alone
   (UNVERIFIED; do not cite).
4. **No "deck comonad" or deck game was found** (search negative, UNVERIFIED). Any such
   construction would be signature generic and so could not prove RC alone.
5. **Graph-specific ingredient.** Every hom/logic tool surveyed is signature generic. The only
   graph-specific inputs located are spectral (Tutte, Godsil–McKay). A hom-count route to RC
   must combine Proposition R with such an input. No paper doing this was found.
6. **Verification debt.**
   - Read in text: Lovász 1967 is used via S1's statement; Dvořák and DGR were read as
     abstract or secondary only.
   - Tutte 1979, Kocay 1981 and Godsil–McKay 1981 are UNVERIFIED and should be checked
     against Bondy (1991) or Lauri–Scapellato before any step cites them.
