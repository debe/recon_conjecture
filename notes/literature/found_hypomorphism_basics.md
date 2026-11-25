# Foundations of hypomorphism

Topic: Hypomorphic is symmetric and transitive; the order is recognizable; each card has
n − 1 vertices; hypomorphism is invariant under isomorphism on either side. These are small
statements that later Kelly-lemma proofs reuse.

Librarian sweep, 2026-11-25. Program: `found`. Nothing in this file is a result. A result
is only what the gate has checked. "Probe compiled" means that a throwaway file in the
scratchpad elaborated under `lake env lean` with the pinned toolchain. That is a
difficulty estimate, not a submission.

## 0. Sources consulted

| Key | Citation | Verified how |
|---|---|---|
| [BM08] | J. A. Bondy, U. S. R. Murty, *Graph Theory*, GTM 244, Springer 2008, §2.7 "Graph Reconstruction", pp. 66–68. DOI 10.1007/978-1-84628-970-5 | Read through R. Gardner's ETSU lecture notes on §2.7 (faculty.etsu.edu/gardnerr/5340/notes-Bondy-Murty-GT/Bondy-Murty-GT-2-7.pdf, rev. 3/29/2020), which quote the definitions, Lemma 2.20 (Kelly), Cor. 2.21, Cor. 2.22, Lemma 2.26 and Cor. 2.28. The book itself was not read. The book DOI is UNVERIFIED. |
| [BH77] | J. A. Bondy, R. L. Hemminger, "Graph reconstruction — a survey", *J. Graph Theory* 1(3) (1977) 227–268. DOI 10.1002/jgt.3190010306 | Bibliographic data confirmed (scilit). Content not read. |
| [Bon91] | J. A. Bondy, "A graph reconstructor's manual", in *Surveys in Combinatorics 1991* (ed. A. D. Keedwell), LMS Lecture Note Ser. 166, CUP 1991, pp. 221–252 | Bibliographic data confirmed (Cambridge Core and citing papers). Content not read. |
| [Har74] | F. Harary, "A survey of the reconstruction conjecture", in *Graphs and Combinatorics*, LNM 406, Springer 1974, pp. 18–28. DOI 10.1007/BFb0066431 | Bibliographic data confirmed (Utah LNM bib index). Content not read. |
| [NW78] | C. St. J. A. Nash-Williams, "The reconstruction problem", Ch. 8 in *Selected Topics in Graph Theory* (eds. L. W. Beineke, R. J. Wilson), Academic Press 1978, pp. 205–236 | Bibliographic data confirmed (Wikipedia, Crossref reference list). Content not read. |
| [LS16] | J. Lauri, R. Scapellato, *Topics in Graph Automorphisms and Reconstruction*, 2nd ed., CUP 2016, Ch. 8 "The Reconstruction Conjectures", pp. 123–139. DOI 10.1017/CBO9781316669846.010 | Chapter preview read. Deck definition confirmed: "the collection of its vertex-deleted subgraphs G − v for all v ∈ V(G) is called the deck of G". The first edition is LMS Student Texts 54, CUP 2003 (series number UNVERIFIED). |
| [Kel57] | P. J. Kelly, "A congruence theorem for trees", *Pacific J. Math.* 7(1) (1957) 961–968. DOI 10.2140/pjm.1957.7.961 | Confirmed (msp.org). The bijection form of "same deck" appears there as vertices "labeled so that" the vertex-deleted subtrees are pairwise congruent. |
| [Koc88] | W. L. Kocay, "Hypomorphisms, orbits, and reconstruction", *J. Combin. Theory Ser. B* 44 (1988) 187–200 | Confirmed (MathWorld, MaRDI portal). DOI not found: UNVERIFIED. MathWorld cites it for the bijection definition. |
| [McK22] | B. D. McKay, "Reconstruction of small graphs and digraphs", *Australas. J. Combin.* 83(3) (2022) 448–457. arXiv:2102.01942 | Abstract and introduction read (arXiv / ar5iv). Defines "card G − v", "(full) deck = multiset of its cards", "reduced deck = set of cards". Thm 3.1(a): graphs with at most 13 vertices are reconstructible (even from reduced decks, for n ≥ 4). |
| [MW] | E. W. Weisstein, "Hypomorphic Graphs", MathWorld | Read. "G is hypomorphic to H if G and H have the same graph deck", equivalently a bijection φ with G − v ≅ H − φ(v). |
| [Sch] | S. Schlesinger, `reconstruction-conjecture` (Lean 4 / Mathlib 4.28), github.com/SamuelSchlesinger/reconstruction-conjecture | Read `Defs.lean`, `Basic.lean` and `EdgeCount.lean` (main branch, fetched 2026-11-25). This is prior-art Lean, not a literature source. The repository states no license, so **do not copy code**; use it only as evidence of difficulty. |

## 1. Definitions as they appear in the literature, and how `Basic.lean` encodes them

- **Card.** G − v is the graph obtained by deleting v and its incident edges. It is treated
  as unlabelled in [McK22] and as a labelled vertex-deleted subgraph in [BM08].
  `Recon.card G x := G.induce ({x}ᶜ)` is the labelled induced subgraph on `{x}ᶜ`, which
  matches [BM08].
- **Deck.** The multiset of cards up to isomorphism ([McK22], [LS16], Wikipedia).
- **Hypomorphic.** There are three equivalent formulations in the literature:
  1. *Same multiset deck* ([MW], Wikipedia, [McK22] implicitly).
  2. *Bijection form*: there is a bijection φ : V(G) → V(H) with G − v ≅ H − φ(v) for all v.
     This form is in [MW], [Koc88], and in [Kel57] in "labelled" wording.
     **`Recon.Hypomorphic` is exactly this form**, and it allows different vertex types
     `V`, `W`.
  3. *Same-vertex-set form* ([BM08] §2.7): "Graphs G and H on the same vertex set V are
     hypomorphic if, for all v ∈ V, their vertex-deleted subgraphs G − v and H − v are
     isomorphic." It is the bijection form with φ = id, after relabelling H.

  The equivalence of 1 ⇔ 2 is stated in [MW] without proof. Its proof is the obvious one:
  match cards class by class. I could not find an equivalence lemma with a number in
  [BH77] or [Bon91], because their text was not read, so **the attribution of the
  equivalence to a specific source is UNVERIFIED**. Mathematically it is elementary (see
  F8 below).
- **Reconstruction / reconstructible.** [BM08]: "A reconstruction of a graph G is any
  graph hypomorphic to G. Graph G is reconstructible if every reconstruction of G is
  isomorphic to G." This matches `Recon.Reconstructible`.
- **Reconstructible parameter** ([BM08]): it "takes the same value on all reconstructions
  of G". This matches `Recon.Recognizable` restricted to n ≥ 3.
- **n = 2.** [BM08]: 2K₁ and K₂ are hypomorphic but not isomorphic. This matches the
  anchor `anchor_two_vertices_hypomorphic`.

## 2. Results

None of the following carries a theorem number in the sources that were read. They are
"folklore" facts that every survey uses implicitly. Where the attribution is to a survey
whose text was not read, it is marked UNVERIFIED.

### F1. Hypomorphism is symmetric

- **Statement.** If G is hypomorphic to H, then H is hypomorphic to G.
- **Source.** Implicit in [MW], [BM08] and [McK22]: "same deck" is a symmetric relation.
  No numbered statement was found. A numbered statement in [BH77] or [Bon91] is UNVERIFIED.
- **Proof idea.** Use φ⁻¹. For y ∈ V(H), the hypothesis at φ⁻¹(y) gives
  G − φ⁻¹(y) ≅ H − φ(φ⁻¹(y)) = H − y. Invert that isomorphism.
- **Formalization.** Trivial, a few lines. Probe compiled. The only wrinkle is the
  dependent type `card H (σ (σ.symm y))` versus `card H y`. Since the goal is `Nonempty`,
  `rw [σ.apply_symm_apply] at key` works. Prior art [Sch] `SameDeck.symm` does the same.
- **Candidate Lean body:**
  `∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Recon.Hypomorphic G H → Recon.Hypomorphic H G`

### F2. Hypomorphism is transitive

- **Statement.** If G ~ H and H ~ K are hypomorphic, then G ~ K.
- **Source.** Same as F1 (implicit). UNVERIFIED as a numbered statement.
- **Proof idea.** Compose the bijections, σ then τ, and compose the card isomorphisms
  G − x ≅ H − σx ≅ K − τσx.
- **Formalization.** Trivial, a one-liner. Probe compiled:
  `⟨σ.trans τ, fun x => ⟨(hσ x).some.trans (hτ (σ x)).some⟩⟩`.
  Together with the reflexivity anchor this makes Hypomorphic an equivalence relation.
- **Candidate Lean body:**
  `∀ (n : ℕ) (G H K : SimpleGraph (Fin n)), Recon.Hypomorphic G H → Recon.Hypomorphic H K → Recon.Hypomorphic G K`

### F3. The order is recognizable

- **Statement.** n = |V(G)| equals the number of cards, so hypomorphic graphs have the
  same order.
- **Source.** Wikipedia (citing Wall, "The Reconstruction Conjecture", an expository note):
  "The order of a graph G, |V(G)| is recognizable from D(G)." [BM08] has the note "If a
  graph has n vertices then it has n vertex-deleted subgraphs." Its presence in [Har74],
  [BH77] or [Bon91] is UNVERIFIED (texts not read).
- **Proof idea.** Count the cards. In the bijection form it is immediate: σ : V ≃ W gives
  |V| = |W|.
- **Formalization.** Trivial. Probe compiled:
  `rintro n m G H ⟨σ, -⟩; simpa using Fintype.card_congr σ`.
- **Fidelity warning.** With `Recon.Hypomorphic` this fact is *built into the
  definition*, through the bijection σ. That is faithful: a multiset deck of n cards
  forces n. But it means the step carries no information about cards. Reviewers should
  not read it as evidence that the cards are being used.
- **Candidate Lean body** (it must allow two different orders to say anything):
  `∀ (n m : ℕ) (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)), Recon.Hypomorphic G H → n = m`

### F4. Each card has n − 1 vertices

- **Statement.** |V(G − v)| = |V(G)| − 1.
- **Source.** By definition of vertex deletion ([BM08] §2.7, [LS16] Ch. 8). This is used
  in Kelly's lemma, where each copy of F with |V(F)| < n avoids exactly n − |V(F)|
  vertices. The exact denominator wording in [BM08] is not reproduced in the notes read
  (UNVERIFIED).
- **Proof idea.** `{x}ᶜ` in a set of size n has size n − 1.
- **Formalization.** Trivial. Probe compiled:
  `rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]; simp`.
  `Fintype.card_compl_set` is in `Data/Fintype/Card.lean:155`. Use `Nat.card` in the
  statement to avoid instance arguments.
- **Candidate Lean body:**
  `∀ (n : ℕ) (x : Fin n), Nat.card ({x}ᶜ : Set (Fin n)) = n - 1`.
  A variant that names the card: `Nat.card (Fin n) = Nat.card ({x}ᶜ : Set (Fin n)) + 1`
  avoids truncated subtraction when n = 0. Note that `Fin 0` has no x, so it is vacuous
  anyway.

### F5. Hypomorphism is invariant under isomorphism on either side

- **Statement.** If G ≅ G′, H ≅ H′ and G ~ H, then G′ ~ H′.
- **Source.** Implicit: decks are defined up to isomorphism ([McK22], [LS16]), so
  isomorphic graphs have equal decks. The isomorphic ⇒ hypomorphic half is the `found`
  step `found_iso_hypomorphic`, which is checked on main. Combined with F1 and F2, F5
  follows. Numbered source UNVERIFIED.
- **Proof idea.** Use the bijection f⁻¹ ; σ ; g. Card isomorphisms are G′ − y ≅ G − f⁻¹y
  (restricted f⁻¹), then G − f⁻¹y ≅ H − σf⁻¹y, then H − σf⁻¹y ≅ H′ − gσf⁻¹y (restricted g).
- **Formalization.** Easy, under 30 lines. Probe compiled. The clean card restriction is
  Mathlib's `SimpleGraph.Iso.induce`
  (`Combinatorics/SimpleGraph/Maps.lean:869`, needs `Set.BijOn f {x}ᶜ {f x}ᶜ`). It can
  also reuse `Recon.Checked.L_found_iso_hypomorphic` (its helper `cardIso` uses
  `Equiv.subtypeEquiv`) together with F1 and F2.
- **Candidate Lean bodies.** Either one combined statement, or two one-sided ones:
  - combined: `∀ (n : ℕ) (G G' H H' : SimpleGraph (Fin n)), Nonempty (G ≃g G') → Nonempty (H ≃g H') → Recon.Hypomorphic G H → Recon.Hypomorphic G' H'`
  - left: `∀ (n : ℕ) (G G' H : SimpleGraph (Fin n)), Nonempty (G ≃g G') → Recon.Hypomorphic G H → Recon.Hypomorphic G' H`

### F6. Reconstructibility is an isomorphism invariant

- **Statement.** If G ≅ G′ and G is reconstructible, then G′ is reconstructible.
- **Source.** Implicit in [BM08]'s definition: reconstructibility is a property of the
  isomorphism class. Numbered source UNVERIFIED.
- **Proof idea.** Take H with G′ ~ H. By F5, G ~ H, so G ≅ H, so G′ ≅ H.
- **Formalization.** Trivial given F5. Probe compiled. It is needed for every class result
  (`ClassReconstructible`) whose class is closed under relabelling, for example "WLOG the
  isolated vertex is 0".
- **Candidate Lean body:**
  `∀ (n : ℕ) (G G' : SimpleGraph (Fin n)), Nonempty (G ≃g G') → Recon.Reconstructible G → Recon.Reconstructible G'`

### F7. Same-vertex-set form of hypomorphism ([BM08] §2.7 definition)

- **Statement.** G ~ H (bijection form) iff there is H′ ≅ H on the same vertex set with
  G − v ≅ H′ − v for every v.
- **Source.** [BM08] uses the right-hand side as *the* definition. The equivalence with
  the bijection form is not stated there (as far as the notes show), so UNVERIFIED as a
  cited lemma.
- **Proof idea.** (⇒) Take H′ := H.comap σ (Mathlib `Iso.comap σ H : H.comap σ ≃g H`,
  `Maps.lean`, around line 805). Then H′ − v ≅ H − σv by restricting `Iso.comap`.
  (⇐) Compose the isomorphism H′ ≅ H with F5.
- **Formalization.** Easy to moderate, 30–60 lines. The statement elaborated in a probe;
  the proof was not attempted. It is useful as a **fidelity bridge** to the textbook
  definition.
- **Candidate Lean body:**
  `∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Recon.Hypomorphic G H ↔ ∃ H' : SimpleGraph (Fin n), Nonempty (H ≃g H') ∧ ∀ x : Fin n, Nonempty (Recon.card G x ≃g Recon.card H' x)`

### F8. Multiset-deck form of hypomorphism (fidelity bridge to "same deck")

- **Statement.** G ~ H iff for every graph F, the number of vertices x with G − x ≅ F
  equals the number with H − x ≅ F.
- **Source.** [MW] states that the definitions are equivalent. The standard definition is
  "same deck = same multiset of cards up to iso" ([McK22], [LS16], Wikipedia). There is
  no numbered lemma: UNVERIFIED as a cited lemma.
- **Proof idea.** (⇒) σ restricts to a bijection between the two fibres
  `{x // G − x ≅ F}` and `{x // H − x ≅ F}`. Probe compiled:
  `Nat.card_congr (σ.subtypeEquiv ...)`.
  (⇐) Partition the vertices by the isomorphism class of the card. Equal fibre counts
  give a bijection on each class (`Fintype.card` equality gives an `Equiv`). Glue them
  with `Equiv.ofFiberEquiv` or `Equiv.sigmaFiberEquiv`, keyed by a class representative
  on `Fin (n-1)`, chosen classically.
- **Formalization.** (⇒) is trivial. (⇐) is moderate, about 80–150 lines; the gluing is
  the work. This is the most valuable fidelity step in this topic, because it ties
  `Recon.Hypomorphic` to the literature's definition of the deck. F8 (⇒) is also the form
  in which Kelly-lemma proofs consume hypomorphism: counts over cards.
- **Candidate Lean body** (elaborated in a probe):
  `∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Recon.Hypomorphic G H ↔ ∀ (m : ℕ) (F : SimpleGraph (Fin m)), Nat.card {x : Fin n // Nonempty (Recon.card G x ≃g F)} = Nat.card {x : Fin n // Nonempty (Recon.card H x ≃g F)}`

### F9. Card edge count plus degree (first Kelly-type identity; reused by kelly_*)

- **Statement.** |E(G − v)| + deg v = |E(G)|. Summing over v gives
  Σᵥ |E(G − v)| = (n − 2)|E(G)|, so for n ≥ 3 the size and the degree sequence are
  recognizable.
- **Source.** [BM08] Cor. 2.22: "The size and the degree sequence are reconstructible
  parameters" (read in the Gardner notes). [BM08] derives it from Lemma 2.20, Kelly's
  lemma: "For any two graphs F and G such that v(F) < v(G), the parameter (G choose F)
  is a reconstructible parameter." Kelly's lemma is due to [Kel57]. The identity
  |E| = Σ|E(G−v)|/(n−2) as an explicit formula: UNVERIFIED wording (standard).
- **Proof idea.** The edges of G not in G − v are exactly the edges at v, and there are
  deg v of them. Each edge avoids exactly n − 2 vertices, so it lies in n − 2 cards
  (double counting).
- **Formalization.** Moderate, about 100–150 lines. Prior art [Sch] `EdgeCount.lean` does
  it in about 150 lines with `edgeFinset` and `incidenceFinset`. Useful Mathlib pieces:
  - `sum_degrees_eq_twice_card_edges` (`Combinatorics/SimpleGraph/DegreeSum.lean:101`);
  - `Iso.card_edgeFinset_eq` (`Finite.lean:647`);
  - `Iso.mapEdgeSet` (`Maps.lean:774`);
  - `induce_deleteIncidenceSet_of_notMem` (`DeleteEdges.lean:146`).

  Use `Nat.card G.edgeSet` in statements to dodge `DecidableRel` and `Fintype` instances
  on `card G x`. The matched-cards version (hypomorphic ⇒ ∃σ with equal card edge counts)
  is trivial: `Nat.card_congr (hσ x).some.mapEdgeSet`, probe compiled. Strictly this
  belongs to program `kelly` or is `found`'s "edge count recognizable" target.
- **Candidate Lean bodies** (elaborated in a probe):
  - `∀ (n : ℕ) (G : SimpleGraph (Fin n)) (x : Fin n), Nat.card (Recon.card G x).edgeSet + Nat.card (G.neighborSet x) = Nat.card G.edgeSet`
  - `∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∑ x : Fin n, Nat.card (Recon.card G x).edgeSet = (n - 2) * Nat.card G.edgeSet`
  - `Recon.Recognizable (fun n G => Nat.card G.edgeSet = k)` per k, or directly
    `∀ n, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H → Nat.card G.edgeSet = Nat.card H.edgeSet`

## 3. Side confirmations (outside this topic, but asked for in CLAUDE.md)

- **Edge reconstruction, Lovász / Müller bounds.** [BM08] Cor. 2.28, read in the Gardner
  notes: "A graph G of size m and order n is edge reconstructible if either
  m > ½·C(n,2) or 2^(m−1) > n!." This confirms the forms m > n(n−1)/4 (Lovász 1972) and
  2^(m−1) > n! (Müller 1977) as *statements in a textbook*. The attribution to Lovász and
  Müller, and the original venues, are still UNVERIFIED here. [BM08] derives both from
  Nash-Williams' lemma (Lemma 2.26) with F = ∅.
- **Small n.** [McK22] Thm 3.1(a): graphs with at most 13 vertices are reconstructible
  (from reduced decks, for n ≥ 4). This agrees with CLAUDE.md.
- The Gardner notes state that "McKay 1977 verified ≤ 10 vertices (J. Graph Theory
  vol. 1)". This is an older bound and is superseded.

## 4. What breaks in the warning settings?

All of F1–F8 are pure "bookkeeping" and hold verbatim for digraphs, tournaments,
hypergraphs and (except counting) infinite graphs. So they cannot be the place where a
false proof of the conjecture hides. F9 uses |V| finite and the edge-incidence structure.
Its analogues for k-uniform hypergraphs (each edge avoids n − k vertices) also hold. Librarian remark, not from a source (UNVERIFIED): this
is consistent with Kocay's counterexamples being about the converse step, not about
counting.

## 5. Summary ranking, most formalizable first

| # | Statement | Difficulty | Reuse |
|---|---|---|---|
| F2 | Hypomorphic transitive | trivial (probe compiled) | everything |
| F1 | Hypomorphic symmetric | trivial (probe compiled) | everything |
| F3 | order recognizable (n = m) | trivial (probe compiled), definitional | fidelity |
| F4 | card has n − 1 vertices | trivial (probe compiled) | Kelly denominators |
| F5 | iso-invariance on both sides | easy (probe compiled) | class results |
| F6 | Reconstructible iso-invariant | trivial given F5 (probe compiled) | every `ClassReconstructible` |
| F8 (⇒) | hypomorphic ⇒ equal card-class counts | trivial (probe compiled) | Kelly lemma input |
| F7 | Bondy–Murty same-vertex-set form | easy–moderate | fidelity |
| F9 | card edges + degree, Σ = (n − 2)·m | moderate (~150 lines, prior art) | size, degree sequence |
| F8 (⇔) | bijection form ⇔ multiset-deck form | moderate (~100–150 lines) | fidelity of `Basic.lean` |
