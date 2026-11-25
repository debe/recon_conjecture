# Kelly's lemma and invariants recognizable from the deck

Librarian sweep for the `kelly` program, written 2026-11-25. It covers the edge count, the
degree sequence, Kelly's subgraph-counting lemma (labelled, unlabelled, induced and rooted
forms), connectivity, and the complement.

Nothing in this note is a result. Each item is a literature fact, with its source, plus a
formalization estimate. Status words follow CLAUDE.md section 1.

## 0. Sources consulted

These sources were actually read during this sweep:

- **[K57]** P. J. Kelly, "A congruence theorem for trees", *Pacific J. Math.* 7(1) (1957)
  961–968. DOI 10.2140/pjm.1957.7.961. I read the full text from msp.org (PDF
  `pjm-v7-n1-p14-s.pdf`). The displayed equations did not survive text extraction, but the
  prose around them did.
- **[BM08]** J. A. Bondy and U. S. R. Murty, *Graph Theory*, GTM 244, Springer 2008,
  Section 2.7. I read it through R. Gardner's lecture notes on that section (ETSU,
  `faculty.etsu.edu/gardnerr/5340/notes-Bondy-Murty-GT/Bondy-Murty-GT-2-7.pdf`, revised
  3/29/2020). These notes quote the numbering: Conjecture 2.19, Lemma 2.20 (Kelly's
  Lemma), Corollaries 2.21 and 2.22, Lemma 2.24, Theorem 2.27 and Corollary 2.28.
  **Caveat:** this is a secondary source for the book. I did not see the book's own text.
- **[GT23]** D. L. Gonçalves and B. D. Thatte, "A refinement of Kelly's lemma for graph
  reconstruction for counting rooted subgraphs", arXiv:2312.17022 (2023). I read the
  abstract only.
- **[AKV24]** V. Arvind, J. Köbler and O. Verbitsky, "On the Expressibility of the
  Reconstructional Color Refinement", arXiv:2406.09351 (2024). I read the abstract only. It
  states that connectedness is determined by the deck, and even by the colour-refinement
  invariants of the cards.
- **[McK22]** B. D. McKay, "Reconstruction of small graphs and digraphs", arXiv:2102.01942
  (v4, January 2022). Wikipedia gives the venue as *Australas. J. Combin.* 83 (2022)
  448–457, which I did not check against the journal. The paper covers computer
  verification for n ≤ 13.
- **[W]** The Wikipedia article "Reconstruction conjecture". I used it only as a
  bibliography and a list of recognizable properties.

These sources were cited but **not read**. Every statement attributed only to them is
UNVERIFIED in content:

- **[BH77]** J. A. Bondy and R. L. Hemminger, "Graph reconstruction—a survey",
  *J. Graph Theory* 1(3) (1977) 227–268, DOI 10.1002/jgt.3190010306. Only the metadata is
  confirmed.
- **[H74]** F. Harary, "A survey of the reconstruction conjecture", in *Graphs and
  Combinatorics*, LNM 406 (1974) 18–28, DOI 10.1007/BFb0066431. The metadata comes from
  [W].
- **[NW78]** C. St. J. A. Nash-Williams, "The reconstruction problem", in *Selected Topics
  in Graph Theory* (1978) 205–236. The metadata comes from [W].
- **[B91]** J. A. Bondy, "A graph reconstructor's manual", *Surveys in Combinatorics 1991*,
  LMS Lecture Note Ser. 166. **UNVERIFIED**: I did not locate a copy or a DOI.

### A note on the definition of the deck

[BM08] (via Gardner) defines G and H as hypomorphic when they have the same vertex set V
and G − v ≅ H − v for every v ∈ V. [K57] uses the same "labeling" form: "there is a labeling
of the two trees A and B such that c(a_i) ≅ c(b_i)". Both match `Recon.Hypomorphic`, with σ
as the labeling.

So "recognizable" results in [K57] actually give the **stronger, σ-pointwise** form: the
invariant of vertex x in G equals the invariant of vertex σ x in H. The proposed statements
below use the pointwise form wherever the source does.

## 1. Edge count (size)

**Statement (counting identity).** For every finite simple graph G on n vertices,

  Σ_{v ∈ V} |E(G − v)| = (n − 2) · |E(G)|.

**Corollary (size recognizable).** For n ≥ 3, hypomorphic graphs have the same number of
edges.

**Source.** [BM08] Corollary 2.22 ("The size and the degree sequence are reconstructible
parameters"). It is the case F = K₂ of Kelly's lemma, Lemma 2.20. The identity is also the
j = 2 case of the counting in [K57], Lemma 1.

**Proof idea.** An edge uv lies in G − w exactly when w ∉ {u, v}, which happens for n − 2
values of w. Double counting gives the identity. Cards that are isomorphic have equal edge
counts, so (n − 2)|E(G)| = (n − 2)|E(H)|, and n ≥ 3 lets us cancel.

**Small-graph check (this sweep).** The identity holds on all 1249 graphs with
3 ≤ n ≤ 7 (networkx atlas).

**Mathlib support.** Everything needed is in Mathlib:

- `SimpleGraph.card_edgeFinset_induce_compl_singleton`
  (`Combinatorics/SimpleGraph/DeleteEdges.lean:160`):
  `#(G.induce {x}ᶜ).edgeFinset = #(G.deleteIncidenceSet x).edgeFinset`.
- `SimpleGraph.card_edgeFinset_deleteIncidenceSet` (`DeleteEdges.lean:181`):
  `… = #G.edgeFinset - G.degree x`.
- `SimpleGraph.sum_degrees_eq_twice_card_edges`
  (`Combinatorics/SimpleGraph/DegreeSum.lean:101`).
- `SimpleGraph.Iso.card_edgeFinset_eq` (`Combinatorics/SimpleGraph/Finite.lean:647`).

Then Σ_x (m − deg x) = n·m − 2m, and the step needs only nat-subtraction bookkeeping. One
also needs `degree_le_card_edgeFinset` (`Finite.lean:359`). The statement uses
`Set.ncard`, so the proof must bridge `ncard` and `edgeFinset.card` with
`Set.ncard_eq_toFinset_card'` (or a similar lemma) under a classical `DecidableRel`.

**Difficulty: easy** (about 40–80 lines). This is the best first target.

## 2. Degree sequence

**Statement (pointwise; Kelly 1957, Lemma 2).** Suppose σ is a hypomorphism, that is,
G − x ≅ H − σ(x) for all x. If n ≥ 3, then deg_G(x) = deg_H(σ x) for every x. In
particular, the degree sequences, taken as multisets, are equal.

**Source.**
- [K57] Lemma 2 states it verbatim: "The vertices a_i and b_i have the same degree,
  i = 1, 2, …, n". It is "the case j = 2" of Lemma 1. [K57] states its lemmas for trees,
  but this part of the argument uses no tree structure.
- [BM08] Corollary 2.22 also covers it.

**Proof idea.** deg_G(x) = |E(G)| − |E(G − x)|. The first term is the same for G and H by
item 1. The second is the same because G − x ≅ H − σ x.

**Small-graph check.** deg v = |E| − |E(G − v)| holds on all graphs with 3 ≤ n ≤ 7.

**Mathlib support.** The lemmas are the same as in item 1. Degree under the statement's
`ncard` form is `(G.neighborSet x).ncard`, which needs a bridge to `G.degree x`
(`card_neighborSet_eq_degree` and `Set.ncard_eq_toFinset_card'`).

**Difficulty: easy**, once item 1 is checked (about 30–60 lines). The multiset form (count
of vertices of each degree d) follows from the pointwise form by transporting along σ.
That costs about 20 more lines.

## 3. Kelly's lemma (subgraph counting)

**Statement (unlabelled, [BM08] Lemma 2.20).** "For any two graphs F and G such that
v(F) < v(G), the parameter s(F, G) [the number of subgraphs of G isomorphic to F] is a
reconstructible parameter." The quantitative form, which is a standard reading and agrees
with the [K57] computation, is

  s(F, G) = Σ_v s(F, G − v) / (n − v(F)).

**Statement (original, [K57] Lemma 1).** "Every type of proper subgraph which occurs in A or
B occurs the same number of times in both, and a_i and b_i are vertices in the same number
of these subgraphs, i = 1, 2, …, n." In this lemma the order j of the subgraph type
satisfies j < n.

[K57] says "occurs as a subgraph" without saying whether the subgraph is induced or not.
The argument is identical in both readings, so both versions hold. Which reading Kelly
intended is UNVERIFIED.

**Proof idea ([K57]).**
1. Let α be the number of T-subgraphs of A, and α_i the number that contain a_i. Then
   Σ_i α_i = jα, since each copy has j vertices.
2. Because c(a_i) ≅ c(b_i), the copies avoiding a_i and b_i are equal in number:
   α − α_i = β − β_i.
3. Summing over i gives nα − jα = nβ − jβ, so α = β because j < n.
4. It follows that α_i = β_i.

The equivalent averaged form is s(F, G) = Σ_v s(F, G − v)/(n − k). It holds because each
copy avoids exactly n − k vertices.

**Rooted corollary.** [BM08] Corollary 2.21 reads: "the number of subgraphs of G that are
isomorphic to F and include a given vertex v is a reconstructible parameter". This is the
second half of [K57] Lemma 1 (α_i = β_i).

[GT23] shows that the finer count, where the root of a rooted F must coincide with the
deleted vertex, is **not** possible in general. It is possible for rooted subgraphs of
height k when rad(G) > k. This is a warning: do not over-strengthen the rooted statement.

**Variants that all follow from the same double count:**
- **Labelled copies.** The number of injective homomorphisms F → G, Mathlib's `Copy F G`.
- **Unlabelled copies.** Mathlib's `copyCount`, which equals labelled / |Aut F|.
- **Induced labelled copies.** Embeddings `F ↪g G`.

**Warning check (CLAUDE.md section 3).** The double count also works for digraphs,
tournaments and hypergraphs. That is consistent: Kelly's lemma is true there too, and
Stockmeyer's and Kocay's counterexamples defeat the step from counts to isomorphism, not
the counts. The lemma fails for infinite graphs only because the counts can be infinite,
and our setting is `Fin n`.

**Mathlib support.** All in `Combinatorics/SimpleGraph/Copy.lean`:
- `SimpleGraph.Copy` (line 89 onward);
- `labelledCopyCount` (line 506), defined as `Fintype.card (Copy H G)`;
- `copyCount` (line 527), defined as `#{G' : G.Subgraph | Nonempty (H ≃g G'.coe)}`;
- `Copy.induce` (line 159), `Copy.comp`, `Iso.toCopy` and `Copy.toEmbedding`.

**Gaps.**
- There is no counting API for induced copies; Copy.lean says "Induced copies: TODO".
- There is no lemma relating copies in `G.induce s` to copies in G with range ⊆ s.
- There is no iso-invariance lemma for `labelledCopyCount`. It is easy to add: compose with
  `e.toCopy` and `e.symm.toCopy`.

**Difficulty.**
- **Labelled form: medium** (about 150–250 lines). You need:
  - the bijection {f : Copy F G // x ∉ range f} ≃ Copy F (G − x);
  - Σ_x #{f | x ∉ range f} = Σ_f (n − k), using `Finset.sum_comm` and
    `card (range f) = k` from injectivity;
  - transport across the card isomorphisms.
- **Unlabelled `copyCount` form: medium-hard.** Subgraphs of G − x have to be mapped to
  subgraphs of G avoiding x, and `copyCount` is phrased over `G.Subgraph` with `coe`
  isomorphisms. The suggested route is to prove the labelled form first, then use
  labelled = |Aut F| · unlabelled. That identity is also missing from Mathlib, so it is
  about another 100 lines.
- **Induced form (`Nat.card (F ↪g G)`): medium.** The proof is the same as the labelled
  form.

## 4. Connectivity

**Statement.** For n ≥ 3, G is connected iff at least two of its cards are connected.
Hence connectedness is recognizable.

**Source.**
- [W] lists "vertex connectivity and connectedness" as recognizable.
- [AKV24] (abstract) states that connectedness is determined by the deck.
- The "at least two connected cards" form is **UNVERIFIED** from a primary source. I could
  not open [H74], [BH77] or [B91].
- I proved the criterion on paper (below) and checked it on all 1249 graphs with
  3 ≤ n ≤ 7. Recognizability of connectedness is traditionally credited to Harary (1964)
  or Kelly; that attribution is UNVERIFIED.

**Proof idea.**
- (⇒) Take a spanning tree T of G. Since n ≥ 2, T has two distinct leaves u and v. A tree
  minus a leaf is connected, so G − u ⊇ T − u is connected, and likewise G − v.
- (⇐) Let u ≠ v with G − u and G − v connected. Any two vertices other than u are joined
  in G − u. Vertex u is joined to every b ≠ v in G − v. For the pair u, v, pick a third
  vertex w (this needs n ≥ 3): then u–w runs in G − v and w–v runs in G − u.
- Recognizability: connectedness of cards is invariant under isomorphism
  (`Iso.connected_iff`), and σ is injective, so H has two connected cards σu ≠ σv.
- n ≥ 3 is necessary: K₂ is connected and 2K₁ is not, yet they are hypomorphic.
- The bound "two" is sharp: K₁ + K_{n−1} has exactly one connected card.

**Mathlib support.** This is unusually good:
- `Connected.exists_isTree_le` (`Combinatorics/SimpleGraph/Acyclic.lean:463`);
- `IsTree.exists_ne_and_degree_eq_one` (`Acyclic.lean:536`), which gives two distinct
  leaves;
- `Connected.induce_compl_singleton_of_degree_eq_one`
  (`Combinatorics/SimpleGraph/Connectivity/Connected.lean:1040`);
- `Connected.mono` (`Connected.lean:340`);
- `Iso.connected_iff` (`Connected.lean:364`);
- `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`
  (`Acyclic.lean:555`), which gives one such vertex.

The (⇐) direction needs reachability in `G.induce s` lifted to G. Use
`Reachable.map (Embedding.induce s).toHom`.

**Difficulty: easy-medium** (about 80–150 lines).

## 5. Complements

**Statement.** If G and H are hypomorphic, then so are Gᶜ and Hᶜ. Hence G is reconstructible
iff Gᶜ is.

**Source.** This is folklore. I believe [B91] and [BH77] state it, but that is UNVERIFIED.
The proof is immediate: (Gᶜ) − x = (G − x)ᶜ, and an isomorphism of graphs is also an
isomorphism of their complements.

**Mathlib.** I found no `Iso.compl` or `induce_compl` lemma by grep, so this is a small gap.
The proof uses the same `toEquiv` together with `compl_adj`.

**Difficulty: easy** (about 30–50 lines). It is useful for later programs, for example to
pass between regular graphs and their complements, or to reach the sparse case through
complements.

## 6. Further recognizable invariants (pointers only)

The following are listed by [W] and in CLAUDE.md section 3. Their contents were not
verified this sweep, so all of them are UNVERIFIED:

- the characteristic polynomial (Tutte 1979);
- the Tutte polynomial and the chromatic polynomial (Tutte);
- the number of spanning trees;
- planarity;
- perfectness (von Rimscha, *Discrete Math.* 47 (1983) 283–291).

All of these are **hard** in Mathlib. There is no Tutte polynomial and no deletion–
contraction framework at this level, so they are not near-term targets.

The edge-reconstruction analogues appear in [BM08] Lemma 2.24 (the edge version of Kelly's
lemma) and Corollary 2.28. Corollary 2.28 says G is edge-reconstructible if
m > ½·C(n, 2) or 2^(m−1) > n!. These are the Lovász (1972) and Müller (1977) bounds. They
are **confirmed via [BM08] as relayed by Gardner**, but the primary papers were not read.

## 7. Candidate Lean bodies (all elaborate against `Recon.Basic`)

Each body below typechecked with `lake env lean` in a scratch file that imports
`Recon.Basic` and opens `SimpleGraph`. These are suggestions for proposals. None has been
proposed by this sweep, and none has had fidelity review.

```lean
-- kelly_card_edge_sum (pure counting; holds for every n thanks to truncated n - 2)
∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  ∑ x : Fin n, (Recon.card G x).edgeSet.ncard = (n - 2) * G.edgeSet.ncard

-- kelly_edge_count
∀ n : ℕ, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H →
  G.edgeSet.ncard = H.edgeSet.ncard

-- kelly_degree_pointwise  (Kelly 1957, Lemma 2)
∀ n : ℕ, 3 ≤ n → ∀ (G H : SimpleGraph (Fin n)) (σ : Fin n ≃ Fin n),
  (∀ x, Nonempty (Recon.card G x ≃g Recon.card H (σ x))) →
  ∀ x, (G.neighborSet x).ncard = (H.neighborSet (σ x)).ncard

-- kelly_degree_sequence (multiset form)
∀ n : ℕ, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H → ∀ d : ℕ,
  {x : Fin n | (G.neighborSet x).ncard = d}.ncard = {x : Fin n | (H.neighborSet x).ncard = d}.ncard

-- kelly_connected_two_cards (the criterion; no hypomorphism)
∀ n : ℕ, 3 ≤ n → ∀ G : SimpleGraph (Fin n), G.Connected ↔
  ∃ u v : Fin n, u ≠ v ∧ (Recon.card G u).Connected ∧ (Recon.card G v).Connected

-- kelly_connected_recognizable
Recon.Recognizable (fun _ G => G.Connected)

-- kelly_copy_sum (labelled Kelly double count; no hypomorphism)
∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (F : SimpleGraph (Fin k)),
  ∑ x : Fin n, (Recon.card G x).labelledCopyCount F = (n - k) * G.labelledCopyCount F

-- kelly_lemma_labelled
∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H → ∀ k : ℕ, k < n →
  ∀ F : SimpleGraph (Fin k), G.labelledCopyCount F = H.labelledCopyCount F

-- kelly_lemma_unlabelled
∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H → ∀ k : ℕ, k < n →
  ∀ F : SimpleGraph (Fin k), G.copyCount F = H.copyCount F

-- kelly_lemma_induced
∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), Recon.Hypomorphic G H → ∀ k : ℕ, k < n →
  ∀ F : SimpleGraph (Fin k), Nat.card (F ↪g G) = Nat.card (F ↪g H)

-- kelly_lemma_rooted  (Kelly 1957 Lemma 1, second half; BM08 Cor. 2.21)
∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (σ : Fin n ≃ Fin n),
  (∀ x, Nonempty (Recon.card G x ≃g Recon.card H (σ x))) → ∀ k : ℕ, k < n →
  ∀ (F : SimpleGraph (Fin k)) (x : Fin n),
  Nat.card {f : F.Copy G // x ∈ Set.range f} = Nat.card {f : F.Copy H // σ x ∈ Set.range f}

-- found_hypomorphic_compl
∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Recon.Hypomorphic G H → Recon.Hypomorphic Gᶜ Hᶜ
```

Notes for fidelity reviewers:

- `G.labelledCopyCount F` counts copies **of F in G**, following Mathlib's argument order
  (`labelledCopyCount G H` = number of copies of H in G).
- The Kelly-lemma statements do not need `3 ≤ n`. They also hold at n = 2, because k < 2
  forces F to have at most one vertex.
- `kelly_copy_sum` holds for every n and k: when k ≥ n both sides are 0, because no
  injection Fin k → Fin(n − 1) exists.
- `ncard` is used throughout so that no `DecidableRel` or `Fintype` instance appears in a
  statement.

## 8. Suggested order

1. `kelly_card_edge_sum`
2. `kelly_edge_count`
3. `kelly_degree_pointwise`
4. `kelly_connected_two_cards`
5. `kelly_connected_recognizable`
6. `kelly_copy_sum`
7. `kelly_lemma_labelled`
8. `kelly_lemma_rooted`

The unlabelled and induced forms come last. Items 1–5 are covered almost completely by
existing Mathlib lemmas. Item 6 is the single genuinely new counting argument, and items
7–8 reuse it.
