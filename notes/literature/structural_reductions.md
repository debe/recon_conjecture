# Structural reductions, the ℓ-deck program and the 2015–2026 arXiv frontier

Librarian sweep, 2026-11-25. Angle: structural graph theory and reductions. Working
hypothesis given by the caller: the conjecture is true, and we want proof routes. Nothing in
this file is a result. Statuses use the CLAUDE.md vocabulary, and literature claims carry
their source. **UNVERIFIED** means I did not read the claim in the primary text. Where I
read only an abstract or a secondary citation, the entry says so.

## Summary

1. The strongest published reduction I found is the 2-connected graphs G with
   diam(G) = 2 or diam(G) = diam(Ḡ) = 3 (Ramachandran–Monikandan 2009, combining Yang 1988
   and Gupta–Mangal–Paliwal 2003). A 2026 preprint gives a domination variant
   (Aravind–Monikandan, arXiv:2601.00620), and a 2014 paper excludes geodetic and
   interval-regular blocks (Monikandan–Balakumar). I read all three only through abstracts
   or secondary citations.
2. Only the complement-plus-diameter half of these reductions is elementary, and that half
   is very formalizable. It rests on three lemmas: (a) G is reconstructible iff Ḡ is;
   (b) disconnected graphs are reconstructible (Kelly); (c) if u and v are at distance ≥ 3
   in G, then {u, v} is a dominating edge of Ḡ. Yang's 2-connectivity half is deep, and I
   could not find its proof idea.
3. No credible full proof exists. One proof claim is withdrawn (Raju Renjit,
   arXiv:cs/0702119). Another is an unrefereed math.GM claim (Mehendale,
   arXiv:math/0503316). Hosaka (arXiv:2003.06759) and Dufresne et al. (arXiv:2604.16567)
   claim no proof. McKay's computation covers n ≤ 13 (arXiv:2102.01942).
4. The ℓ-deck program gives one firm limit. Nýdl showed that M_ℓ/ℓ → ∞, and that no fixed
   fraction q < 1 of the vertices suffices. Any argument that would reconstruct from the
   ⌊qn⌋-deck is wrong. Kostochka–West also show that ℓ-reconstruction of G + (ℓ−1)K₁
   implies the classical conjecture.
5. Some attackable open subclasses remain:
   - triangle-free graphs of diameter 2 with connectivity ≥ 4 (open after Clifton et al.
     2022);
   - bipartite graphs in general;
   - planar graphs;
   - graphs whose deck has exactly two card types (a 2026 preprint claims this; UNVERIFIED).

   For this fleet, the best first moves are the cheap reductions plus "isolated or
   universal vertex".

## Sources

Each entry gives the citation, what it proves, how it was verified, behaviour in the
failing settings, and Lean difficulty. The failing settings are tournaments and digraphs
(Stockmeyer), k-uniform hypergraphs with k ≥ 3 (Kocay) and infinite graphs (Fisher;
Bowler et al.).

### S1. Yang Yongzhi (1988): reduction to 2-connected graphs
- Y. Yongzhi, *The reconstruction conjecture is true if all 2-connected graphs are
  reconstructible*, J. Graph Theory 12(2) (1988) 237–243, DOI 10.1002/jgt.3190120214.
- **Statement:** if every 2-connected graph is reconstructible, then every graph on ≥ 3
  vertices is. Aravind–Monikandan state the connected-graph form: every connected graph is
  reconstructible iff every 2-connected graph is.
- **Verified:** the statement only, from the abstract (via zendy.io) and three citing papers
  (AJC 80 (2021) 167–177, read in full; arXiv:2601.00620; DMGT 34 (2014)). **Proof idea
  UNVERIFIED**: I found no text describing it.
- **Why the proof is not just a complement trick:** P₄ is self-complementary and separable.
  So the reduction must reconstruct separable graphs from their 2-connected pieces.
  - It plausibly builds on Bondy 1969 (separable graphs without end vertices) and on the
    Greenwell–Hemminger branch-counting technique. This is my inference.
  - A related paper is A. Vince & Y. Yang, *Reconstruction of the set of branches of a
    graph*, Graphs Combin. 12 (1996) 69–80. I read its full text. It proves that the set of
    rooted branches of G is reconstructible except in one case: G has exactly two
    branches, the pruned centre is a vertex or an edge, one branch holds every degree-1
    vertex, and the other holds exactly one end-block. In that case reconstructing the
    branches is equivalent to reconstructing G.
- **Failing settings:** UNVERIFIED for digraphs. The statement is vacuous for infinite
  graphs, where the conjecture is false anyway. I know of no hypergraph analogue.
- **Lean:** very hard. Mathlib has no vertex connectivity, cut vertices, blocks or
  block-cut tree. 2-connectivity can be phrased with the repo's definitions as
  `∀ x, (Recon.card G x).Connected`, which is equivalent to 2-connected for n ≥ 3. The
  proof itself is the obstacle.

### S2. Bondy (1969): separable graphs without end vertices
- J. A. Bondy, *On Ulam's conjecture for separable graphs*, Pacific J. Math. 31(2) (1969)
  281–288 (msp.org/pjm/1969/31-2/p02).
- **Statement (from the MSP abstract):** connected separable graphs with no pendant
  (degree-1) vertices are reconstructible. The paper also has partial results with pendant
  vertices.
- **Verified:** abstract only. Proof idea UNVERIFIED in detail. My understanding is that it
  counts end-blocks via Kelly-type counting and the block-cut tree.
- **Lean:** very hard. It needs blocks and cut vertices, which Mathlib lacks.

### S3. Gupta, Mangal, Paliwal (2003): reduction by diameter
- S. K. Gupta, P. Mangal, V. Paliwal, *Some work towards the proof of the reconstruction
  conjecture*, Discrete Math. 272 (2003) 291–296, DOI 10.1016/S0012-365X(03)00198-5,
  zbMATH 1028.05070.
- **Statement:** RC holds iff every connected G with diam(G) = 2, or with
  diam(G) = diam(Ḡ) = 3, is reconstructible. They also show both classes are recognizable
  (Theorem 2.2 of AJC 80), and they introduce the vertex-pair parameters pv(G, i) and
  pav(G, i).
- **Verified:** secondary only. The wording comes from AJC 80 (2021), read in full, and from
  arXiv:2601.00620 and arXiv:2210.00338. One search snippet says "diam(Ḡ) = 2", which
  conflicts with the others. Every source I could read says 3.
- **Proof idea:** this is my reconstruction, but each step is elementary and I checked the
  key lemma on all graphs with n ≤ 7, plus 2000 random graphs with n ∈ {8, 9, 10}.
  - G is reconstructible iff Ḡ is (S12).
  - Disconnected graphs are reconstructible, so assume G and Ḡ are both connected.
  - Standard fact: diam(G) ≥ 3 implies diam(Ḡ) ≤ 3, and diam(G) ≥ 4 implies diam(Ḡ) ≤ 2.
  - So either one of G and Ḡ has diameter ≤ 2, or both have diameter 3.
- **Failing settings:** the complement lemma also holds for digraphs (take the complement
  relation) and for k-uniform hypergraphs (complement in the complete k-graph). This
  reduction only shrinks the class, so it cannot transfer a false conclusion. Fine.
- **Lean:** the diameter half is easy to medium. Mathlib has `edist`, `ediam` and
  `two_lt_edist_iff` (see the Mathlib map below). Recognizability is not needed for the
  reduction, because `ClassReconstructible` quantifies over all H.

### S4. Ramachandran & Monikandan (2009): combined reduction
- S. Ramachandran, S. Monikandan, *Graph reconstruction conjecture: reductions using
  complement, connectivity and distance*, Bull. Inst. Combin. Appl. 56 (2009) 103–108.
  Citation read in the AJC 80 reference list.
- **Statement:** RC holds iff every 2-connected G with diam(G) = 2 or
  diam(G) = diam(Ḡ) = 3 is reconstructible. Later papers call this class the "DR-class".
- **Verified:** secondary only (AJC 80 introduction, read in full; arXiv:2601.00620). Proof
  UNVERIFIED. Combining "2-connected" with "complement" is not automatic, because the
  complement of a 2-connected graph need not be 2-connected. Treat it as a black box.
- **Lean:** very hard, since it inherits Yang.

### S5. Monikandan & Balakumar (2014): blocks that are neither geodetic nor interval-regular
- S. Monikandan, J. Balakumar, *A reduction of the graph reconstruction conjecture*,
  Discuss. Math. Graph Theory 34(3) (2014) 529–537, DOI 10.7151/dmgt.1746.
- **Statement:** RC holds iff every non-geodetic, non-interval-regular block G with
  diam(G) = 2 or diam(G) = diam(Ḡ) = 3 is reconstructible. Interval-regular graphs are
  reconstructible.
- **Verified:** abstract via eudml/DOAJ search snippets. The full text was blocked (HTTP 403
  and a TLS error). Proof idea UNVERIFIED.
- **Related:** Monikandan & Balakumar, *Reconstruction of bipartite graphs and triangle-free
  graphs with connectivity two*, Australas. J. Combin. 53 (2012) 141–150. Citation from
  the AJC 80 reference list; content UNVERIFIED.

### S6. Aravind & Monikandan (2026): domination reduction
- J. Antony Aravind, S. Monikandan, *A reduction of the reconstruction conjecture using
  domination and vertex pair parameters*, arXiv:2601.00620 (2 Jan 2026). Preprint, not
  refereed as far as I know.
- **Statement (Theorem 7):** RC holds iff every 2-connected G with γ(G) = 2, or with
  diam(G) = diam(Ḡ) = 2, is reconstructible. Theorem 5 is the connected version.
- **Key lemma (Lemma 4):** if G is connected and diam(G) ≥ 3, then γ(Ḡ) = 2. The proof:
  - take u, v at distance ≥ 3;
  - then uv ∈ E(Ḡ), and every other vertex is a Ḡ-neighbour of u or v;
  - and Ḡ has no universal vertex.
- **Verified:** read in the arXiv HTML, Theorems 2–7 and Lemma 4.
- **Caveat:** Theorem 7's proof does not explain how 2-connectivity survives passing to the
  complement. It just cites Yang. Treat the "2-connected" part of Theorem 7 as unjustified
  in this preprint.
- **Strengthening (my observation):** the connected-graph version (Theorem 5) holds with
  γ(G) = 2 replaced by the narrower "G has a dominating *edge*", because Lemma 4 produces
  an adjacent dominating pair. This is candidate C4 below.
- **Lean:** easy to medium for the connected version. It needs no domination number, only
  an explicit ∃-statement.

### S7. Devi Priya & Monikandan: classes inside the DR-class
- P. Devi Priya, S. Monikandan:
  - *Reconstruction of distance hereditary 2-connected graphs*, Discrete Math. 341 (2018)
    2326–2331;
  - *Reconstruction of 2-connected parity graphs*, Australas. J. Combin. 80(2) (2021)
    167–177.
- **Statement (AJC 80, read in full):** 2-connected graphs in the DR-class are
  reconstructible if they are domino-free parity graphs, or triangle-free with girth 5.
  Theorem 3.1 covers 2-connected parity graphs of diameter 2. Parity graphs are recognizable
  (Lemma 2.4, via Kelly's lemma on odd holes and Burlet–Uhry).
- **Lean:** hard. It uses Tutte's theorem on counting non-separable spanning subgraphs.

### S8. Clifton, Liu, Mahmoud, Shantanam (2022): triangle-free graphs
- A. Clifton, X. Liu, R. Mahmoud, A. Shantanam, *Reconstruction and edge reconstruction of
  triangle-free graphs*, arXiv:2210.00338 (Oct 2022). No journal reference on arXiv.
- **Statement (abstract):** RC holds for triangle-free graphs with
  diam(G) = diam(Ḡ) = 3, and for triangle-free graphs of diameter 2 with connectivity 3.
  Analogous edge-reconstruction results are included. This answers in part a question of
  Balakumar–Monikandan, who had covered connectivity 2.
- **Open by implication:** triangle-free graphs of diameter 2 with connectivity ≥ 4.
- **Verified:** abstract only.

### S9. Kostochka & West (2020): survey of the ℓ-deck program
- A. V. Kostochka, D. B. West, *On reconstruction of graphs from the multiset of subgraphs
  obtained by deleting ℓ vertices*, arXiv:2004.05527 (Apr 2020). I read the full text
  (pp. 1–10).
- **Kelly's conjecture (Conj. 1.4):** for every ℓ there is M_ℓ such that every graph on
  ≥ M_ℓ vertices is ℓ-reconstructible. The classical conjecture is M₁ = 3.
- **Observation 1.3:** the k-deck determines the (k−1)-deck, because each (k−1)-card
  appears in n − k + 1 k-cards.
- **Nýdl's lower bound:** M_ℓ/ℓ → ∞. For every q < 1 there are non-isomorphic n-vertex
  graphs with the same ⌊qn⌋-deck. McMullen–Radziszowski asked whether M₂ = 6.
- **Degree list:**
  - 2-reconstructible for n ≥ 6 (Chernyak);
  - 3-reconstructible for n ≥ 7 (Kostochka–Nahvi–West–Zirlin, arXiv:1904.11901);
  - determined by D_{Δ+2} (Manvel; Lemma 2.3 gives the counting identity);
  - ℓ-reconstructible for n ≥ g(ℓ) ≈ eℓ (Taylor).
- **Connectedness:**
  - 2-reconstructible for n ≥ 6 (Manvel);
  - 3-reconstructible for n ≥ 7 (KNWZ);
  - ℓ-reconstructible for n > 2(ℓ+1)^2 (Spinoza–West). The exponent is garbled in the
    extracted PDF text; this is the reading I believe is right.
  - Conjecture 3.3 asks whether n ≥ 2ℓ + 2 suffices.
- **Classical connectedness argument (p. 7):** a connected graph on n ≥ 3 vertices has at
  least two connected cards, and a disconnected one has at most one.
- **Trees:** Kelly showed trees are 1-reconstructible, and Giles showed trees with ≥ 5
  vertices are 2-reconstructible. Nýdl: S_{k−1,k−1,1} and S_{k,k−2,1} have the same
  k-deck, so M_ℓ(T) ≥ 2ℓ + 1.
- **Proposition 6.1 (a reverse reduction):** if every graph made of a connected graph plus
  ℓ − 1 isolated vertices, with ≥ ℓ + 2 vertices, is ℓ-reconstructible, then RC holds. The
  proof: Kelly handles the disconnected case; for connected G, the (n−ℓ)-deck of
  G + (ℓ−1)K₁ is computable from D_{n−1}(G).
- **Section 6:** graphs whose components all have ≤ n − ℓ vertices are ℓ-recognizable and
  ℓ-reconstructible. This generalises Greenwell–Hemminger counting.
- **Section 7:** r-regular graphs with connectivity 1 are (r+1)-reconstructible.
- **Failing settings:** the counting (Observation 1.3, Lemma 2.3) is finite and fails for
  infinite graphs. It is generic for digraphs and hypergraphs, so it is safe but carries no
  graph-specific force.

### S10. Groenland, Johnston, Scott, Tan: reconstruction from smaller cards
- C. Groenland, T. Johnston, A. Scott, J. Tan, *Reconstruction from smaller cards*,
  arXiv:2103.13359; Israel J. Math. (2025), DOI 10.1007/s11856-025-2858-3. DOI from the TU
  Delft repository listing.
- **Verified, read in ar5iv:**
  - Theorem 4: any n-vertex tree is reconstructible from D_{n−r} when
    r < n/9 − (4/9)√(8n+5) − 1.
  - Theorem 5: connectedness is recognizable from D_ℓ when ℓ ≥ 9n/10.
  - Theorem 7: the degree sequence is reconstructible from D_ℓ when
    ℓ ≥ √(2n log(2n)).
- **Related:**
  - Groenland, Johnston, Kupavskii, Meeks, Scott, Tan, *Reconstructing the degree sequence
    of a sparse graph from a partial deck*, arXiv:2102.08679; JCTB (2022), venue per search
    result. The degree sequence survives O(n/d³) missing cards.
  - Kostochka, Nahvi, West, Zirlin, *Trees with at least 6ℓ+11 vertices are
    ℓ-reconstructible*, arXiv:2307.10035 (abstract verified).
  - Kostochka, Qu, Ritter, West, *Caterpillars with n vertices are reconstructible from
    subgraphs with at most n/2+1 vertices*, arXiv:2511.23309 (Nov 2025; abstract
    verified). Caterpillars with ≥ 48 vertices are determined by their m-deck for
    m > n/2, which is sharp.
  - Kostochka, Nahvi, West, Zirlin, *3-regular graphs are 2-reconstructible*,
    arXiv:1908.01258 (abstract verified).

### S11. Spinoza & West (2019): k-deck reconstruction
- H. Spinoza, D. B. West, *Reconstruction from the deck of k-vertex induced subgraphs*,
  J. Graph Theory (2019), DOI 10.1002/jgt.22409. Statements as quoted in S9:
  - Theorem 4.2: max-degree-2 graphs meeting component-size conditions share k-decks.
  - Theorem 4.5: exact k-deck reconstructibility of graphs with Δ ≤ 2.
  - P_{2ℓ} and C_{ℓ+1} + P_{ℓ−1} have the same ℓ-deck.
- I did not read the primary text, so UNVERIFIED beyond the S9 quotations.

### S12. Complement lemma (folklore)
- **Statement:** G is reconstructible iff Ḡ is. Stated as "well-known" in
  arXiv:2601.00620 (Theorem 2) and used throughout S3–S7.
- **Proof:** (Ḡ) − v = (G − v)‾, and G ≅ H iff Ḡ ≅ H̄. So Hyp(G, H) ⇔ Hyp(Ḡ, H̄), and
  complement is an involution.
- **Failing settings:** true verbatim for digraphs, tournaments (where the complement is
  the reversal) and hypergraphs. It is pure bookkeeping.
- **Lean:** easy. See C1–C2.

### S13. Reconstruction numbers and degree-associated reconstruction
- Facts from the S9 survey, pp. 1–2:
  - Harary–Plantholt defined the reconstruction number rn(G).
  - Myrvold: trees with ≥ 5 vertices have rn = 3.
  - Bollobás: almost every graph has rn = 3.
  - No graph has rn = 2.
  - Myrvold, and Bowler et al.: any ⌊n/2⌋ + 2 cards determine connectedness.
  - Myrvold: any n − 1 cards determine m and the degree list for n ≥ 7.
  - Brown–Fenner: any n − 2 cards determine m for n ≥ 29.
  - Groenland–Guggiari–Scott: any n − √n/20 cards determine m for large n.
- B. Bollobás, *Almost every graph has reconstruction number three*, J. Graph Theory 14
  (1990) 1–4. Pages UNVERIFIED.
- M. D. Barrus, D. B. West, *Degree-associated reconstruction number of graphs*, Discrete
  Math. (2010), DOI 10.1016/j.disc.2010.03.037. DOI from search; content UNVERIFIED. A
  dacard is a card paired with the degree of the deleted vertex.
- Ramachandran introduced degree-associated cards. Citation UNVERIFIED.
- For this fleet, these give no reduction of RC. They are refinements, and they are
  irrelevant to the root.

### S14. Recognizability of planarity
- M. Bilinski, Y. S. Kwon, X. Yu, *On the reconstruction of planar graphs* (preprint dated
  6 Sep 2006). I read the full text intro; published in JCTB 97 (2007), UNVERIFIED.
- **Statement:** Theorem 1.1, the class of planar graphs is recognizable. This answers
  Bondy–Hemminger (1979).
- **Earlier results cited in the intro:**
  - Fiorini: planar graphs with δ ≥ 5 are recognizable.
  - Fiorini–Manvel: the same for δ ≥ 4.
  - Lauri: maximal planar graphs are reconstructible.
- Reconstructing all planar graphs is open. Their intro and the Yu-group papers say so.

### S15. Claimed proofs and community response
- **Raju Renjit G**, *Ulam's conjecture is true for connected graphs*, arXiv:cs/0702119.
  Eight versions (2007–2009), then v9 (25 Aug 2009) was **withdrawn** by the author.
  Verified on arXiv.
- **D. P. Mehendale**, *The reconstruction of graphs*, arXiv:math/0503316 (v1 2005, v2
  2011, math.GM). It claims a proof via spanning trees and pendant-deleted decks. There is
  no journal reference and I found no acceptance. Not credible.
- **T. Hosaka**, *The reconstruction conjecture for finite simple graphs and associated
  directed graphs*, arXiv:2003.06759 (v2 2021). It studies an associated digraph built from
  a hypomorphism. It claims **no** proof. Verified from the abstract.
- **E. Dufresne, G. Jeronimo, J. Kenkel, H. Lindo, N. Villamizar**, *Shuffling the deck:
  invariant theory and the graph reconstruction conjecture*, arXiv:2604.16567 (Apr 2026).
  An expository invariant-theory programme. It claims no proof.
- **M. Zinchenko**, *Two types of cards in Kelly–Ulam conjecture*, arXiv:2611.13728
  (10 Nov 2026). It claims that graphs whose deck has exactly two isomorphism types of card
  are reconstructible. Brand new and unrefereed: **UNVERIFIED**. Note that a single card
  type forces regularity (see C6).
- **McKay**, *Reconstruction of small graphs and digraphs*, arXiv:2102.01942 (v4 Jan 2022).
  Verified from the abstract:
  - graphs with ≤ 13 vertices are reconstructible;
  - tournaments are investigated up to 13 vertices, and digraphs up to 9;
  - the results also cover set reconstruction.

### S16. Failing settings (citations)
- P. K. Stockmeyer, *The falsity of the reconstruction conjecture for tournaments*,
  J. Graph Theory 1 (1977) 19–25. Citation read in the AJC 80 reference list.
- W. L. Kocay, *A family of nonreconstructible hypergraphs*, J. Combin. Theory Ser. B 42
  (1987). Pages UNVERIFIED.
- J. Fisher, *A counterexample to the countable version of a conjecture of Ulam*,
  J. Combin. Theory 7 (1969). UNVERIFIED.
- N. Bowler, J. Erde, P. Heinig, F. Lehner, M. Pitz:
  - *A counterexample to the reconstruction conjecture for locally finite trees*,
    arXiv:1606.02926 (2016);
  - *Non-reconstructible locally finite graphs*, arXiv:1611.04370 (v3 Jan 2018). This one
    has bounded-degree non-reconstructible graphs with one end and with countably many
    ends, answering Nash-Williams.

  Both existences were verified on arXiv. Journal venues UNVERIFIED.

## Reductions

"Holds iff ... reconstructible" means: if every graph in the target class is reconstructible,
then RC holds. The converse is trivial.

| From | To (it suffices to reconstruct) | Source | Status in literature | Status here |
|---|---|---|---|---|
| all graphs, n ≥ 3 | connected G with Ḡ connected | folklore: complement + Kelly (disconnected) | standard | candidates C2 + C5'; Kelly's disconnected case belongs to the `discon` program |
| all graphs | 2-connected graphs | Yang 1988 (S1) | published, JGT | proof idea UNVERIFIED; very hard in Lean |
| all graphs | connected G with diam G = 2, or diam G = diam Ḡ = 3 | Gupta–Mangal–Paliwal 2003 (S3) | published, Discrete Math | elementary given the complement lemma and Kelly; candidate C4' |
| all graphs | connected G and Ḡ, with G having a dominating edge or diam G, diam Ḡ ≤ 2 | strengthening of Aravind–Monikandan Thm 5 (S6) | preprint 2026, with γ = 2 in place of "dominating edge" | candidate C4; I checked the key lemma C3 on n ≤ 7 |
| all graphs | 2-connected G in the DR-class | Ramachandran–Monikandan 2009 (S4) | published, BICA | UNVERIFIED proof |
| all graphs | non-geodetic, non-interval-regular blocks in the DR-class | Monikandan–Balakumar 2014 (S5) | published, DMGT | UNVERIFIED proof |
| all graphs | 2-connected G with γ(G) = 2 or diam G = diam Ḡ = 2 | Aravind–Monikandan 2026 Thm 7 (S6) | preprint; the 2-connectivity step is not justified in the text | treat as UNVERIFIED |
| RC (ℓ = 1) | ℓ-reconstruction of (connected) + (ℓ−1)K₁ | Kostochka–West 2020 Prop. 6.1 (S9) | survey, verified | reverse direction only; not useful as a target |

**Strongest known reduction (smallest target class).** Monikandan–Balakumar 2014 targets
non-geodetic, non-interval-regular blocks with diam G = 2 or diam G = diam Ḡ = 3. A
"block" here means 2-connected. Its proof is UNVERIFIED.

**Strongest reduction we could plausibly get checked.** C4: connected G with Ḡ connected,
and either a dominating edge in G or both diameters ≤ 2. It needs only complement, Kelly's
disconnected case and a 5-line distance lemma.

I found no reduction to 3-connected graphs. Searches turned up nothing, so whether one is
known is UNVERIFIED either way. It is a natural open question, because Yang's technique is
specific to cut vertices.

## Open attackable subclasses

Ranked by how attackable they look for this fleet: Lean-friendly first, open-in-literature
second.

1. **Graphs with an isolated or a universal vertex.** Known, as a special case of
   disconnected graphs and of complements, but not yet in our library. It is a clean
   counting proof:
   - the degree sequence is recognizable;
   - deg_H(σv) = deg_G(v) ∈ {0, n−1};
   - extend the card isomorphism G − v ≅ H − σv by v ↦ σv.

   This is a tracer bullet for `discon`.
2. **Graphs with a single card type.** All cards are isomorphic, so all degrees are equal
   (deg v = m − |E(G−v)|), so G is regular and falls under the `regular` program. Easy, and
   it also anchors Zinchenko's two-type claim.
3. **Graphs with exactly two card types.** Zinchenko 2026 claims this class; UNVERIFIED.
   Worth a thinker reading. If the argument is degree-counting, it may be formalizable on
   top of `kelly_*`.
4. **Triangle-free graphs of diameter 2 with connectivity ≥ 4.** Open after S8. Hard, and
   Lean-hostile because of connectivity.
5. **Bipartite graphs.** Open in general. Covered with connectivity 2 (Monikandan–Balakumar
   2012); parity graphs inside the DR-class cover some 2-connected cases (S7). Bipartiteness
   is recognizable: Manvel says the 2-deck suffices for n ≥ 6. Hard.
6. **Planar graphs.** Open. Recognizable (S14), and maximal planar graphs are done (Lauri).
   Lean-hostile: Mathlib has no planarity.
7. **Graphs G with diam G = diam Ḡ = 3 that are triangle-free.** Done in S8, so not open.

## What breaks in failing settings

- **Complement lemma, the diameter/domination lemma and the C4 reduction.** These hold
  verbatim for digraphs, tournaments and k-uniform hypergraphs (with the appropriate
  complement and distance), and for infinite graphs. That is fine: they are *reductions*,
  and they shrink the target without proving anything. A route made only of such steps
  cannot be wrong, but it cannot finish either.
- **Kelly's disconnected-graph theorem.** It uses finite counting of components (Kelly's
  lemma divides by n − |V(H)|), so it fails for infinite graphs. That matches Fisher and
  Bowler et al., where infinite counterexamples exist.
  - Digraph analogue: UNVERIFIED. I believe disconnected digraphs are reconstructible by
    the same counting, but have no source.
  - Stockmeyer's tournaments are strongly connected-ish objects, so a disconnected-case
    argument does not touch them.
- **Yang / Bondy.** They rely on block structure of undirected graphs (cut vertices, the
  block-cut tree). There is no direct tournament analogue, since tournaments have no cut
  vertices in this sense. That this fails for hypergraphs is UNVERIFIED.
- **ℓ-deck arguments.** Nýdl's examples show that any "local" argument which uses only
  induced subgraphs on ≤ qn vertices (q < 1) fails for graphs. A proof of RC must use
  near-full cards. This is the graph analogue of the warning from Kocay's hypergraphs.

The question to ask of every route in this file: the real work is in reconstructing the
target class (2-connected, DR-class, dominating edge). An argument for that class that does
not use (a) finiteness, (b) undirected binary edges, and (c) near-full cards would also
apply in a failing setting, and is therefore wrong.

## Formalizable candidate steps

These are **not proposed**: the caller asked me not to run `desk.py propose`. The Lean
bodies are rough. They use `Recon.*` from `lean/Recon/Basic.lean` and Mathlib names checked
in `lean/.lake/packages/mathlib/Mathlib/`. Each needs fidelity review.

**C1 `found_hypomorphic_compl`.** Complements of hypomorphic graphs are hypomorphic.
```lean
∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Recon.Hypomorphic G H → Recon.Hypomorphic Gᶜ Hᶜ
```
- Easy, roughly 40–80 lines.
- `Recon.card Gᶜ x = (Recon.card G x)ᶜ` by `ext` plus `compl_adj` / `comap_adj` /
  `Subtype.ext_iff`.
- An isomorphism `A ≃g B` gives `Aᶜ ≃g Bᶜ` with the same equiv: `map_rel_iff'` via
  `compl_adj` and injectivity. Mathlib has `Embedding.complEquiv` (Maps.lean:671), but I
  found no `Iso` version.

**C2 `found_reconstructible_compl`.** G is reconstructible iff its complement is.
```lean
∀ (n : ℕ) (G : SimpleGraph (Fin n)), Recon.Reconstructible G ↔ Recon.Reconstructible Gᶜ
```
- Easy given C1: use `compl_compl` and the iso complement from C1.
- Holds for every n, including n = 2.

**C3 `found_far_pair_dominates_compl`.** If u and v are at distance > 2 in G (including
unreachable), then uv is an edge of Ḡ that dominates Ḡ.
```lean
∀ (n : ℕ) (G : SimpleGraph (Fin n)) (u v : Fin n), 2 < G.edist u v →
  Gᶜ.Adj u v ∧ ∀ x : Fin n, x = u ∨ x = v ∨ Gᶜ.Adj x u ∨ Gᶜ.Adj x v
```
- Easy. `SimpleGraph.two_lt_edist_iff` (Metric.lean, about line 162) gives `u ≠ v`,
  `¬ G.Adj u v` and `commonNeighbors = ∅`, and `compl_adj` finishes.
- Corollary C3': `∀ x y, Gᶜ.edist x y ≤ 3`.
- Checked by small-graph search: no witness for n ≤ 7, or in 2000 random graphs with
  n ≤ 10.

**C4 (reduction, root, e.g. a new program `yang` or under `found`).** The conjecture
follows from Kelly's disconnected case plus the "dominating edge or both diameters ≤ 2"
class.
```lean
Recon.ClassReconstructible (fun n G => ¬ G.Connected) →
Recon.ClassReconstructible (fun n G => G.Connected ∧ Gᶜ.Connected ∧
  ((∃ u v : Fin n, G.Adj u v ∧ ∀ x : Fin n, x = u ∨ x = v ∨ G.Adj x u ∨ G.Adj x v) ∨
   ∀ u v : Fin n, G.edist u v ≤ 2 ∧ Gᶜ.edist u v ≤ 2)) →
Recon.ReconstructionConjecture
```
- Medium, given C2 and C3.
- The proof:
  - case on `G.Connected` and `Gᶜ.Connected`; if Ḡ is disconnected, apply hypothesis 1 to
    Ḡ and use C2;
  - if some pair has `2 < G.edist`, then C3 puts Ḡ in the class (Ḡᶜ = G is connected), so
    use C2;
  - symmetrically for Ḡ;
  - otherwise both diameters are ≤ 2.
- `edist` takes values in ℕ∞, so `¬ (2 < d) ↔ d ≤ 2` is `not_lt`.
- A cleaner fleet shape is a *reduction* of `ReconstructionConjecture` with children C5'
  and the C4 class, but CLAUDE.md requires that children not reference the parent. A
  standalone conditional root is fine.

**C4' (Gupta–Mangal–Paliwal shape).** The same reduction, with target class "diam G ≤ 2,
or diam G = diam Ḡ = 3". Written with `∀ u v, G.edist u v ≤ 2` and similar. Medium. C4 is
simpler and at least as strong, so prefer it.

**C5 `discon_isolated_vertex`.** Graphs with an isolated vertex are reconstructible.
Universal vertex follows by C2 and `isUniversal_compl_iff_isIsolated` (Basic.lean:1133).
```lean
Recon.ClassReconstructible (fun n G => ∃ v : Fin n, G.IsIsolated v)
```
- Medium. It needs `kelly_edge_count` and `kelly_card_edges_add_degree` (both proposed) to
  get deg_H(σ v) = 0, then an extension of the card isomorphism across v.
- The extension lemma ("an iso of the cards at isolated vertices extends to an iso of the
  graphs") is reusable for regular graphs.

**C5' `discon_disconnected`.** Kelly: disconnected graphs are reconstructible.
```lean
Recon.ClassReconstructible (fun n G => ¬ G.Connected)
```
- Hard: it needs Kelly's lemma for counting connected components, or the
  Greenwell–Hemminger argument.
- It is the `discon` program's mandate, listed here because C4 needs it.

**C6 `regular_single_card_type`.** If all cards are isomorphic, G is regular.
```lean
∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  (∀ x y : Fin n, Nonempty (Recon.card G x ≃g Recon.card G y)) →
  ∃ d, G.IsRegularOfDegree d
```
- Easy, given `kelly_card_edges_add_degree`: isomorphic cards have equal edge counts, so
  degrees are equal.
- Fidelity note: this needs `DecidableRel G.Adj` and `LocallyFinite` instances for
  `IsRegularOfDegree` on `Fin n`; classical instances resolve this inside the statement.

## Mathlib map for this topic

Paths are under `lean/.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/`.

**Present:**
- `connected_or_connected_compl` (Connectivity/Connected.lean:386) and
  `connected_or_preconnected_compl` (:379). Either G or Ḡ is connected, which is crucial
  for C4.
- `Connected.of_isUniversal` (Connectivity/Connected.lean, about line 390).
- `Connected.induce_compl_singleton_of_degree_eq_one` (Connectivity/Connected.lean:1040).
- `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`
  (Acyclic.lean:556): every finite connected graph has a non-cut vertex. This is half of
  the "≥ 2 connected cards" argument.
- `edist`, `dist`, `edist_eq_one_iff_adj`, `edist_eq_two_iff` and `two_lt_edist_iff`
  (Metric.lean:131–175); `dist_le` (Metric.lean:230).
- `eccent`, `ediam`, `diam`, `radius`, `connected_iff_ediam_ne_top` and `ediam_top`
  (Diam.lean).
- `IsUniversal` (Basic.lean:1103), `IsIsolated` (Basic.lean:1038),
  `isUniversal_compl_iff_isIsolated` (Basic.lean:1133) and
  `isIsolated_compl_iff_isUniversal` (:1141).
- `universalVerts` and `deleteUniversalVerts` (UniversalVerts.lean).
- `compl_adj` (Basic.lean:248), `induce_adj` (Maps.lean:316), `comap_adj` (Maps.lean:136)
  and `Embedding.complEquiv` (Maps.lean:671).
- `card_edgeFinset_induce_compl_singleton` (DeleteEdges.lean:160): the card's edges are the
  edges left after deleting the incidence set. Useful for `kelly_*`.
- Edge connectivity: `IsEdgeReachable`, `IsEdgeConnected`,
  `isEdgeConnected_two_iff_forall_not_isBridge` (Connectivity/EdgeConnectivity.lean); and
  `IsBridge`, `isAcyclic_iff_forall_isBridge` (Acyclic.lean:170).

**Gaps:**
- **No vertex connectivity**: no κ(G), cut vertex, separator, k-connected predicate, block or
  block-cut tree. Workaround for 2-connected with n ≥ 3:
  `∀ x, (Recon.card G x).Connected`.
- **No `Iso` between complements.** Build it from the equiv in a few lines, as in C1.
- **No domination number.** Use an explicit ∃.
- No planarity, no geodetic or interval-regular graphs, no parity graphs.

## Open gaps

1. **Yang 1988 proof idea**: UNVERIFIED. I need the JGT text, or Lauri–Scapellato Ch. on
   reductions. Until then, any `yang` program step about 2-connectivity is a black box.
2. **Ramachandran–Monikandan 2009** (BICA): I could not access it. How does the combination
   of 2-connectivity with the complement work? Aravind–Monikandan 2026 Theorem 7 does not
   justify it.
3. **Monikandan–Balakumar 2014**: the full text was blocked. The exact definitions of
   interval-regular and the proof are UNVERIFIED.
4. **Gupta–Mangal–Paliwal 2003 primary text**: not read. There is a minor conflict in
   secondary sources over "= 3" versus "= 2" for Ḡ; the majority, and the mathematics,
   support 3.
5. **Zinchenko 2026 (two card types)**: unread and unrefereed. It deserves a thinker pass
   before anyone relies on it.
6. **Reduction to 3-connected graphs**: no source found either way. Whether this is known
   to be open or known to be achieved is UNVERIFIED.
7. **Digraph analogues**: does Kelly's disconnected-case argument, or Yang's, hold for
   digraphs? UNVERIFIED. This matters for the "what breaks" audit of any C5'-based route.
8. Journal venues for Bowler et al., Kocay, Fisher, Bollobás and Barrus–West are partly
   UNVERIFIED, as marked in each entry.
