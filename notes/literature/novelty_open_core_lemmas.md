# Novelty check: lemmas derived for `conj_kelly_ulam__connected_dominating_or_diam2`

Literature only; nothing here is checked. Scope: the lemmas in
`notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t1.md … t4.md`.
Verdicts: **KNOWN** (exact source), **PARTIALLY KNOWN** (a special case or close variant),
**NOT FOUND** (we list what was searched). "Not found" never means new.
"Read" means we read the full text (PDF through `pdftotext`). "Secondary" means we know the
statement only through another paper's quotation, so the primary source is UNVERIFIED.

## Summary table

| # | Lemma | Verdict | Citation | What matches / differs |
|---|---|---|---|---|
| 1 | t2 Lemma B (neighbour-degree data per vertex along σ); t1 K1 step 3 (level counts) | **KNOWN** | Lauri–Scapellato 2003 (as Lemma 1.1 of Clifton–Liu–Mahmoud–Shantanam, arXiv:2210.00338, read); Woodall, Nottingham PG notes 2004/05, Thm 5(c) (read); Steane arXiv:1810.02602 §1 (read); Bondy–Hemminger 1977 (secondary, via Ramachandran arXiv:2305.14401) | The classical form: "given the card G − v, the degrees in G of the neighbours of v are reconstructible". Along a hypomorphism this is exactly Lemma B. The level-count form \|N ∩ L_k\| = \|S ∩ L_k\| restates it. Woodall's proof is the same degree comparison as t2's recursion. |
| 2 | t1 (★) / "ds-completable card" ⇒ reconstructible; t2 "degree separation" corollary | **KNOWN** | F. S. Mulla, *A class of graphs for which the Ulam conjecture holds*, Discrete Math. 22 (1978) 197–198, doi:10.1016/0012-365X(78)90126-7 (primary not read; statement via Steane, Thm 3) | Steane's Thm 3 [Mulla 1978]: "G − v is ds-completable iff no non-neighbour of v (excluding v) has degree one less than a neighbour of v." This is exactly (★), with an iff. Woodall Cor 5.1 states the sufficient direction, with w ranging over V ∖ N(u), so it includes w = u: a slightly stronger hypothesis. Also Bartha–Shuva 2014 (Steane's [4]; not read). |
| 3 | t4 Lemma G (adjacent ordered pairs typed by (deg x, G − x − y) are deck invariants) | **NOT FOUND** (techniques known) | Close relatives: Gupta–Mangal–Paliwal 2003 (pv/pav: pairs split by adjacency and number of common neighbours; secondary via arXiv:2601.00620); Manvel 1974 (Kostochka–West Lemma 2.3: typed ℓ-deck counts solved by back-substitution); Ramachandran arXiv:2305.14401 Obs. 3.7 (edges typed by endpoint degrees, digraph dacards) | No source states the split of the (n − 2)-deck by adjacency, with or without the degree type. The unsplit count π (Kelly's lemma on the (n − 2)-deck) and the typed count L1 (dacard × card deck) are classical. Gupta et al. split a *different* pair statistic (codegree) by adjacency. |
| 4 | t4 Lemma P (a pure degree class ⇒ reconstructible) | **PARTIALLY KNOWN** | Chinn 1971, LNM 186, 71–73 (statement via Kostochka–West arXiv:2004.05527 Thm 8.1, read; primary not read); Zhu, Ars Combin. 46 (1997) 245–250 (secondary via Farhadian; UNVERIFIED) | Chinn: "if the subgraphs obtained by deleting two vertices are pairwise non-isomorphic, G is reconstructible". This is t4's second corollary (every class is pure). Regular graphs, and "no two consecutive degrees" (Woodall Cor 5.1), are further special cases. The general statement for one degree class was not found. |
| 5a | t2 Lemma C (unique induced copy of F = G − u − v, and Aut(F) fixes N(u) ∩ S) | **KNOWN** (preprint) | A. Farhadian, *Reconstruction of graphs via asymmetry*, arXiv:1611.01609 (2016), Thm 4 and Cor 2 (read); the same as Thm 1 of Farhadian, arXiv:1704.01454 (read). We found no journal version. | Thm 4: "Let G be a graph with unique subgraph H = G∖{v,u}. If α(N_{v,H}) = N_{v,H} for any α ∈ Aut(H), then G is reconstructible." Identical to Lemma C, and the edge uv is settled by the edge count, as in t2 step 4. Cor 2 (asymmetric unique (n − 2)-subgraph) is t2's case W. This is the deterministic core of Bollobás 1990 as Kostochka–West describe it (§8). |
| 5b | t4 L5–L7: twist by g ∈ Aut(F); reconstructions ↔ double cosets A_u \ A / A_v; Aut(F) = A_u·A_v ⇒ reconstructible; anchors A2, A3 | **PARTIALLY KNOWN** (the ambiguity is known; the criterion was not found) | Farhadian arXiv:1611.01609 §6 and Lemma 4; arXiv:1704.01454 Thm 2, Lemma 10; Lauri, *Vertex-deleted and edge-deleted subgraphs*, Thm 6.1 (read; venue UNVERIFIED); Ramachandran arXiv:2305.14401 Thms 5.2, 5.8 ("pastings") | Farhadian names the obstruction ("s_v and s_w can arbitrarily move by the action of H's automorphism group") and handles only an orbit of size 2 with Aut ∈ {I, Z₂, Z₃, D₃}, or a vague "distance fixes the relative position" condition. Lauri Thm 6.1 is the one-graph analogue: pseudosimilar u, v give N(u), N(v) "similar but not interchange similar" in G − u − v. The factorization criterion and the double-coset count: NOT FOUND. |
| 6a | t3 S4 (walks from each vertex agree along σ) and S5 (rank W ≥ n − 1 ⇒ reconstructible, with σ itself an isomorphism) | **KNOWN** | Godsil–McKay, JCTB 30 (1981) 285–289, doi:10.1016/0095-8956(81)90046-0 (primary not read); He, EJC 14 (2007) #N14 = arXiv:math/0607142, Thm 4 and Cor 3 (read); Wang–Wen–Guo, EJC 32(4) (2025) #P4.33, doi:10.37236/13610 (read); Liu–Siemons, J. Algebraic Combin. 55 (2022) 663–690, arXiv:1911.00062, Thm 1.2 (abstract only) | He Cor 3: for hypomorphic real symmetric A, B (aligned by Σ), the projection of 1 onto each eigenspace agrees. This is equivalent to S4. WWG report that Godsil–McKay prove all graphs in a family that includes the controllable (rank W = n) and almost controllable (rank n − 1) graphs are reconstructible: this is S5. Liu–Siemons: "W determines the adjacency matrix if rank ≥ n − 1". That is S5core, so Δ = 0. Hagos, LAA 356 (2002) 103–111: rank W = number of main eigenvalues (secondary). |
| 6b | t3 S6 / S6core (rank W = n − 2: the second graph is a balanced block switch; a block of size 1 gives a transposition) | **KNOWN as labelled linear algebra** (preprint); the reconstruction use was not found | Zhu–Yue, *A characterization of walk-matrix equivalence at corank two via reciprocal WQH switching*, arXiv:2609.36895v2 (Oct 2026), Thms 1.1 and 1.2 (read; unrefereed). Background: Wang–Qiu–Hu, LAA 571 (2019), doi:10.1016/j.laa.2018.10.027; Lv–Liu–Wang–Wang, DAM 378 (2026) 337–347 | Thm 1.1: rank W_G = n − 2, H ≠ G on the same labels, then W_H = W_G iff H is a reciprocal WQH switch of G. In that case A − B = uvᵀ + vuᵀ, where u, v ∈ {0, ±1}ⁿ have disjoint supports and span ker Wᵀ. This is t3's P/Q block shape. Thm 1.2: a non-isomorphic walk mate needs n ≥ 10, which is sharper than t3's n ≥ 8. Neither paper assumes hypomorphism, so "aligned hypomorphic pair at corank 2" as a reconstruction lemma was not found. |

## Notes per lemma (proof idea, Lean estimate)

**1. Lemma B.**
- Woodall's proof: list the degrees of G − u and of G − v side by side; the degrees that drop
  belong to the neighbours. t2's induction on k (A_k ⇒ B_k ⇒ A_{k+1}) is the same comparison.
- Lean: medium, 250–450 lines as t2 estimates. It is pure `ncard` partition counting on top of
  the checked `L_kelly_degree_sequence`.
- Attribution to use: "folklore; Lauri–Scapellato 2003 (via arXiv:2210.00338 Lemma 1.1);
  Bondy–Hemminger 1977". The exact item in Bondy's *manual* (1991) and in Nash-Williams
  (1978) is UNVERIFIED: we read neither text.

**2. Mulla (★).**
- Primary not read. MaRDI gives the record and DOI; zbMATH 0436.05049.
- Both Steane and Woodall present the proof as the degree-matching argument in t1 steps 1–5.
- Lean: medium, given Lemma B plus the extension lemma (t1 §3).
- Cite as **Mulla 1978**, not as an own derivation.

**3. Lemma G.**
- Proof idea (t4): the bit law e(G − x − y) = e − deg x − deg y + [x ~ y], swap symmetry
  e_a = e_{s+1−a}, then telescoping.
- Searched without finding the statement:
  - Kostochka–West survey on ℓ-decks (full text);
  - Tan, DPhil thesis *Graph Reconstruction and Structure* (Oxford; full-text grep);
  - Lauri's survey (full text);
  - Aravind–Monikandan arXiv:2601.00620 (HTML);
  - Clifton et al. arXiv:2210.00338;
  - Woodall's notes;
  - Ramachandran arXiv:2305.14401;
  - Farhadian ×2;
  - web searches for "(n−2)-deck", "pairs of adjacent vertices", "G − u − v", "pair
    reconstruction" and "Kelly lemma pairs".
- Not consulted: Manvel 1974 (primary), Kocay 1981/1988, Chinn (primary), Bondy 1991, the
  Lauri–Scapellato book, Gupta–Mangal–Paliwal (primary).
- Lean: medium, 350–550 lines (t4).

**4. Lemma P.**
- Chinn's hypothesis forces every π_a(F) ≤ 2 (one unordered pair, both orders), so every
  degree class is pure. Lemma P therefore strictly generalises Chinn's theorem.
- Kostochka–West say Chinn proved it "in a stronger form". Farhadian (arXiv:1611.01609 §6)
  gives that form: some v such that all (n − 2)-subgraphs of G − v are unique. Both are
  secondary.
- Lean: 500–750 lines (t4). Chinn's theorem itself would be a short corollary once Lemma P
  is checked.

**5. Gluing.**
- 5a is Farhadian's Thm 4 almost word for word. Cite it and do not claim the lemma.
- The proof (identify the anchor in G − u and G − v by Kelly's lemma, then glue) is the same
  as t2's.
- Kostochka–West add one point: under Chinn's hypothesis, two cards rebuild everything except
  [u ~ v] (their account of Bollobás's argument).
- Müller 1976 (Comment. Math. Univ. Carolinae 17(4) 709–719) and Bollobás 1990 (JGT 14
  1–4) supply only the "almost every graph" input: large induced subgraphs are asymmetric and
  pairwise non-isomorphic. Lauri cites this as Korshunov 1971, Müller 1976 and Bollobás 1990.
  Primaries not read.
- 5b: the double-coset count and the criterion A = A_u A_v were not found. The closest are
  Farhadian Lemma 4 (small groups) and Ramachandran's isomorphic pastings, an unrefereed
  framework with no group criterion.
- Lean: 450–650 lines (t4); the risk is subtype plumbing.

**6. Spectral chain.**
- S1–S2 (Tutte 1979) and S3 are classical. S3 is the generating function φ(G − v)/φ(G); He's
  Cor 2 quotes Godsil–McKay Thm 3.2 for the squares of simple eigenvector entries.
- S4 is Godsil–McKay (He's proof, via the rank-one perturbation A + tJ).
- S5 is Godsil–McKay plus Liu–Siemons.
- S6 is Zhu–Yue's Thm 1.1 restricted to hypomorphic pairs. It is a 2026 preprint: cite it, and
  treat it as unrefereed.
- S5′ is Hong, JCTB 32 (1982) 245–256 (WWG Thm 4, read in WWG). WWG Thm 5 extends it to
  almost controllable cards.
- Lean:
  - S5core: easy to medium (pure matrix rank, `Matrix.rank`; t3 §8).
  - S4 and S2: hard. They need Tutte's theorem, which Mathlib lacks; see `attack_map.md`
    tier 4.
  - S6core: medium to hard (rank-2 symmetric decomposition over ℚ).

## Recommended attributions for proposals

| Lemma | Attribution to use |
|---|---|
| B | classical (Lauri–Scapellato 2003; Bondy–Hemminger 1977) |
| (★) | Mulla 1978 |
| Lemma C | Farhadian 2016 (arXiv), Thm 4 |
| S4 | Godsil–McKay 1981 |
| S5 | Godsil–McKay 1981 and Liu–Siemons 2022 |
| S6core | Zhu–Yue 2026 (arXiv) |
| Lemma P | generalises Chinn 1971; general form: no source found |
| Lemma G | no source found |
| Double-coset criterion | no source found |

## Sources consulted (all accessed 2026-11-25)

- Steane, arXiv:1810.02602: https://arxiv.org/abs/1810.02602 (full text)
- Mulla 1978 record: https://portal.mardi4nfdi.de/wiki/Publication:1140664
- Clifton et al., arXiv:2210.00338 (full text, Lemma 1.1)
- Woodall (author inferred from the URL, UNVERIFIED), *The Reconstruction Conjecture*, PG notes
  2004/05: https://www.maths.nottingham.ac.uk/plp/pmadw/PG/reconstruct.pdf (full text)
- Kostochka–West, arXiv:2004.05527 (full text, §8 and Lemma 2.3)
- Farhadian, arXiv:1611.01609 and arXiv:1704.01454 (full text)
- Lauri, *Vertex-deleted and edge-deleted subgraphs*: http://staff.um.edu.mt/jlau/research/UoM400.pdf
  (full text; venue and year UNVERIFIED)
- Ramachandran, arXiv:2305.14401 (full text)
- Aravind–Monikandan, arXiv:2601.00620 (HTML, extracted)
- He, arXiv:math/0607142 (full text)
- Wang–Wen–Guo, EJC 32(4) #P4.33: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v32i4p33 (full text)
- Zhu–Yue, arXiv:2609.36895v2 (full text)
- Liu–Siemons, arXiv:1911.00062 (abstract)
- Hagos 2002 record: https://portal.mardi4nfdi.de/wiki/Publication:1855393 (abstract only)
- Tan, DPhil thesis (Oxford ORA; full-text grep only)
