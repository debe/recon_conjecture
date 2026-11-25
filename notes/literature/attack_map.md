# Attack map: routes to the reconstruction conjecture (round 1 synthesis)

Working hypothesis for this sweep: the conjecture is true, and we look for proof routes.
Nothing below is checked. Every citation and UNVERIFIED flag comes from the four survey notes.
The sources are in those notes:

- `hom_counts_and_logic.md`: homomorphism counts, counting logics, game comonads
- `algebraic_methods.md`: Kelly/Kocay, polynomials, Möbius inversion, edge reconstruction
- `groups_and_harmonic.md`: group actions, inclusion matrices, S_n orbits
- `structural_reductions.md`: Yang and the diameter reductions, the ℓ-deck program, the arXiv frontier

The Mathlib API maps are in `notes/mathlib/`.

## 1. The one lesson all four surveys agree on

**Counting alone cannot prove it.** Kelly's lemma, Kocay's lemma, homomorphism
indistinguishability, Weisfeiler–Leman/C^k, game comonads, Nash-Williams/ACKR inclusion–exclusion
and inclusion-matrix rank arguments all transfer verbatim to digraphs/tournaments (Stockmeyer)
and to k-uniform hypergraphs, k ≥ 3 (Kocay), where reconstruction fails. Some precise forms:

- Oliveira–Thatte (arXiv:1301.4121): the Kocay system has rank exactly the number of decks.
  Their framework is identical for digraphs and hypergraphs.
- The deck is the same as homomorphism counts from all F on ≤ n−1 vertices (van Dobben de
  Bruyn et al., arXiv:2610.07927, Lemma 3.5). The only gap to Lovász's theorem is the top
  layer: homomorphisms onto all n vertices.
- Nýdl (1992; via Kostochka–West, arXiv:2004.05527): for every α < 1, counts from subgraphs on
  ≤ αn vertices do not suffice. A proof must use that the target has exactly n vertices.
- The map from a graph to its deck has a large kernel (8 < 11 at n = 4;
  `groups_and_harmonic.md`, own derivation), so no linear (Lovász/Stanley-type) argument
  closes it. A proof must use that the input is a single S_n orbit.

So a real route needs **graph-specific input**. Two kinds are known:

1. **Spectral.** The characteristic polynomial is recognizable for graphs (Tutte 1979,
   UNVERIFIED primary) but not for 3-uniform hypergraphs (Cooper–Okur, arXiv:2312.16152). A
   librarian's own brute force found it failing for tournaments at n = 5. This computation is
   unconfirmed; red team to re-run `scripts/tourn.py`. It is not a complete invariant.
2. **Structural.** Complements, distance and domination: the Yang-style reductions use
   undirected connectivity (G or Ḡ is connected), which has no tournament analogue in that form.

## 2. Tiers of work, cheapest first

Each tier feeds the next. Ids are candidates, not proposals, unless marked.

### Tier 0: foundations (frozen, builders running in round 1)

- `found_hypomorphic_symm`, `found_hypomorphic_trans`, `found_hypomorphic_iso_invariant`
- `kelly_card_edges_add_degree`, `kelly_edge_sum`, `kelly_edge_count`

### Tier 1: the Kelly machinery every route uses

| Candidate | Claim | Difficulty | Note |
|---|---|---|---|
| `kelly_degree_sequence` | deg_H(σv) = deg_G(v) | easy given tier 0 | kelly note §2 |
| `kelly_induced_subset_count` | for k < n, the number of k-subsets inducing F is recognizable | medium | groups C2 |
| `kelly_hom_image_count` | homs from F with image size j < n agree; gives copy and hom counts | easy to medium | hom C1; one double count Σ_v h_j(F, G−v) = (n−j)·h_j(F, G) |
| `kelly_deleted_edge_power_sum` | Σ over \|S\| = s of e(G−S)^k is recognizable | medium | algebraic C3 |

### Tier 2: real reconstruction theorems (class results)

| Candidate | Claim | Difficulty | Note |
|---|---|---|---|
| `found_hypomorphic_compl`, `found_reconstructible_compl` | G is reconstructible iff Ḡ is | easy | structural C1, C2; needs an iso of complements by hand |
| `discon_isolated_vertex` | graphs with an isolated vertex are reconstructible; universal vertex via complement | medium | structural C5; tracer bullet for `discon` |
| `regular_reconstructible` | regular graphs are reconstructible | medium | needs the degree sequence; CLAUDE.md §10 |
| `discon_reconstructible` | disconnected graphs are reconstructible (Kelly 1957) | hard | needs `kelly_induced_subset_count` on components |

### Tier 3: a kernel-checked reduction of the conjecture itself

The strongest *elementary* reduction (structural note, C3/C4). It uses Aravind–Monikandan
arXiv:2601.00620 Lemma 4: two vertices at distance ≥ 3 in G form a dominating edge of Ḡ.

```
ReconstructionConjecture  ⇐  ClassReconstructible (¬ Connected)
                          ∧  ClassReconstructible (Connected ∧ Ḡ Connected ∧
                               (G has a dominating edge  ∨  diam G ≤ 2 ∧ diam Ḡ ≤ 2))
```

Proof sketch: by complement invariance, assume G and Ḡ are both connected. If diam G ≥ 3, then
Ḡ has a dominating edge, so pass to Ḡ. Otherwise diam G ≤ 2, and likewise diam Ḡ ≤ 2 or swap.
The C3 lemma survived exhaustive search for n ≤ 7, which is evidence only.

Once a root `ReconstructionConjecture` step exists, this is a `reduce` with 2–3 children. It
would be the first checked structure under the root: a reduction, not progress on the open core.
Yang's 2-connected reduction (1988) is deep and its proof idea is unknown to us, so it is not a
near-term target.

### Tier 4: graph-specific invariants (the spectral route)

- `kelly_charpoly_derivative`: (charpoly G)′ = Σ_v charpoly(G − v). This is Jacobi's formula
  with Fin-indexed submatrices, 300–600 lines. Mathlib lacks it, and it is worth upstreaming.
  Hypomorphic graphs then have equal derivatives, so the charpoly is recognizable up to the
  constant term.
- Tutte's full theorem (the constant term, i.e. det A) is the hard part. It needs Kocay/Sachs
  machinery that Mathlib lacks.
- `kelly_perfect_matching_count` as a reduction: an inclusion–exclusion identity for every G
  (algebraic C4), plus deleted-edge power sums (C3), plus the edge count.

### Not pursued now

- Edge reconstruction (Lovász, Müller, ACKR): it needs an edge-deck definition in `Basic.lean`
  (human), and an `edge` program. The ACKR route is purely finite and 800–1500 lines.
- Pure reformulations: the surjective-hom version, and invariance under adding an isolated
  vertex (arXiv:2610.07927 Ex. 3.8). They are clean in Lean but carry no new mathematical
  content.
- The S_n orbit-fibre reformulation: it needs a permutation action on `SimpleGraph`, which Mathlib
  lacks; about 600 lines and more.

## 3. Open subclasses that look attackable later

- Triangle-free graphs of diameter 2 with connectivity ≥ 4 (left open by Clifton et al.,
  arXiv:2210.00338).
- Bipartite graphs.
- Planar graphs: planarity is recognizable (Bilinski–Kwon–Yu), but the reconstruction is open.
- The two-card-type class (Zinchenko, arXiv:2611.13728, Nov 2026; unrefereed, UNVERIFIED).

## 4. Status of claimed proofs

There is no credible full proof:

- Raju Renjit (cs/0702119): withdrawn by the author.
- Mehendale (math/0503316): math.GM, no acceptance.
- McKay (arXiv:2102.01942): n ≤ 13 by computer.

## 5. Prior Lean work

SamuelSchlesinger/reconstruction-conjecture (Lean 4.28) claims Kelly's lemma, injective-hom
counts, Kocay cover counts, tr(Aᵏ) for k < n, and that disconnected and regular graphs are
reconstructible. It has **no licence**, so use it as a roadmap only and never copy code. It has
not been audited beyond a `sorry` grep.

## 6. Recommended next proposals (round 2)

1. `found_hypomorphic_compl` and `found_reconstructible_compl` (tier 2, easy; unlocks tier 3).
2. `kelly_degree_sequence` and `kelly_induced_subset_count` (tier 1).
3. `discon_isolated_vertex` (tier 2 tracer bullet).
4. A root step `ReconstructionConjecture`, approved by a human, to hang the tier 3 reduction
   from.
5. `kelly_charpoly_derivative` (tier 4, the first graph-specific brick).
