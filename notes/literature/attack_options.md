# Attack options for the two open residuals

Merged from `options_algebraic.md`, `options_combinatorial.md` and `options_logic_topology.md`
(2026-11-25). Targets:
- `conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure`;
- `conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure`.

Nothing here is checked; every option is a plan. Small-graph facts below were used only to
decide where to spend effort. They are not arguments.

## What the residual graphs look like (known members, evidence only)

- **Shape:** prime (no non-trivial module), p-connected, no clique separator.
- **Degrees:** typically two consecutive values, d and d + 1, half the vertices each.
- **Self-complementary:** many members are self-complementary, a shape shared with Stockmeyer's
  self-converse tournament pairs.
- **Walk matrix:** most members have walk-matrix rank 2, i.e. exactly two main eigenvalues.
  **Godsil–McKay (rank ≥ n − 1) and the corank-2 switch analysis are void on this face.** This
  retracts the earlier recommendation to formalize the spectral route first.
- **More members:** an SRG minus one vertex (Paley(13), 4×4 rook, Shrikhande, Clebsch) lies in
  `diam2_impure`.

## Ranked options

| # | Option | Graph-specific? | Lean cost | First lemma | Source |
|---|---|---|---|---|---|
| 1 | **Codegree-refined pair typing**: type pairs by (deg x, G − x − y, codeg(x, y), adjacency); a pure class under this finer key would extend checked Lemma P | yes (bit law) | low, on top of the checked Lemma P / Kelly files | `kelly_pair_codegree_count` (Gupta–Mangal–Paliwal 2003: common-neighbour pair counts split by adjacency are recognizable) | options_combinatorial O3 |
| 2 | **Two card types**: Zinchenko arXiv:2611.13728 (Nov 2026, unrefereed) claims graphs whose deck has exactly 2 card types are reconstructible; its reduction forces degrees d, d + 1, the residual's shape | yes (symmetric adjacency, per the paper) | unknown until the proof is read; then a reduction child `t(G) = 2` | a paper audit of §§3–10 by a thinker, then a child statement | options_logic_topology #1 |
| 3 | **Tutte-free one-card closed-walk class**: Jacobi's formula φ′(G) = Σ φ(G − v) fixes closed walks of length ≤ n − 1 at v along σ, giving a one-card feasibility test | no on its own (has a tournament analogue), so a reduction child only | moderate; Jacobi's charpoly identity is a Mathlib gap | `jacobiCharpoly` | options_algebraic #1 |
| 4 | **Two-deleted spectral identity** (Desnanot–Jacobi: φ(M∖0)φ(M∖1) − φ(M)φ(M∖{0,1}) = adj(tI − M)₀₁² for symmetric M). It speaks about the two-deleted subgraphs in which "impure" is phrased. **Guess.** | yes (symmetric matrix) | moderate; Desnanot–Jacobi is a Mathlib gap | `twoMinor` | options_algebraic #3 |
| 5 | **Structure theory of impure pairs**, modelled on pseudosimilarity (Godsil–Kocay; Kocay, cosets) | no alone; must be combined with the bit law | thinker work first | none yet | options_combinatorial O2 |
| 6 | **Two-main-eigenvalue split**: Σ_{w∼v} deg w = a·deg v + b is recognizable from neighbour-degree data; it isolates the face where walk methods are void | n/a (bookkeeping) | low | `twoMainRecognizable` | options_algebraic #2 |
| 7 | **Modular / P4 carving** (Skums 2008, arXiv:0804.4093; Brignall–Georgiou–Waters 2012, arXiv:1112.1509) | half (Ille's recognizability fails for tournaments) | low as a child | p-disconnected ⇒ reconstructible | both notes |

## Ruled out or deprioritized (reasons in the source notes)

- Godsil–McKay walk-matrix rank ≥ n − 1, the generalized-spectrum (DGS) criteria and the rank
  n − 2 switch: void on rank-2 members.
- Hom-indistinguishability over restricted classes and Ehrenfeucht–Fraïssé games: they
  quantify over targets of every size.
- A "deck comonad": a reformulation only.
- Clique/independence complexes and Euler characteristics: trivially recognizable, nothing
  more found.
- Matroid and topological decks; vertex-transitive and Cayley graphs (regular, already
  excluded); posets.
- Self-complementary structure: shared with Stockmeyer's counterexamples.
- Almost-every-graph arguments, ℓ-decks, switching, graph limits and products: generic, no bite.

## Literature cautions

- Aravind–Monikandan arXiv:2601.00620 has proof gaps (Cor 14, Thm 16, Thms 20–21).
- Zinchenko arXiv:2611.13728 is two weeks old and unrefereed.

## Process notes

- **The 2026 Lean RH proof.** The Lean community post (2026-11-21) describes only certification:
  statement isolation, `comparator`, and replay by independent kernels on an inert export. It
  does not mention AI; the AI involvement reported elsewhere is UNVERIFIED.
- **Our gap:** a second-kernel replay of `Checked/` in CI. That is a trusted change, so it is
  for the human.
- **Certificates:** our gate forbids string literals and `ofReduceBool`, so SAT/LRAT
  certificates are out. Only `decide`-sized checks fit.
