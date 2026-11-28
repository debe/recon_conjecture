# alt_triangle: an alternative split of `dominating_edge_impure` (not submitted)

Allgoerithm campaign round, 2026-11-25. **A sketch, not a result.** Nothing here is checked.

This step was reduced on `main` by debe's round 10 (PR #22) into `level_half_pure`,
`two_card_narrow` and `no_half_pure_no_two_card`. In parallel, and without knowing that, our
campaign built a different two-child split. Its lease had expired, which is how the work
overlapped. The gate accepted the split locally as `_r1`, but that name clashes with debe's
merged r1, so we discarded the local result and never shipped it. Only the bundle is kept, as an
idea.

## The split

Both children assume the parent's residual class: G and its complement connected, a dominating
edge, no pure degree class, and no unique-copy factorizing pair.

| Slug | Extra hypothesis |
|---|---|
| `triangle_free_dominating_edge` | some dominating edge uv has no common neighbour, so V = {u, v} ⊔ (N(u) − v) ⊔ (N(v) − u) |
| `dominating_edges_in_triangles` | every dominating edge uv has a common neighbour |

The implication is a single case split on that existential (`reduction_alt_triangle.lean`).
The red-team screens (`screen_*.py`, with the shared encoding in `screen_common.py`) found no
fidelity gap.

## Possible reuse

Updated 2026-11-28: since this note was written, the remainder has been reduced several levels
further. The open leaf is now
`dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window__phantom_and_mate__walk_degenerate`.
You could submit this split as a reduction of that leaf, or of whatever leaf is open when it is
used. To do that, add the leaf's extra negations to each child, and rename both the slugs and
the R theorem for that parent (`gate.py next-reduction`). The triangle-free branch has an explicit vertex partition, which
may make a counting argument easier. That is untested.

## Files

| File | What |
|---|---|
| `reduction_alt_triangle.json` | the bundle (its parent and proof_file paths refer to the old target) |
| `reduction_alt_triangle.lean` | the implication, as it was accepted locally |
| `screen_*.py` | red-team fidelity screens |
