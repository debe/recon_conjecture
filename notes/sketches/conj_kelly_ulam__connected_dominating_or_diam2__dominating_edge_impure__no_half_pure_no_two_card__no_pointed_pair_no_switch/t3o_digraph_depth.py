"""Anchoring in all non-reconstructible digraph pairs on n = 4, 5 vertices. Evidence only.
For each hypomorphic non-isomorphic pair (D, R): the number of 2-anchorings and 3-anchorings
(ordered tuples p in D, q in R), and whether the Helly condition holds at a 3-anchored triple
of D (the generic triple twist lemma says it must not)."""
import itertools
import sys
from collections import defaultdict

import numpy as np

from t3o_digraph_redteam import (anchored3, canon_table, card_codes, helly, pointed_ok,
                                 to_digraph)


def main(n):
    can = canon_table(n)
    small = canon_table(n - 1)
    codes = np.arange(len(can), dtype=np.int64)
    reps = np.nonzero(can == codes)[0]
    decks = np.sort(np.stack([small[card_codes(n, reps, v)] for v in range(n)], axis=1), axis=1)
    groups = defaultdict(list)
    for code, dk in zip(reps.tolist(), map(tuple, decks.tolist())):
        groups[dk].append(code)
    bad = [g for g in groups.values() if len(g) > 1]
    viol = 0
    for g in bad:
        D, R = to_digraph(n, g[0]), to_digraph(n, g[1])
        V = sorted(D)
        a2 = sum(1 for p in itertools.permutations(V, 2) for q in itertools.permutations(V, 2)
                 if pointed_ok(D, p[0], [p[1]], R, q[0], [q[1]])
                 and pointed_ok(D, p[1], [p[0]], R, q[1], [q[0]]))
        a3 = [(p, q) for p in itertools.permutations(V, 3) for q in itertools.permutations(V, 3)
              if anchored3(D, p, R, q)]
        hel = [helly(D, *p) for p, _ in a3]
        viol += sum(hel)
        print(f"   pair {g}: arcs {D.number_of_edges()}, tournament "
              f"{D.number_of_edges() == n * (n - 1) // 2 and all(not D.has_edge(j, i) for i, j in D.edges())}, "
              f"2-anchorings {a2}, 3-anchorings {len(a3)}, Helly at 3-anchored triples: {sum(hel)}")
    print(f"n={n}: {len(bad)} pairs; violations of '3-anchored + Helly => isomorphic': {viol}")


for n in map(int, sys.argv[1:]):
    main(n)
