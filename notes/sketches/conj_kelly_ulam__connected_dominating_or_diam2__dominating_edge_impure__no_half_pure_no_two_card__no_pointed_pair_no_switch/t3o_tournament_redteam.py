"""All non-reconstructible tournaments on n = 5, 6 vertices against the generic statements of
the sketch (brute force over labelled tournaments, numpy). Evidence only.
Printed per hypomorphic non-isomorphic pair: 2- and 3-anchorings, triples with (a), (b) of T3u,
Helly at 3-anchored triples."""
import itertools
import sys
from collections import defaultdict

import networkx as nx
import numpy as np

from t3o_digraph_redteam import ab_triples, anchored3, helly, pointed_ok


def pairs(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def canon_table(n):
    P = pairs(n)
    idx = {p: k for k, p in enumerate(P)}
    codes = np.arange(1 << len(P), dtype=np.int64)
    best = codes.copy()
    for perm in itertools.permutations(range(n)):
        new = np.zeros_like(codes)
        for k, (i, j) in enumerate(P):
            a, b = perm[i], perm[j]
            bit = (codes >> k) & 1
            if a < b:
                new |= bit << idx[(a, b)]
            else:
                new |= (1 - bit) << idx[(b, a)]
        np.minimum(best, new, out=best)
    return best


def card_codes(n, codes, v):
    Q = pairs(n - 1)
    idx = {p: k for k, p in enumerate(Q)}
    ren = {x: (x if x < v else x - 1) for x in range(n) if x != v}
    out = np.zeros_like(codes)
    for k, (i, j) in enumerate(pairs(n)):
        if v in (i, j):
            continue
        out |= ((codes >> k) & 1) << idx[(ren[i], ren[j])]
    return out


def to_tournament(n, code):
    D = nx.DiGraph()
    D.add_nodes_from(range(n))
    for k, (i, j) in enumerate(pairs(n)):
        if (code >> k) & 1:
            D.add_edge(i, j)
        else:
            D.add_edge(j, i)
    return D


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
    print(f"n={n}: {len(reps)} tournaments, {len(bad)} deck classes with more than one")
    for g in bad:
        D, R = to_tournament(n, g[0]), to_tournament(n, g[1])
        V = sorted(D)
        a2 = sum(1 for p in itertools.permutations(V, 2) for q in itertools.permutations(V, 2)
                 if pointed_ok(D, p[0], [p[1]], R, q[0], [q[1]])
                 and pointed_ok(D, p[1], [p[0]], R, q[1], [q[0]]))
        a3 = [(p, q) for p in itertools.permutations(V, 3) for q in itertools.permutations(V, 3)
              if anchored3(D, p, R, q)]
        print(f"   pair {g}: 2-anchorings {a2}, 3-anchorings {len(a3)}, "
              f"Helly at 3-anchored triples {sum(helly(D, *p) for p, _ in a3)}, "
              f"triples with (a), (b): {len(ab_triples(D))} and {len(ab_triples(R))}")


for n in map(int, sys.argv[1:]):
    main(n)
