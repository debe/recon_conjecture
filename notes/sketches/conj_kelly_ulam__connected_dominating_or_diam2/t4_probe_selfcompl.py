"""Hunt among self-complementary graphs (evidence only).

A self-complementary graph has an antimorphism tau whose cycles have length divisible by 4
(plus at most one fixed point). Random such graphs: choose tau, then choose one bit per
tau-orbit of pairs, alternating along the orbit. The D2 ones are tested against the t4 classes.
'GhEJ]o' (n = 8, |Aut| = 8, two vertex orbits) is of this kind and lies outside
star / pure / glue / T.

  python3 .../t4_probe_selfcompl.py [seed]
"""
import itertools
import os
import random
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import in_D2, pair_table, pure_degrees, star_vertices  # noqa: E402
from t4_stats import glue  # noqa: E402
from t4_probe_transport import in_T  # noqa: E402
from small_graphs import canon, g6  # noqa: E402


def random_sc(n, shape, rng):
    tau = {}
    pos = 0
    for L in shape:
        for i in range(L):
            tau[pos + i] = pos + (i + 1) % L
        pos += L
    for x in range(pos, n):
        tau[x] = x
    G = nx.empty_graph(n)
    seen = set()
    for a, b in itertools.combinations(range(n), 2):
        if (a, b) in seen:
            continue
        orbit = []
        x, y = a, b
        while True:
            key = (min(x, y), max(x, y))
            if orbit and key == orbit[0]:
                break
            orbit.append(key)
            x, y = tau[x], tau[y]
        if len(orbit) % 2:
            return None
        bit = rng.random() < 0.5
        for i, key in enumerate(orbit):
            seen.add(key)
            if bit == (i % 2 == 0):
                G.add_edge(*key)
    return G


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
    plans = [(8, (8,)), (8, (4, 4)), (9, (8,)), (9, (4, 4)), (12, (12,)), (12, (8, 4)),
             (12, (4, 4, 4)), (13, (12,)), (13, (4, 4, 4)), (16, (16,)), (16, (8, 8)),
             (16, (4, 4, 4, 4))]
    for n, shape in plans:
        c = Counter()
        left = []
        seen = set()
        for _ in range(400 if n <= 13 else 120):
            G = random_sc(n, shape, rng)
            if G is None or not in_D2(G):
                continue
            k = canon(G)
            if k in seen:
                continue
            seen.add(k)
            pi, e = pair_table(G)
            reg = len(set(d for _, d in G.degree())) == 1
            s = bool(star_vertices(G))
            p = bool(pure_degrees(G, pi, e))
            gl = glue(G, pi, e)
            t = s or p or in_T(G)
            c["D2"] += 1
            c["regular"] += reg
            c["star"] += s
            c["pure"] += p
            c["glue"] += gl
            c["T"] += t
            if not (s or p or gl or t):
                c["none"] += 1
                left.append(g6(G))
        print(n, shape, dict(c), left[:6], flush=True)


if __name__ == "__main__":
    main()
