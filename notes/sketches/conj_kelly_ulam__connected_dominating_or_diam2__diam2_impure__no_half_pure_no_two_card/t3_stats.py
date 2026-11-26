"""Class sizes for sketch t3, exhaustive n <= 7, plus a random self-complementary hunt.
Evidence only.

  python3 .../t3_stats.py small 7       # all graphs on 4..7 vertices
  python3 .../t3_stats.py sc 12 150     # random self-complementary graphs on 12 vertices
"""
import os
import random
import sys
from collections import Counter

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from t3_lib import *  # noqa
from small_graphs import all_graphs  # noqa: E402
from t4_probe_selfcompl import random_sc  # noqa: E402


def dom_edge(G):
    V = set(G)
    return any(set(G[a]) | set(G[b]) | {a, b} == V for a, b in G.edges())


def small(nmax):
    for n in range(4, nmax + 1):
        c = Counter()
        left = []
        for G in all_graphs(n):
            G = nx.convert_node_labels_to_integers(G)
            c["all"] += 1
            ty = pair_types(G)
            cid = pointed_classes(G, ty)
            t0 = bool(T_pairs(G, ty, cid, "rigid"))
            tp = bool(Tplus_pairs(G, ty, cid))
            t = t0 or tp
            c["T"] += t0
            c["T star"] += bool(T_pairs(G, ty, cid, "star"))
            c["T+"] += tp
            c["T or T+"] += t
            both = nx.is_connected(G) and nx.is_connected(nx.complement(G))
            if not both:
                continue
            fl, _ = remainder_flags(G)
            kind = "D2" if fl["D2"] else ("DE" if dom_edge(G) else None)
            if kind is None or fl["PURE"] or fl["GLUE"]:
                continue
            c[kind + " residual"] += 1
            c[kind + " residual in T or T+"] += t
            if not (fl["LHP"] or fl["NARROW"]):
                c[kind + " remainder"] += 1
                c[kind + " remainder in T or T+"] += t
                if not t:
                    left.append(g6(G))
        print("n =", n, dict(c), "remainder outside T and T+:", left, flush=True)


def sc(n, count):
    rng = random.Random(11)
    shapes = {12: [(12,), (8, 4), (4, 4, 4)], 13: [(12,), (8, 4), (4, 4, 4)], 9: [(8,), (4, 4)],
              8: [(8,), (4, 4)], 16: [(16,), (8, 8), (4, 4, 4, 4)]}[n]
    for shape in shapes:
        c = Counter()
        seen = set()
        left = []
        for _ in range(count):
            G = random_sc(n, shape, rng)
            if G is None or not in_D2(G):
                continue
            k = canon(G)
            if k in seen:
                continue
            seen.add(k)
            c["D2"] += 1
            ty = pair_types(G)
            if has_pure(G, ty):
                continue
            c["not pure"] += 1
            fl, _ = remainder_flags(G)
            if not fl["REM"]:
                continue
            c["remainder"] += 1
            cid = pointed_classes(G, ty)
            t = bool(T_pairs(G, ty, cid, "rigid")) or bool(Tplus_pairs(G, ty, cid))
            c["remainder in T or T+"] += t
            if not t:
                left.append((g6(G), len(auts(G))))
        print("self-complementary n =", n, shape, dict(c), "remainder outside T:", left, flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "small":
        small(int(sys.argv[2]))
    else:
        sc(int(sys.argv[2]), int(sys.argv[3]))
