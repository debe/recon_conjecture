"""Sizes and non-vacuity for class US of sketch t1. Evidence only.

  python3 .../t1_stats.py            exhaustive n = 4..7 and the named graphs
"""
import itertools
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1us_lib import (two_walk_linear, classify, named, canon)  # noqa: E402
from t1us_claims import nonsingular, moving_card_iso  # noqa: E402
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import all_graphs, g6  # noqa: E402


def us_vertices(G):
    """vertices u at which the class clause of US holds (None if G is not two-walk-linear)."""
    ab = two_walk_linear(G)
    if ab is None:
        return None
    a = ab[0]
    return [u for u in G if nonsingular(G, a - G.degree(u)) and moving_card_iso(G, u)]


def n_alternatives(G, u, ab):
    N = frozenset(G[u])
    others = [x for x in G if x != u]
    base = G.copy()
    base.remove_node(u)
    k = 0
    for S in itertools.combinations(others, len(N)):
        if frozenset(S) == N:
            continue
        H = base.copy()
        H.add_node(u)
        H.add_edges_from((u, s) for s in S)
        if two_walk_linear(H) == ab:
            k += 1
    return k


def main():
    for n in range(4, 8):
        c = Counter()
        for G in all_graphs(n):
            ab = two_walk_linear(G)
            if ab is None:
                continue
            c["2wl non-regular"] += 1
            us = us_vertices(G)
            both = nx.is_connected(G) and nx.is_connected(nx.complement(G))
            if both:
                c["2wl, G and co-G connected"] += 1
            for u in G:
                ns = nonsingular(G, ab[0] - G.degree(u))
                k = n_alternatives(G, u, ab)
                c["(G,u)"] += 1
                if ns:
                    c["(G,u) nonsingular"] += 1
                    c["(G,u) nonsingular, %d alternatives" % k] += 1
                else:
                    c["(G,u) singular, %s alternatives" % (k if k < 2 else ">=2")] += 1
            if us:
                c["US"] += 1
                if both:
                    c["US, G and co-G connected"] += 1
                    cl = classify(G)
                    if not cl["pure"]:
                        c["US, both connected, not pure"] += 1
                        if not cl["D"]:
                            c["US, both connected, not pure, not D"] += 1
                            print("   ", n, g6(G), cl)
        print(n, dict(sorted(c.items())), flush=True)
    for name, G in named():
        ab = two_walk_linear(G)
        if ab is None:
            print(name, "not two-walk-linear")
            continue
        us = us_vertices(G)
        sing = [u for u in G if not nonsingular(G, ab[0] - G.degree(u))]
        print(name, "n=%d" % G.number_of_nodes(), "(a,b)=(%s,%s)" % ab,
              "US vertices: %d" % len(us), "singular vertices: %d" % len(sing), flush=True)


if __name__ == "__main__":
    main()
