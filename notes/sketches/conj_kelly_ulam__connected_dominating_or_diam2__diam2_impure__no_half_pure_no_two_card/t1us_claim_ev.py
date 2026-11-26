"""Theorem S of sketch t1 (eigenvector class EV), strong single-card form. Evidence only.

  python3 tools/search/small_graphs.py counterexample --claim <this file> --n-min 3 --n-max 7

claim(G): if G is two-walk (a,b)-linear and A_G has an eigenvector f for the eigenvalue
a - deg u with f(u) != 0, then no re-attachment of u (other than N(u)) with |S| = deg u gives a
two-walk (a,b)-linear graph.  (Uses the symmetry of A_G; this is Zinchenko's Lemma 3.3 outside
the normal form.)   STATS counts how often the hypothesis holds.
"""
import os
import sys
from collections import Counter
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1us_lib import two_walk_linear, _kernel  # noqa: E402
from t1us_stats import n_alternatives  # noqa: E402

STATS = Counter()


def claim(G):
    ab = two_walk_linear(G)
    if ab is None:
        return True
    STATS["2wl graphs"] += 1
    nodes = sorted(G.nodes())
    n = len(nodes)
    hit = False
    for u in nodes:
        lam = ab[0] - G.degree(u)
        M = [[Fraction(0)] * n for _ in range(n)]
        for x in nodes:
            M[x][x] -= lam
            for y in G[x]:
                M[x][y] += 1
        basis, _ = _kernel(M, n)
        if any(v[u] != 0 for v in basis):
            STATS["(G,u) with eigenvector not vanishing at u"] += 1
            hit = True
            if n_alternatives(G, u, ab) != 0:
                return False
    if hit:
        STATS["graphs in EV"] += 1
    return True


if __name__ == "__main__":
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    "..", "..", "..", "tools", "search"))
    from small_graphs import all_graphs
    for n in range(3, 8):
        bad = [G for G in all_graphs(n) if not claim(G)]
        print(n, "witnesses:", len(bad), dict(STATS))
