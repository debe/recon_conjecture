"""Hunt: circulant graphs minus a vertex against the remainder and Theorem T. Evidence only.

  python3 .../t3_hunt_vt.py 9 13      # orders m of the circulant X; G = X - 0 has m - 1 vertices

Output per order: number of non-isomorphic G = X - 0, how many are in D2, in the D2 residual
(not PURE, not GLUE), in the remainder (also not LHP, not NARROW), and how many of each lie in
the classes of Theorem T (mode rigid) and Theorem T+.
"""
import itertools
import sys
import os
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import *  # noqa


def circulants(m):
    half = list(range(1, m // 2 + 1))
    seen = set()
    for r in range(1, len(half)):
        for sub in itertools.combinations(half, r):
            X = nx.circulant_graph(m, list(sub))
            k = canon(X)
            if k in seen:
                continue
            seen.add(k)
            yield sub, X


def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for m in range(lo, hi + 1):
        c = Counter()
        rem = []
        seen = set()
        for sub, X in circulants(m):
            G = X.copy()
            G.remove_node(0)
            G = nx.convert_node_labels_to_integers(G)
            k = canon(G)
            if k in seen:
                continue
            seen.add(k)
            c["G"] += 1
            if not in_D2(G):
                continue
            c["D2"] += 1
            fl, ty = remainder_flags(G)
            if fl["PURE"] or fl["GLUE"]:
                continue
            c["D2 residual"] += 1
            cid = pointed_classes(G, ty)
            t = bool(T_pairs(G, ty, cid, "rigid"))
            tp = bool(Tplus_pairs(G, ty, cid))
            c["residual in T"] += t
            if fl["REM"]:
                c["remainder"] += 1
                c["remainder in T"] += t
                c["remainder in T+"] += tp
                rem.append((sub, g6(G), len(auts(G)), t, tp))
        print("m =", m, dict(c), flush=True)
        for r in rem:
            print("   remainder member: S=%s g6=%s |Aut|=%d T=%s T+=%s" % r, flush=True)


if __name__ == "__main__":
    main()
