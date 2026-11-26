"""Hunt for graphs outside C3 among circulants minus one or two vertices. Evidence only.
  python3 t2_hunt_vt.py 9 13 [two]
"""
import itertools
import sys
from collections import Counter

import networkx as nx

from t2_lib import *
from t3_lib import in_D2


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
    two = len(sys.argv) > 3
    for m in range(lo, hi + 1):
        c = Counter()
        seen = set()
        out = []
        for sub, X in circulants(m):
            drops = [(0,)] if not two else [(0, j) for j in range(1, m // 2 + 1)]
            for drop in drops:
                G = X.copy()
                G.remove_nodes_from(drop)
                G = nx.convert_node_labels_to_integers(G)
                k = canon(G)
                if k in seen:
                    continue
                seen.add(k)
                c["G"] += 1
                d2 = in_D2(G)
                c["D2"] += d2
                C = Census(G)
                tw = triple_census_w(G, C)
                c3 = in_triple_class_w(G, C, "K", tw) is not None
                c3t = in_triple_class_w(G, C, "TRIV", tw) is not None
                c2 = in_pair_class_w(G, C, "K") is not None
                c["C3"] += c3
                c["C3t"] += c3t
                c["C2"] += c2
                c["D2 in C3"] += d2 and c3
                if not c3:
                    out.append((sub, drop, g6(G), "census classes %d" % len(tw)))
        print("m =", m, "two" if two else "one", dict(c), "outside C3:", out, flush=True)


main()
