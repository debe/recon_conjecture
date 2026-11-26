"""Cayley graphs of D_k and A_4 minus a vertex against C3, C3t, C2. Evidence only.
  python3 t2_hunt_cayley.py D 6 6 | A4
"""
import sys
from collections import Counter

import networkx as nx

from t2_lib import *
from t3_lib import in_D2
from t3_hunt_cayley import dihedral, a4, cayley_graphs


def run(name, els, mul, e):
    c = Counter()
    seen = set()
    out = []
    for Cn, X, r in cayley_graphs(els, mul, e):
        G = X.copy()
        G.remove_node(r)
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
        c["C3"] += c3
        c["C3t"] += in_triple_class_w(G, C, "TRIV", tw) is not None
        c["C2"] += in_pair_class_w(G, C, "K") is not None
        c["D2 in C3"] += d2 and c3
        if not c3:
            out.append(g6(G))
    print(name, "order", len(els), dict(c), "outside C3:", out, flush=True)


if sys.argv[1] == "A4":
    run("A4", *a4())
else:
    for k in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
        run("D_%d" % k, *dihedral(k))
