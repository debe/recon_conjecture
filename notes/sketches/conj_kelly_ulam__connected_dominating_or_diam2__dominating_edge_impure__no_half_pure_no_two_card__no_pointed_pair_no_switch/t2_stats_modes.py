"""Class sizes by kill clause, window census, exhaustive n <= nmax. Evidence only.
  python3 t2_stats_modes.py 7
TRIV = every twist trivial at x;  DP = every twist degree preserving;  K = per twist TRIV or DP.
"""
import sys
from collections import Counter

import networkx as nx

from t2_lib import *
from small_graphs import all_graphs

for n in range(5, int(sys.argv[1]) + 1):
    c = Counter()
    for G in all_graphs(n):
        G = nx.convert_node_labels_to_integers(G)
        c["all"] += 1
        C = Census(G)
        pw, tw = pair_census_w(G, C), triple_census_w(G, C)
        c["pair census"] += bool(pw)
        c["triple census"] += bool(tw)
        for m in ("TRIV", "DP", "K"):
            c["pair " + m] += in_pair_class_w(G, C, m, pw) is not None
            c["triple " + m] += in_triple_class_w(G, C, m, tw) is not None
        c["triple old-census K"] += in_triple_class(G, C, "K") is not None
        c["pair old-census DP (= T+ or sym. variant)"] += in_pair_class(G, C, "DP") is not None
    print("n =", n, dict(c), flush=True)
