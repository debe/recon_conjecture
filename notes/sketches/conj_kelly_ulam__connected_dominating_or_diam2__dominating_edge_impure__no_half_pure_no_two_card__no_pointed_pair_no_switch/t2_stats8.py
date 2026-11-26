"""All graphs on 8 vertices (built by one-vertex extension of the atlas graphs on 7 vertices,
deduplicated by canonical form; expected count 12346) against the classes C3, C2 of the
sketch. Evidence only.   python3 t2_stats8.py [kill-mode, default K]
"""
import itertools
import os
import sys
from collections import Counter

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from t2_lib import *  # noqa
from small_graphs import all_graphs  # noqa: E402


def graphs8():
    seen = set()
    for G in all_graphs(7):
        G = nx.convert_node_labels_to_integers(G)
        for k in range(8):
            for N in itertools.combinations(range(7), k):
                H = G.copy()
                H.add_node(7)
                H.add_edges_from((7, x) for x in N)
                c = canon(H)
                if c not in seen:
                    seen.add(c)
                    yield H


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "K"
    c = Counter()
    out3, out2 = [], []
    for G in graphs8():
        c["all"] += 1
        C = Census(G)
        c3 = in_triple_class_w(G, C, mode) is not None
        c2 = in_pair_class_w(G, C, mode) is not None
        c["C3"] += c3
        c["C2"] += c2
        if not c3:
            out3.append(g6(G))
        if not c2:
            out2.append(g6(G))
        if c["all"] % 2000 == 0:
            print(dict(c), flush=True)
    print("n = 8", mode, dict(c))
    print("outside C3:", out3)
    print("outside C2:", out2)


main()
