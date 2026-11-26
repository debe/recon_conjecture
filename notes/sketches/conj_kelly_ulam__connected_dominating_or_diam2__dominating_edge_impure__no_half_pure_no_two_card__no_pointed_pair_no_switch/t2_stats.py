"""Class sizes, exhaustive for small n, and the dominating-edge / D2 remainders. Evidence only.

  python3 t2_stats.py 7
Classes (see t2.md):
  C3    triple window census + clause K at the pointed stabiliser
  C3t   triple window census + every pointed-stabiliser twist trivial at x
  C2    pair window census + clause K at Aut(F)            (pair analogue)
  C3o   triple census in the form of T+ ((i) or symmetric, (ii)) + clause K
"""
import os
import sys
from collections import Counter

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from t2_lib import *  # noqa
from t3_lib import remainder_flags, T_pairs, Tplus_pairs, pointed_classes  # noqa
from small_graphs import all_graphs  # noqa: E402
import t1us_lib as U  # noqa: E402


def dom_edge(G):
    V = set(G)
    return any(set(G[a]) | set(G[b]) | {a, b} == V for a, b in G.edges())


def main():
    nmax = int(sys.argv[1])
    for n in range(4, nmax + 1):
        c = Counter()
        left = []
        for G in all_graphs(n):
            G = nx.convert_node_labels_to_integers(G)
            c["all"] += 1
            C = Census(G)
            tw = triple_census_w(G, C)
            pw = pair_census_w(G, C)
            c3 = in_triple_class_w(G, C, "K", tw) is not None
            c3t = in_triple_class_w(G, C, "TRIV", tw) is not None
            c2 = in_pair_class_w(G, C, "K", pw) is not None
            c3o = in_triple_class(G, C, "K") is not None
            c["C3"] += c3
            c["C3t"] += c3t
            c["C2"] += c2
            c["C3o"] += c3o
            c["C2 not C3"] += c2 and not c3
            c["C3 not C2"] += c3 and not c2
            both = nx.is_connected(G) and nx.is_connected(nx.complement(G))
            if not both:
                continue
            fl, ty = remainder_flags(G)
            kind = "D2" if fl["D2"] else ("DE" if dom_edge(G) else None)
            if kind is None or fl["PURE"] or fl["GLUE"] or fl["LHP"] or fl["NARROW"]:
                continue
            cid = pointed_classes(G, ty)
            t = bool(T_pairs(G, ty, cid, "rigid")) or bool(Tplus_pairs(G, ty, cid))
            c[kind + " remainder (before T, T+, US)"] += 1
            if t:
                continue
            us = U.two_walk_linear(G) is not None   # necessary for US
            c[kind + " outside T, T+"] += 1
            c[kind + " outside T, T+ and two-walk-linear"] += us
            c[kind + " outside T, T+: in C3"] += c3
            c[kind + " outside T, T+: in C3t"] += c3t
            c[kind + " outside T, T+: in C2"] += c2
            left.append((g6(G), "C3" if c3 else "-", "C2" if c2 else "-"))
        print("n =", n, dict(c), "\n   residual members:", left, flush=True)


main()
