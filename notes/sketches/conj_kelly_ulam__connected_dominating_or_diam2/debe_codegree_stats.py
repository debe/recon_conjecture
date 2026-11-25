"""Membership statistics for the classes of sketch debe_codegree. Evidence only.

  python3 .../debe_codegree_stats.py [n_max]     (default 7; 8 takes several minutes)

Single-graph facts: how many graphs of the parent class / of the two residual children lie in
the new classes.  Nothing here says anything about reconstructibility.
"""
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import (pair_table, pure_degrees, diam_le2, factorizes, unique_copy_pairs)  # noqa: E402
from t4_stats import dom_edge  # noqa: E402
from t1_stats import graphs  # noqa: E402
from debe_codegree_lib import classes  # noqa: E402

FACE = ["GhdYLc", "GhEKzW", "GhEJ]o", "K[N_ZpBVe`q{", "KbcrMZwA~c@r", "OpyHvCM]IFJpsMdwu`pJp"]


def residual_kind(G):
    Gc = nx.complement(G)
    if not (nx.is_connected(G) and nx.is_connected(Gc)):
        return None
    if dom_edge(G):
        return "DE"
    if diam_le2(G) and diam_le2(Gc):
        return "D2"
    return None


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    for g6 in FACE:
        G = nx.from_graph6_bytes(g6.encode())
        G = nx.convert_node_labels_to_integers(G)
        pi, e = pair_table(G)
        c = classes(G)
        print("face", g6, "n=%d" % G.number_of_nodes(), "pure_deg=%s" % bool(pure_degrees(G, pi, e)),
              {k: v for k, v in c.items()}, flush=True)
    for n in range(6, n_max + 1):
        cnt = {k: Counter() for k in ("DE", "D2")}
        left = {k: [] for k in ("DE", "D2")}
        allc = Counter()
        for G in graphs(n):
            c = classes(G)
            allc["total"] += 1
            for lab, v in c.items():
                if v:
                    allc[lab] += 1
            k = residual_kind(G)
            if k is None:
                continue
            cnt[k]["total"] += 1
            pi, e = pair_table(G)
            if pure_degrees(G, pi, e):
                continue
            cnt[k]["not_pure"] += 1
            for lab in ("R", "P", "CR", "CE", "CRE", "ALL"):
                if c[lab]:
                    cnt[k]["not_pure_" + lab] += 1
            a1 = any(factorizes(G, u, v)[0] for (u, v) in unique_copy_pairs(G))
            if a1:
                continue
            cnt[k]["residual"] += 1
            for lab in ("R", "P", "CR", "CE", "CRE", "ALL"):
                if c[lab]:
                    cnt[k]["residual_" + lab] += 1
            if not c["ALL"]:
                left[k].append(nx.to_graph6_bytes(G, header=False).decode().strip())
        print(n, "all graphs", dict(allc), flush=True)
        for k in ("DE", "D2"):
            print(n, k, dict(cnt[k]), flush=True)
            print(n, k, "residual outside ALL:", left[k], flush=True)


if __name__ == "__main__":
    main()
