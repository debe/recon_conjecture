"""Sizes of the residual children of sketch t4 (section 11), exhaustive. Evidence only.

  python3 .../t4_stats_residual.py [n_max]     (default 7; 8 takes a few minutes)

Columns per class (DE = G, co-G connected with a dominating edge; D2 = both diameters <= 2):
  total / not pure / not pure and no glue with anchor A3 / with anchor A1 (the residual
  children as stated in Lean) / with anchor A2 / with any anchor / additionally not (star).
"""
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import (pair_table, pure_degrees, star_vertices, diam_le2, factorizes,
                    gap_anchored_pairs, typed_anchored_pairs, unique_copy_pairs)  # noqa: E402
from t4_stats import dom_edge  # noqa: E402
from t1_stats import graphs  # noqa: E402


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    for n in range(6, n_max + 1):
        c = {k: Counter() for k in ("DE", "D2")}
        for G in graphs(n):
            Gc = nx.complement(G)
            if not (nx.is_connected(G) and nx.is_connected(Gc)):
                continue
            if dom_edge(G):
                k = "DE"
            elif diam_le2(G) and diam_le2(Gc):
                k = "D2"
            else:
                continue
            c[k]["total"] += 1
            pi, e = pair_table(G)
            if pure_degrees(G, pi, e):
                continue
            c[k]["not_pure"] += 1
            a3 = any(factorizes(G, u, v)[0] for (u, v) in gap_anchored_pairs(G))
            if not a3:
                c[k]["not_pure_no_A3glue"] += 1
            a1 = any(factorizes(G, u, v)[0] for (u, v) in unique_copy_pairs(G))
            a2 = any(factorizes(G, u, v)[0] for (u, v) in typed_anchored_pairs(G, pi, e))
            if not a1:
                c[k]["not_pure_no_A1glue"] += 1
            if not a2:
                c[k]["not_pure_no_A2glue"] += 1
            anyglue = a1 or a2 or a3
            if not anyglue:
                c[k]["not_pure_no_glue"] += 1
                if not star_vertices(G):
                    c[k]["not_pure_no_glue_no_star"] += 1
        for k in ("DE", "D2"):
            print(n, k, dict(c[k]), flush=True)


if __name__ == "__main__":
    main()
