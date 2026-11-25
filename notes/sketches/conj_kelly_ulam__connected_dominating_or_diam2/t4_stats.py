"""Coverage of the t4 classes, exhaustively for n <= n_max (default 7; 8 takes minutes).

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t4_stats.py [n_max]

Evidence only. Columns, per class (ALL graphs / parent class PAR / DE branch / D2 branch):
  total   number of graphs
  star    (star) of t1 at some vertex (degree separation of t2)
  pure    some pure degree class (Lemma P of t4)
  uniq    some vertex of unique degree whose class is pure (Corollary U)
  s|p     star or pure
  glue    some anchored pair (A1, A2 or A3) with Aut(F) = Stab(N_u) Stab(N_v)
  any     star or pure or glue
"""
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import (pair_table, pure_degrees, star_vertices, in_D2, diam_le2, factorizes,
                    gap_anchored_pairs, typed_anchored_pairs, unique_copy_pairs)  # noqa: E402
from t1_stats import graphs  # noqa: E402
from small_graphs import g6  # noqa: E402


def dom_edge(G):
    nodes = set(G.nodes())
    return any(nodes <= ({u, v} | set(G[u]) | set(G[v])) for u, v in G.edges())


def glue(G, pi, e):
    pairs = set(gap_anchored_pairs(G)) | set(typed_anchored_pairs(G, pi, e)) | set(unique_copy_pairs(G))
    for (u, v) in pairs:
        if factorizes(G, u, v)[0]:
            return True
    return False


def flags(G):
    pi, e = pair_table(G)
    pure = pure_degrees(G, pi, e)
    degc = Counter(d for _, d in G.degree())
    f = {
        "star": bool(star_vertices(G)),
        "pure": bool(pure),
        "uniq": any(degc[a] == 1 for a in pure),
    }
    f["s|p"] = f["star"] or f["pure"]
    f["glue"] = glue(G, pi, e)
    f["any"] = f["s|p"] or f["glue"]
    return f


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    cols = ["star", "pure", "uniq", "s|p", "glue", "any"]
    for n in range(5, n_max + 1):
        tot = {k: Counter() for k in ("ALL", "PAR", "DE", "D2")}
        left = []
        for G in graphs(n):
            cls = ["ALL"]
            Gc = nx.complement(G)
            if nx.is_connected(G) and nx.is_connected(Gc):
                if dom_edge(G):
                    cls += ["PAR", "DE"]
                elif diam_le2(G) and diam_le2(Gc):
                    cls += ["PAR", "D2"]
            f = flags(G)
            for c in cls:
                tot[c]["total"] += 1
                for k in cols:
                    tot[c][k] += f[k]
            if "D2" in cls and not f["any"]:
                left.append(g6(G))
        for c in ("ALL", "PAR", "DE", "D2"):
            print(n, c, "total", tot[c]["total"], " ".join(f"{k}={tot[c][k]}" for k in cols), flush=True)
        print(n, "D2 graphs outside every t4 class:", len(left), left[:40], flush=True)


if __name__ == "__main__":
    main()
