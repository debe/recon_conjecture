"""Claim file for sketch t3 (steps 3-6 of Theorem T, strong single-graph form). Evidence only.

For every graph G, every pair u < v and every automorphism g of F = G - u - v let G_g be the
twist: G_g[S] = F, v attached to N_v, u attached to {x in S : g x in N_u}, [u ~ v] as in G.
(These are exactly the graphs H that contain a pair (a, b) with pointed isomorphisms
(G-u, v) -> (H-a, b) and (G-v, u) -> (H-b, a).)

  C1  degseq(G_g) = degseq(G)  <=>  the level-count filter adm_deg(g)
  C2  degseq(G_g) = degseq(G) and g preserves G-degrees on S  =>  G_g = G
  C3  degseq(G_g) = degseq(G) and g factorizes (the checked GLUE clause)  =>  G_g ~ G

  python3 tools/search/small_graphs.py counterexample --claim <this file> --n-min 3 --n-max 7 \
      --random 150 --random-n 8 9
"""
import itertools
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import pair_data, adm_deg, deg_preserving, factor_ok, canon  # noqa: E402

STATS = {"twists": 0, "same_degseq": 0, "c2": 0, "c3": 0, "nontrivial_c3": 0}


def claim(G):
    n = G.number_of_nodes()
    ds = sorted(d for _, d in G.degree())
    cG = None
    for u, v in itertools.combinations(sorted(G.nodes()), 2):
        S, A, Nu, Nv = pair_data(G, u, v)
        for g in A:
            STATS["twists"] += 1
            newNu = frozenset(x for x in S if g[x] in Nu)
            H = G.copy()
            for x in Nu:
                H.remove_edge(u, x)
            for x in newNu:
                H.add_edge(u, x)
            same = sorted(d for _, d in H.degree()) == ds
            if same != adm_deg(G, S, Nu, g):
                return False
            if not same:
                continue
            STATS["same_degseq"] += 1
            if deg_preserving(G, S, g):
                STATS["c2"] += 1
                if newNu != Nu:
                    return False
            if factor_ok(A, Nu, Nv, g):
                STATS["c3"] += 1
                if newNu != Nu:
                    STATS["nontrivial_c3"] += 1
                    if cG is None:
                        cG = canon(G)
                    if canon(H) != cG:
                        return False
    return True
