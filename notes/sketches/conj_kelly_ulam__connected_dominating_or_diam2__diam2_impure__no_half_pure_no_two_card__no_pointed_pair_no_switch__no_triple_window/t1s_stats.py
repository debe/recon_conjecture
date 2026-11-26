"""Class sizes (evidence only): python3 t1s_stats.py 7
NS    : Sw(G) has no nonempty degree-balanced subset
NSv   : the same with the viewer clause in Sw
NSiso : every degree-balanced switch along Sw is isomorphic to G
Also: number of graphs with pairwise non-isomorphic cards ('distinct cards'), and NS among them.
"""
import sys
from collections import Counter

import networkx as nx

import t1s_lib as L

n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
c = Counter()
out_examples = []
for G in L.all_graphs(n):
    c["graphs"] += 1
    reg = len(set(d for _, d in G.degree())) == 1
    cards = [L.canon(L.card(G, v)) for v in G.nodes()] if hasattr(L, "card") else None
    S = L.sw_pairs(G)
    ns = not L.has_balanced(G, S)
    Sv = L.sw_pairs(G, viewer=True)
    nsv = not L.has_balanced(G, Sv)
    iso = L.in_NSiso(G, viewer=True)
    c["Sw empty"] += (not S)
    c["NS"] += ns
    c["NSv"] += nsv
    c["NSiso"] += (iso is True)
    c["NSiso undecided"] += (iso is None)
    c["regular"] += reg
    c["nonregular"] += (not reg)
    c["nonregular NSiso"] += (not reg and iso is True)
    c["regular NSiso"] += (reg and iso is True)
    if not reg and iso is False and len(out_examples) < 12:
        out_examples.append(L.g6(G))
print(n, dict(c))
print("non-regular outside NSiso (first 12):", out_examples)
