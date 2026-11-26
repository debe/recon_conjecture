"""Variants and cross-tabs (evidence only): python3 t1s_variants.py 7
local  : no vertex meets both a switchable edge and a switchable non-edge
plain  : Sw has no nonempty subset balanced at every vertex (degrees of the far ends ignored)
NS     : Sw has no nonempty degree-balanced subset
TW     : any two vertices with isomorphic cards are twins (N(a)-b = N(b)-a)
CD     : cards pairwise non-isomorphic
"""
import itertools
import sys
from collections import Counter

import t1s_lib as L

n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
c = Counter()
ex = []
for G in L.all_graphs(n):
    c["graphs"] += 1
    S = L.sw_pairs(G)
    local = not any(any(G.has_edge(*p) for p in S if v in p) and any(not G.has_edge(*p) for p in S if v in p)
                    for v in G.nodes())
    plain = not L.has_balanced(G, S, refined=False)
    ns = not L.has_balanced(G, S)
    cc = {v: L.canon(L.card(G, v)) for v in G.nodes()}
    cd = len(set(cc.values())) == n
    tw = all(cc[a] != cc[b] or set(G[a]) - {b} == set(G[b]) - {a}
             for a, b in itertools.combinations(G.nodes(), 2))
    reg = len(set(d for _, d in G.degree())) == 1
    c["local"] += local; c["plain"] += plain; c["NS"] += ns
    c["CD"] += cd; c["TW"] += tw
    c["CD and NS"] += (cd and ns); c["TW and NS"] += (tw and ns)
    c["NS and not TW"] += (ns and not tw)
    if tw and not ns:
        c["TW not NS"] += 1
        iso = L.in_NSiso(G)
        c["TW not NS, NSiso"] += (iso is True)
        if len(ex) < 15:
            ex.append((L.g6(G), "reg" if reg else "nonreg", "NSiso" if iso else "not NSiso"))
print(n, dict(c))
print("TW but not NS:", ex)
