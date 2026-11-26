"""Tries to kill two candidate lemmas at n = 8 (evidence only):
  (L-CD)  cards pairwise non-isomorphic  ==>  G in NS
  (L-TW)  ... what fraction of TW graphs is in NS
Graphs on 8 vertices by one-vertex extension of the atlas (expected 12346).
"""
import itertools
import sys
from collections import Counter

import networkx as nx

import t1s_lib as L


def graphs8():
    seen = set()
    for G in L.all_graphs(7):
        G = nx.convert_node_labels_to_integers(G)
        for k in range(8):
            for N in itertools.combinations(range(7), k):
                H = G.copy()
                H.add_node(7)
                H.add_edges_from((7, x) for x in N)
                c = L.canon(H)
                if c not in seen:
                    seen.add(c)
                    yield H


c = Counter()
cd_out, tw_out = [], []
for G in graphs8():
    c["graphs"] += 1
    cc = {v: L.canon(L.card(G, v)) for v in G.nodes()}
    cd = len(set(cc.values())) == 8
    tw = all(cc[a] != cc[b] or set(G[a]) - {b} == set(G[b]) - {a}
             for a, b in itertools.combinations(G.nodes(), 2))
    c["CD"] += cd
    c["TW"] += tw
    if not tw:
        continue
    S = L.sw_pairs(G)
    ns = not L.has_balanced(G, S)
    c["TW and NS"] += ns
    c["CD and NS"] += (cd and ns)
    if not ns:
        iso = L.in_NSiso(G)
        c["TW not NS, NSiso"] += (iso is True)
        (cd_out if cd else tw_out).append((L.g6(G), "NSiso" if iso else "not NSiso"))
print(dict(c))
print("CD not NS:", cd_out[:30], len(cd_out))
print("TW (not CD) not NS:", tw_out[:10], len(tw_out))
