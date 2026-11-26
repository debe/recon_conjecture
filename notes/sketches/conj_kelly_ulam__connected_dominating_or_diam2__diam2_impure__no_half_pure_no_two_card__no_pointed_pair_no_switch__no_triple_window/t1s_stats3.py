"""NS with the three-card form Sw3 (evidence only): python3 t1s_stats3.py 7"""
import itertools
import sys
from collections import Counter
import t1s_lib as L

n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
c = Counter(); ex = []
for G in L.all_graphs(n):
    c["graphs"] += 1
    cc = {v: L.canon(L.card(G, v)) for v in G.nodes()}
    tw = all(cc[a] != cc[b] or set(G[a]) - {b} == set(G[b]) - {a} for a, b in itertools.combinations(G.nodes(), 2))
    S = L.sw_pairs(G); S3 = L.sw3_pairs(G)
    assert S3 <= S
    ns = not L.has_balanced(G, S); ns3 = not L.has_balanced(G, S3)
    c["TW"] += tw; c["NS"] += ns; c["NS3"] += ns3
    c["|Sw|"] += len(S); c["|Sw3|"] += len(S3)
    if ns3 and not tw:
        print("BUG: NS3 but not TW", L.g6(G))
    if tw and not ns3:
        ex.append(L.g6(G))
print(n, dict(c)); print("TW not NS3:", ex)
