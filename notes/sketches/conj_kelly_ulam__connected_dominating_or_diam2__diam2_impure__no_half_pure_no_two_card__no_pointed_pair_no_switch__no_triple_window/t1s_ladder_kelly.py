"""Kelly rungs (evidence only): python3 t1s_ladder_kelly.py 7
BS_k : every nonempty degree-balanced D inside Sw(G) such that G^D and G have the same number
       of induced copies of every graph on at most k vertices gives G^D isomorphic to G.
BS_0 = NSiso.  Rungs k = 3, 4 and the per-vertex key rung K0 (BSK) are compared.
"""
import itertools
import sys
from collections import Counter

import networkx as nx

import t1s_lib as L

n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
LIMIT = 20000


def graphs8():
    seen = set()
    for G in L.all_graphs(7):
        G = nx.convert_node_labels_to_integers(G)
        for k in range(8):
            for N in itertools.combinations(range(7), k):
                H = G.copy()
                H.add_node(7)
                H.add_edges_from((7, x) for x in N)
                cc = L.canon(H)
                if cc not in seen:
                    seen.add(cc)
                    yield H


def ind(G, k):
    """Counter of induced k-vertex subgraph invariants (edge count + sorted degrees: complete for k <= 4)."""
    c = Counter()
    for S in itertools.combinations(G.nodes(), k):
        sub = G.subgraph(S)
        c[tuple(sorted(d for _, d in sub.degree()))] += 1
    return c


def keys(G):
    return (nx.triangles(G), nx.triangles(nx.complement(G)))


c = Counter(); out3, out4, outk = [], [], []
for G in (graphs8() if n == 8 else L.all_graphs(n)):
    c["graphs"] += 1
    cG = L.canon(G)
    sets = L.balanced_sets(G, L.sw_pairs(G), limit=LIMIT)
    if len(sets) >= LIMIT:
        c["undecided"] += 1
        continue
    bad = [L.switch(G, D) for D in sets]
    bad = [H for H in bad if L.canon(H) != cG]
    c["BS_0 (NSiso)"] += (not bad)
    if not bad:
        c["BS_3"] += 1; c["BS_4"] += 1; c["BSK"] += 1
        continue
    i3 = ind(G, 3)
    b3 = [H for H in bad if ind(H, 3) == i3]
    c["BS_3"] += (not b3)
    if b3 and len(out3) < 8:
        out3.append(L.g6(G))
    i4 = ind(G, 4)
    b4 = [H for H in b3 if ind(H, 4) == i4]
    c["BS_4"] += (not b4)
    if b4 and len(out4) < 30:
        out4.append(L.g6(G))
    kG = keys(G)
    bk = [H for H in bad if keys(H) == kG]
    c["BSK"] += (not bk)
    if bk and len(outk) < 30:
        outk.append(L.g6(G))
print(n, dict(c))
print("outside BS_3 (first 8):", out3)
print("outside BS_4 (first 30):", out4)
print("outside BSK (first 30):", outk)
