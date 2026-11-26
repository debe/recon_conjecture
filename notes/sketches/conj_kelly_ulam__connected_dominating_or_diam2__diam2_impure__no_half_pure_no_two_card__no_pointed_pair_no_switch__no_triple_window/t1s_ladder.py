"""The ladder NS < NSiso < NSiso+K0 < ... (evidence only): python3 t1s_ladder.py 7
A graph is in a rung if every nonempty degree-balanced D inside the rung's pair set that passes
the rung's filter gives G^D isomorphic to G.
  NS        : no D at all (pair set Sw)
  NSiso     : pair set Sw, no filter
  NS3iso    : pair set Sw3, no filter
  K0        : pair set Sw3, filter: triangles and independent triples through every vertex agree
  ports     : pair set Sw3, filter K0 and: the multiset of types of two-deleted subgraphs agrees
  K0 on Sw  : pair set Sw (two-card form), filter K0
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


def keys(G):
    t = nx.triangles(G)
    tb = nx.triangles(nx.complement(G))
    return {v: (t[v], tb[v]) for v in G.nodes()}


def ports(G):
    return sorted(L.port_canon(G).values())


c = Counter()
left = []
for G in (graphs8() if n == 8 else L.all_graphs(n)):
    c["graphs"] += 1
    cG = L.canon(G)
    S = L.sw_pairs(G)
    sets = L.balanced_sets(G, S, limit=LIMIT)
    if len(sets) >= LIMIT:
        c["undecided"] += 1
        continue
    c["NS"] += (not sets)
    bad = [D for D in sets if L.canon(L.switch(G, D)) != cG]
    c["NSiso"] += (not bad)
    if not bad:
        c["NS3iso"] += 1; c["K0"] += 1; c["ports"] += 1; c["K0 on Sw"] += 1
        continue
    S3 = L.sw3_pairs(G)
    bad3 = [D for D in bad if D <= S3]
    c["NS3iso"] += (not bad3)
    kG = keys(G)
    c["K0 on Sw"] += (not [D for D in bad if keys(L.switch(G, D)) == kG])
    badk = [D for D in bad3 if keys(L.switch(G, D)) == kG]
    c["K0"] += (not badk)
    pG = ports(G)
    badp = [D for D in badk if ports(L.switch(G, D)) == pG]
    c["ports"] += (not badp)
    if badp:
        left.append(L.g6(G))
print(n, dict(c))
print("outside the last rung:", left[:20], len(left))
