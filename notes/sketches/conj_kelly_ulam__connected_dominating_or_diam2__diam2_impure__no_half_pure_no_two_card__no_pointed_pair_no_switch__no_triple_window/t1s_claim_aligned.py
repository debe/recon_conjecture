"""Labelled test of Theorem Sw (t1.md section 4), run as
    python3 t1s_claim_aligned.py 6
For every graph G on n vertices (one labelling per isomorphism class) and every labelled graph
H on the same vertex set:
  (two-card form)  if H - w ~ G - w, H - y ~ G - y, deg_H = deg_G at w and y, and the bit wy
                   differs, then {w, y} is in Sw(G);
  (aligned form)   if H - v ~ G - v for every v (an aligned pair, sigma = id), then the
                   difference set is contained in Sw(G) and in the three-card form Sw3(G), satisfies the
                   viewer clause, is
                   degree-balanced, and keeps the triangle keys (t, t-bar) of every vertex.
Not vacuous: aligned pairs with H != G exist (H = pi(G) for pi a transposition of two
removal-similar vertices that are not twins).
"""
import itertools
import sys
from collections import defaultdict

import networkx as nx

import t1s_lib as L

n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
V = list(range(n))
pairs = list(itertools.combinations(V, 2))

# all labelled graphs: card canon per vertex, degrees
lab = []
idx = defaultdict(list)       # (v, canon(H - v), deg_H v) -> list of indices
cache = {}


def card_canon(edges, v):
    key = (frozenset(e for e in edges if v not in e), v)
    sub = tuple(sorted(e for e in edges if v not in e))
    k = (sub, v)
    if k not in cache:
        H = nx.Graph()
        H.add_nodes_from(x for x in V if x != v)
        H.add_edges_from(sub)
        cache[k] = L.canon(H)
    return cache[k]


for mask in range(1 << len(pairs)):
    edges = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    cc = [card_canon(edges, v) for v in V]
    lab.append((mask, deg, cc))
    for v in V:
        idx[(v, cc[v], deg[v])].append(len(lab) - 1)

two_card = aligned = aligned_nontrivial = 0
for G in L.all_graphs(n):
    Gm = 0
    for i, (a, b) in enumerate(pairs):
        if G.has_edge(a, b):
            Gm |= 1 << i
    _, dG, cG = lab[Gm]
    Sw = L.sw_pairs(G)
    SwV = L.sw_pairs(G, viewer=True) & L.sw3_pairs(G)
    for pi, (w, y) in enumerate(pairs):
        A = set(idx[(w, cG[w], dG[w])])
        B = idx[(y, cG[y], dG[y])]
        for h in B:
            if h not in A:
                continue
            mask = lab[h][0]
            if (mask >> pi & 1) == (Gm >> pi & 1):
                continue
            two_card += 1
            if (w, y) not in Sw:
                print("WITNESS two-card", L.g6(G), w, y, bin(mask))
                sys.exit(0)
    # aligned pairs
    cand = set(idx[(0, cG[0], dG[0])])
    for v in V[1:]:
        cand &= set(idx[(v, cG[v], dG[v])])
    for h in cand:
        mask = lab[h][0]
        aligned += 1
        if mask == Gm:
            continue
        aligned_nontrivial += 1
        D = {pairs[i] for i in range(len(pairs)) if (mask ^ Gm) >> i & 1}
        if not D <= Sw or not D <= SwV:
            print("WITNESS aligned Sw", L.g6(G), bin(mask), sorted(D - SwV))
            sys.exit(0)
        bal = defaultdict(int)
        for (a, b) in D:
            s = 1 if G.has_edge(a, b) else -1
            bal[(a, dG[b])] += s
            bal[(b, dG[a])] += s
        if any(bal.values()):
            print("WITNESS aligned balance", L.g6(G), bin(mask))
            sys.exit(0)
        if n >= 4:   # K0: triangle keys are card-tied
            Hh = nx.Graph(); Hh.add_nodes_from(V)
            Hh.add_edges_from(pairs[i] for i in range(len(pairs)) if mask >> i & 1)
            if (nx.triangles(G) != nx.triangles(Hh)
                    or nx.triangles(nx.complement(G)) != nx.triangles(nx.complement(Hh))):
                print("WITNESS aligned K0", L.g6(G), bin(mask))
                sys.exit(0)
print(f"n={n}: NO WITNESS; two-card instances {two_card}, aligned pairs {aligned}, of which H != G: {aligned_nontrivial}")
