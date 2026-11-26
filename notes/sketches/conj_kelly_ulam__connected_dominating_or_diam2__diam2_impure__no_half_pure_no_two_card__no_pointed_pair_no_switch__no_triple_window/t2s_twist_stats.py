"""Which twists survive which kill?  Exhaustive small n.  Evidence only.
Over all graphs G on n vertices, ordered pairs (u, v), g in Aut(G-u-v) with G_g NOT isomorphic to G
(counted as distinct triples (G, (u, v), neighbourhood g^{-1}N(u))):
   total / Delta_0 = 0 (same sum of squares) / same degree multiset / + Delta_1 = 0 /
   + all Delta_j = 0 (same characteristic polynomial) / + same (deg, w2) multiset / same deck (must be 0)
  python3 t2s_twist_stats.py 7
  python3 t2s_twist_stats.py 8 8 [MOD RES]
"""
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa
from t2s_claim_transfer import deltas  # noqa
from t2_lib import deck  # noqa


def kw(G):
    return sorted((G.degree(x), sum(G.degree(y) for y in G[x])) for x in G)


MOD = int(sys.argv[3]) if len(sys.argv) > 3 else 1   # optional: only graphs with index = RES mod MOD
RES = int(sys.argv[4]) if len(sys.argv) > 4 else 0   # (to run n = 8 in parallel; add the counters)
for n in range(int(sys.argv[2]) if len(sys.argv) > 2 else 5, int(sys.argv[1]) + 1):
    c = Counter()
    for gi, G in enumerate(graphs_n(n)):
        if gi % MOD != RES:
            continue
        C = Census(G, triples=False)
        cG = canon(G)
        ds = degseq(G)
        kG = kw(G)
        for (u, v) in C.ty:
            S, A, Nu, Nv, Ku, Kv = C.pd(u, v)
            seen = set()
            for g in A:
                Np = frozenset(x for x in S if g[x] in Nu)
                if Np in seen or Np == Nu:
                    continue
                seen.add(Np)
                H = twist_graph(G, u, v, S, Nu, g)
                if canon(H) == cG:
                    c["twists isomorphic to G (N' != N)"] += 1
                    continue
                c["non-isomorphic twists"] += 1
                D = deltas(G, S, Nu, Nv, g)
                if D[0] == 0 and D[1] == 0:
                    c["Delta_0 = Delta_1 = 0 (any degree multiset)"] += 1
                if not any(D):
                    c["all Delta_j = 0 (same characteristic polynomial)"] += 1
                if D[0] != 0:
                    continue
                c["Delta_0 = 0"] += 1
                if degseq(H) != ds:
                    continue
                c["same degree multiset"] += 1
                if D[1] == 0:
                    c["same degree multiset, Delta_1 = 0"] += 1
                    if kw(H) == kG:
                        c["same degree multiset, Delta_1 = 0, same (deg, w2) multiset"] += 1
                if not any(D):
                    c["same degree multiset, all Delta_j = 0"] += 1
                    if kw(H) == kG:
                        c["same degree multiset, all Delta_j = 0, same (deg, w2) multiset"] += 1
                if kw(H) == kG:
                    c["same (deg, w2) multiset"] += 1
                if deck(H) == deck(G):
                    c["SAME DECK (impossible for n <= 13)"] += 1
    print("n =", n, dict(c), flush=True)
