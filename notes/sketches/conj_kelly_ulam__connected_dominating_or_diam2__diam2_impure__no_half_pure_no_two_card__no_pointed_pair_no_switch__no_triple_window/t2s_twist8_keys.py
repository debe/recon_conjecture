"""Cross-check at n = 8: the non-isomorphic twists G_g with the (deg, w2) keys of G versus slices.
t2s_twist_stats.py counts 60 such twists; t2s_phantoms.py says no weak phantom on 8 vertices has
the keys.  So each of the 60 must change the slice over F = G-u-v.  This script lists them with
the number of copies of F before and after.  Evidence only.   python3 -u t2s_twist8_keys.py [MOD RES]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa
from t2s_hunt import keys  # noqa

MOD = int(sys.argv[1]) if len(sys.argv) > 1 else 1   # optional: graphs with index = RES mod MOD
RES = int(sys.argv[2]) if len(sys.argv) > 2 else 0
found = same = 0
for gi, G in enumerate(graphs_n(8)):
    if gi % MOD != RES:
        continue
    kG, cG, ds = keys(G), canon(G), degseq(G)
    C = Census(G, triples=False)
    slG = None
    for (u, v) in C.ty:
        S, A, Nu, Nv, _, _ = C.pd(u, v)
        seen = set()
        for g in A:
            Np = frozenset(x for x in S if g[x] in Nu)
            if Np in seen or Np == Nu:
                continue
            seen.add(Np)
            H = twist_graph(G, u, v, S, Nu, g)
            if degseq(H) != ds or keys(H) != kG or canon(H) == cG:
                continue
            slG = slG or slices(G, C)
            slH = slices(H)
            F = C.ty[(u, v)]
            eq = slH.get(F) == slG[F]
            found += 1
            same += eq
            print(g6(G), (u, v), "twist", g6(H), "| slice over F equal:", eq,
                  "| copies of F in G:", sum(slG[F].values()) // 2, "in the twist:", sum(slH.get(F, {}).values()) // 2,
                  "| pointed types over F in G:", len(slG[F]), "in the twist:", len(slH.get(F, {})), flush=True)
print("TOTAL key-preserving non-isomorphic twists:", found, "| with the slice of G over F:", same)
