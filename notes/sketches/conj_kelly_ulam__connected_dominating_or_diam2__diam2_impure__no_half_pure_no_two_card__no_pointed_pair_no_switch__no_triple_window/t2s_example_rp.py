"""The first re-paired phantom found: G = H@~~ibT (n = 9), K = HO~}ibt.  Evidence only.
Prints, for the two-deleted type F with a re-paired slice: the ordered pairs of type F in G and in K,
their pointed types (numbered), degrees and adjacency, and the swap pairing of types in both graphs.
Also re-checks: K not isomorphic to G, same (deg, w2) keys, same slice, no anchored pair, and
whether G passes the W2 / W3 window census at some class over F.
  python3 t2s_example_rp.py ['<G graph6>' '<K graph6>']
"""
import os
import sys
from collections import Counter, defaultdict

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa
from t2s_hunt import keys  # noqa

gs = sys.argv[1] if len(sys.argv) > 2 else "H@~~ibT"
ks = sys.argv[2] if len(sys.argv) > 2 else "HO~}ibt"
G = nx.convert_node_labels_to_integers(from_g6(gs))
K = nx.convert_node_labels_to_integers(from_g6(ks))
C, CK = Census(G, triples=True), Census(K, triples=False)
sl, slK = slices(G, C), slices(K, CK)
print("isomorphic:", canon(G) == canon(K), "| keys equal:", keys(G) == keys(K), "| degrees", degseq(G))
names = {}
for F, cnt in sl.items():
    if slK.get(F) != cnt:
        continue
    pairsG = sorted(p for p, t in C.ty.items() if t == F)
    pairsK = sorted(p for p, t in CK.ty.items() if t == F)
    swapG = {(C.c2[p], C.c2[(p[1], p[0])]) for p in pairsG}
    anch = [p for p in pairsK if (CK.c2[p], CK.c2[(p[1], p[0])]) in swapG]
    print("--- shared slice: F has", len(pairsG) // 2, "copies in G;", "TWISTED" if anch else "RE-PAIRED")
    if anch:
        continue
    for p in pairsG + pairsK:
        t = (C if p in pairsG and (p in C.c2) and False else None)
    def nm(t):
        if t not in names:
            names[t] = "t%d" % (len(names) + 1)
        return names[t]
    for label, X, CX, pairs in (("G", G, C, pairsG), ("K", K, CK, pairsK)):
        for (x, y) in pairs:
            print("   %s: pair (%d, %d)  type %s  deg x = %d, deg y = %d, %s   swap type %s" % (
                label, x, y, nm(CX.c2[(x, y)]), X.degree(x), X.degree(y),
                "adjacent" if X.has_edge(x, y) else "non-adjacent", nm(CX.c2[(y, x)])))
    pw = [Acl for r, Acl in pair_census_w(G, C) if C.ty[Acl[0]] == F]
    tw = [Acl for r, Acl in triple_census_w(G, C) if C.ty[(Acl[0][0], Acl[0][1])] == F]
    print("   pointed classes over F passing the pair window census in G:", len(pw),
          "| doubly pointed classes over F passing the triple window census:", len(tw))
    print("   |Aut(F)| =", len(C.pd(*pairsG[0])[1]))

# the card of the common vertex of the two copies: is the exchange a card automorphism?
if gs == "H@~~ibT":
    u, a, b = 5, 2, 7
    card = [x for x in G if x != u]
    A = auts(G, card)
    sw = [g for g in A if g[a] == b]
    print("card G-%d: |Aut| = %d; automorphisms mapping %d to %d: %d" % (u, len(A), a, b, len(sw)))
    N = set(G[u])
    hits = 0
    for g in A:
        H = G.copy()
        H.remove_edges_from([(u, t) for t in N])
        H.add_edges_from((u, g[t]) for t in N)
        if canon(H) == canon(K):
            hits += 1
    print("card automorphisms g with G[%d -> g N(%d)] isomorphic to K: %d" % (u, u, hits))
    print("|Aut G| =", len(auts(G)), " |Aut K| =", len(auts(K)))
