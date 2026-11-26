"""Pair-level diagnostics on the residual members: why T+ fails at each pointed pair.
Columns: pair, alpha, deg, copies of F (unordered), |A|, |C|, |R|, (i), (ii), (iii), |Aut F|,
number of non-trivial admissible twists (twisted graph has the degree sequence of G and is not
isomorphic to G)."""
import sys
from collections import Counter, defaultdict
from t3o_lib import *


def pair_data(G, u, v):
    S = [x for x in sorted(G.nodes()) if x not in (u, v)]
    A = auts(G, S)
    return S, A, frozenset(set(G[u]) - {v}), frozenset(set(G[v]) - {u})


for s in sys.argv[1:]:
    G = from_g6(s)
    V = sorted(G.nodes())
    cid = pointed_classes(G, 2)
    members = defaultdict(list)
    for p, i in cid.items():
        members[i].append(p)
    ty = {}
    for p in cid:
        ty[p] = ctype(G, p)
    tsize = Counter(ty.values())
    cG = canon(G)
    dseq = sorted(d for _, d in G.degree())
    print("==", s)
    stats = Counter()
    for (u, v) in sorted(cid):
        alpha = int(G.has_edge(u, v))
        ci = G.degree(u) - G.degree(v) not in (-alpha, 1 - alpha)
        A = members[cid[(u, v)]]
        chat = {cid[(y, x)] for (x, y) in A}
        C = sum(len(members[j]) for j in chat)
        R = tsize[ty[(u, v)]] - len(A) - C
        cii = R < len(A)
        S, Au, Nu, Nv = pair_data(G, u, v)
        ciii = True
        for (x, y) in A:
            S2, A2, _, _ = pair_data(G, x, y)
            if not all(G.degree(g[z]) == G.degree(z) for g in A2 for z in S2):
                ciii = False
        # twists at (u, v): u re-attached to g(Nu), bit free
        surv = set()
        for g in Au:
            newN = frozenset(g[x] for x in Nu)
            for beta in (0, 1):
                K = twist_graph(G, u, newN, S)
                if K.has_edge(u, v):
                    K.remove_edge(u, v)
                if beta:
                    K.add_edge(u, v)
                if sorted(d for _, d in K.degree()) != dseq:
                    continue
                cK = canon(K)
                if cK != cG:
                    surv.add(cK)
        stats[(ci, cii, ciii)] += 1
        if "-v" in sys.argv or (ci and cii):
            print("  ", (u, v), "a", alpha, "deg", G.degree(u), G.degree(v), "copies",
                  tsize[ty[(u, v)]] // 2, "|A|", len(A), "|C|", C, "|R|", R,
                  "(i)", ci, "(ii)", cii, "(iii)", ciii, "|AutF|", len(Au),
                  "surviving non-iso twists", len(surv))
    print("   (i),(ii),(iii) histogram:", sorted(stats.items()))
