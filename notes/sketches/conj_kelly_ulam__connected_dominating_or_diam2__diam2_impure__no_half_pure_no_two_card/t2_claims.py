"""Claims for sketch t2 (class N+: equitable two-degree graphs with a non-extending card
isomorphism into every vertex of one degree class). Evidence only, never a result.

  python3 tools/search/small_graphs.py counterexample \
      --claim notes/sketches/<step>/t2_claims.py --n-min 3 --n-max 7 --random 300 --random-n 8 9 10

All claims are *relaxed single-graph forms*: the family of graphs hypomorphic to G is replaced
by the larger family K_rel of graphs with the same parameters (d, p, q, b, e):
degrees in {d, d+1}, q vertices of degree d+1, and every vertex x has b + theta*chi(x)
neighbours of degree d+1. The paper argument uses a hypomorphic graph only through these
parameters, so every lemma must already hold in K_rel.

 Z   (eigen-relation, sketch Lemma Z): K1, K2 in K_rel agreeing off u, z = row difference at u,
     s = chi(u):  sum_{y ~_K1 x} z(y) = (theta - s) z(x) for x != u, and = k at u.
 V   (vanishing + rigidity, Lemmas V and A5): for two extensions K1, K2 != K of K at u,
     k2 z1 - k1 z2 vanishes at every vertex of the degree class of u that has an extension of
     its own; if such a vertex lies in supp z1, then k1 = k2.
 B3  two extensions K1 != K2 at a low vertex share no lost vertex x that has an extension of K1.
 S   (bilinear identities B1 of the sketch; pure algebra from Z and A = A^T): for extensions
     K at x and K' at x' != x of the same base G, with k, k' their numbers of lost vertices:
       deg x = deg x'      :  k * z_K'(x) = k' * z_K(x')
       x low, x' high      :  <z_K, z_K'> = k' * z_K(x') - k * z_K'(x)
 B4  Steps 1 and 2 of the sketch, on every instance where G has an extension at every vertex
     and some low vertex has two extensions with disjoint lost sets.
 B   (descent, Theorem N+ core): if every vertex of G has an extension, and every low vertex of
     every extension K of G at a low vertex has an extension of K, then some low vertex of G has
     at most one extension.  (In a counterexample every vertex of every hypomorphic graph has an
     extension, and under (H3) every low vertex has two: contradiction.)
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2_lib import equitable_two_degrees  # noqa: E402

STATS = {"graphs": 0, "equitable": 0, "with_ext": 0, "Z": 0, "S_same": 0, "S_mixed": 0, "V": 0,
         "B3_pairs": 0, "B3": 0, "B4_step1": 0, "B4_step2": 0, "B_hyp": 0}


def params(G):
    eq = equitable_two_degrees(G)
    if eq is None:
        return None
    d, b, e = eq
    q = sum(1 for _, x in G.degree() if x == d + 1)
    return d, b, e, q


def in_Krel(K, par):
    return params(K) == par


def extensions(K, u, par):
    """All K' != K in K_rel that agree with K off u, as (K', z, k) with z = [x~_K u] - [x~_K' u]."""
    out = []
    others = [x for x in K.nodes() if x != u]
    N = set(K[u])
    a = len(N)
    for S in itertools.combinations(others, a):
        S = set(S)
        if S == N:
            continue
        K2 = K.copy()
        K2.remove_edges_from([(u, w) for w in N])
        K2.add_edges_from((u, w) for w in S)
        if in_Krel(K2, par):
            z = {x: (1 if x in N else 0) - (1 if x in S else 0) for x in K.nodes()}
            out.append((K2, z, len(N - S)))
    return out


def check_Z(K, u, z, k, par):
    d, b, e, q = par
    theta = e - b
    s = 1 if K.degree(u) == d + 1 else 0
    for x in K.nodes():
        lhs = sum(z[y] for y in K[x])
        if x == u:
            if lhs != k:
                return False
        elif lhs != (theta - s) * z[x]:
            return False
    return True


def claim(G):
    STATS["graphs"] += 1
    par = params(G)
    if par is None:
        return True
    STATS["equitable"] += 1
    d, b, e, q = par
    deg = dict(G.degree())
    ext = {u: extensions(G, u, par) for u in G.nodes()}
    # Z
    for u, lst in ext.items():
        for (K2, z, k) in lst:
            STATS["Z"] += 1
            if not check_Z(G, u, z, k, par):
                return False
    if any(ext.values()):
        STATS["with_ext"] += 1
    # S
    for x, x2 in itertools.permutations(list(G.nodes()), 2):
        for (_, z, k) in ext[x]:
            for (_, z2, k2) in ext[x2]:
                if deg[x] == deg[x2]:
                    STATS["S_same"] += 1
                    if k * z2[x] != k2 * z[x2]:
                        return False
                elif deg[x] == d:
                    STATS["S_mixed"] += 1
                    if sum(z[y] * z2[y] for y in G.nodes()) != k2 * z[x2] - k * z2[x]:
                        return False
    every = all(ext[u] for u in G.nodes())
    # V at base G: y = k2 z1 - k1 z2 vanishes at every vertex of the class of u that has an
    # extension of its own (Lemma V); if such a vertex lies in supp z1, then k1 = k2.
    for u, lst in ext.items():
        cls = [x for x in G.nodes() if deg[x] == deg[u] and ext[x]]
        for (_, z1, k1), (_, z2, k2) in itertools.combinations(lst, 2):
            for x in cls:
                STATS["V"] += 1
                if k2 * z1[x] != k1 * z2[x]:
                    return False
                if z1[x] != 0 and k1 != k2:
                    return False
    # B3: two extensions K1 != K2 at a low vertex v cannot share a lost vertex x that has an
    # extension of K1 (x is low in K1).
    for v in G.nodes():
        if deg[v] != d:
            continue
        for (K1, z1, _), (K2, z2, _) in itertools.permutations(ext[v], 2):
            STATS["B3_pairs"] += 1
            for x in G.nodes():
                if z1[x] == 1 and z2[x] == 1:
                    STATS["B3"] += 1
                    if extensions(K1, x, par):
                        return False
    # B4, Steps 1 and 2, whenever their objects exist (needs an extension at every vertex, so
    # that kappa, R0, R1 are well defined and B2 applies).
    if every:
        for v in G.nodes():
            if deg[v] != d or len(ext[v]) < 2:
                continue
            for (K1, z1, k1), (K2, z2, k2) in itertools.permutations(ext[v], 2):
                S1 = {x for x in G.nodes() if z1[x] == 1}
                S2 = {x for x in G.nodes() if z2[x] == 1}
                if S1 & S2:
                    continue
                for w in S1:
                    for (_, zw, kw) in ext[w]:
                        STATS["B4_step1"] += 1
                        R1 = {x for x in G.nodes() if zw[x] == 1}
                        if not R1 <= (S1 - {w}):
                            return False
                        gamma = [x for x in G.nodes() if zw[x] == -1]
                        for v2 in gamma:
                            if len(ext[v2]) < 2:
                                continue
                            (_, m1, km1), (_, m2, km2) = ext[v2][0], ext[v2][1]
                            if {x for x in G.nodes() if m1[x] == 1} & {x for x in G.nodes() if m2[x] == 1}:
                                continue
                            STATS["B4_step2"] += 1
                            if km1 > kw - 1:
                                return False
    # B
    if every:
        low = [v for v in G.nodes() if deg[v] == d]
        ok = True
        for v in low:
            for (K, _, _) in ext[v]:
                for x in K.nodes():
                    if K.degree(x) == d and not extensions(K, x, par):
                        ok = False
                        break
                if not ok:
                    break
            if not ok:
                break
        if ok and low:
            STATS["B_hyp"] += 1
            if all(len(ext[v]) >= 2 for v in low):
                return False
    return True


import atexit  # noqa: E402

atexit.register(lambda: print("t2_claims stats:", STATS))
