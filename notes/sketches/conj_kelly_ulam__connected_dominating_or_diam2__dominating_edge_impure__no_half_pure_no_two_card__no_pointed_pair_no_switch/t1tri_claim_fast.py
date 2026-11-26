"""Faster exhaustive run of the relaxed claims S, G3, M of t1tri_claims.py (same statements, with a
degree-sequence prefilter before any isomorphism search), with a breakdown that shows where the
hypotheses do work.  Evidence only.

  python3 t1tri_claim_fast.py 7            exhaustive n = 7
  python3 t1tri_claim_fast.py 8 300        300 random graphs on 8 vertices
  python3 t1tri_claim_fast.py members      the three known residual members
"""
import itertools
import os
import random
import sys
import time
from collections import Counter

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import t1tri_lib as L  # noqa: E402
from small_graphs import all_graphs  # noqa: E402

C = Counter()


def run(G):
    """Returns False on a witness against S, G3 or M."""
    V = sorted(G.nodes())
    deg = dict(G.degree())
    adj = {x: set(G[x]) for x in V}
    cG = L.canon(G)
    carddeg = {x: sorted(deg[y] - (y in adj[x]) for y in V if y != x) for x in V}
    C["graphs"] += 1
    for T in itertools.combinations(V, 3):
        Ts = set(T)
        sr = {}
        for x in T:
            y, z = [t for t in T if t != x]
            sr[x] = (L.type_straight(G, x, y, z), L.card_swap(G, x, y, z))
        all_straight = all(a or b for a, b in sr.values())
        oi = {}
        for x in T:
            y, z = [t for t in T if t != x]
            oi[(x, y, z)] = L.orbit_intersection(G, x, y, z)
            oi[(x, z, y)] = L.orbit_intersection(G, x, z, y)
        oi_any = any(oi.values())
        C["triples"] += 1
        C["triples all_straight"] += all_straight
        C["triples oi_any"] += oi_any
        C["triples oi_all"] += all(oi.values())
        for u in T:
            v, w = [t for t in T if t != u]
            R, A, U, Vs, W = L.stab_data(G, u, v, w)
            m_wu = all(L.img(g, U) == U for g in A if L.img(g, W) == W)
            rest = [x for x in V if x != u]
            for k in range(len(rest) + 1):
                for Np in itertools.combinations(rest, k):
                    Nps = set(Np)
                    if Nps == adj[u]:
                        continue  # H = G: trivially matched, isomorphic
                    dH = {y: deg[y] - (y in adj[u]) + (y in Nps) for y in rest}
                    dH[u] = k
                    aH = {y: (adj[y] - {u}) | ({u} if y in Nps else set()) for y in rest}
                    aH[u] = Nps
                    H = None
                    for tau in ({v: v, w: w}, {v: w, w: v}):
                        ok = True
                        for x in (v, w):
                            tx = tau[x]
                            if sorted(dH[y] - (y in aH[tx]) for y in V if y != tx) != carddeg[x]:
                                ok = False
                                break
                        if not ok:
                            continue
                        if H is None:
                            H = nx.Graph()
                            H.add_nodes_from(V)
                            H.add_edges_from((a, b) for a in V for b in aH[a] if a < b)
                        Iv = isos_T(G, H, v, tau[v], Ts)
                        if not Iv:
                            continue
                        Iw = isos_T(G, H, w, tau[w], Ts)
                        if not Iw:
                            continue
                        crossed = tau[v] != v
                        iso = L.canon(H) == cG
                        C["matched (H != G)"] += 1
                        C["matched crossed"] += crossed
                        C["matched non-iso"] += (not iso)
                        if not iso:
                            C["non-iso, all_straight"] += all_straight
                            C["non-iso, oi_any"] += oi_any
                        if sr[u][0]:
                            C["S instances"] += 1
                            if crossed:
                                print("S fails at u", L.g6(G), T, u, Np)
                                return False
                        if sr[v][0]:
                            C["S instances"] += 1
                            if any(f[u] != u or f[w] != tau[w] for f in Iv):
                                print("S fails at v", L.g6(G), T, u, Np)
                                return False
                        if sr[w][0]:
                            C["S instances"] += 1
                            if any(f[u] != u or f[v] != tau[v] for f in Iw):
                                print("S fails at w", L.g6(G), T, u, Np)
                                return False
                        if all_straight and oi_any:
                            C["G3 instances"] += 1
                            if not iso:
                                print("G3 fails", L.g6(G), T, u, Np)
                                return False
                        full = (not crossed) and any(f[u] == u and f[w] == w for f in Iv) \
                            and any(f[u] == u and f[v] == v for f in Iw)
                        if full:
                            C["fully anchored (H != G)"] += 1
                            C["fully anchored non-iso"] += (not iso)
                            if oi[(u, v, w)]:
                                C["G3-anchored instances"] += 1
                                if not iso:
                                    print("G3 (anchored, OI at u) fails", L.g6(G), T, u, Np)
                                    return False
                            if m_wu:
                                # M says H = G; we skipped H = G above, so any hit is a witness
                                print("M fails", L.g6(G), T, u, Np)
                                return False
    return True


def isos_T(G, H, x, tx, T):
    A = G.subgraph([y for y in G if y != x]).copy()
    B = H.subgraph([y for y in H if y != tx]).copy()
    for y in A:
        A.nodes[y]["m"] = int(y in T)
    for y in B:
        B.nodes[y]["m"] = int(y in T)
    return list(GraphMatcher(A, B, node_match=lambda a, b: a["m"] == b["m"]).isomorphisms_iter())


if __name__ == "__main__":
    t0 = time.time()
    arg = sys.argv[1]
    if arg == "members":
        gs = [L.from_g6(s) for s in L.MEMBERS]
    else:
        n = int(arg)
        if len(sys.argv) > 2:
            rnd = random.Random(12)
            gs = []
            for _ in range(int(sys.argv[2])):
                p = rnd.choice([0.3, 0.4, 0.5, 0.6, 0.7])
                gs.append(nx.gnp_random_graph(n, p, seed=rnd.randrange(10 ** 9)))
        else:
            gs = all_graphs(n)
    ok = True
    for i, G in enumerate(gs):
        if not run(G):
            ok = False
            break
    print(arg, "NO WITNESS" if ok else "WITNESS", dict(C), round(time.time() - t0, 1), "s")
