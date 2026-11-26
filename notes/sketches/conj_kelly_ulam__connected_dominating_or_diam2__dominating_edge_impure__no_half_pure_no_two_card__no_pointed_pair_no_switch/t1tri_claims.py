"""Claim file for sketch t1 (three-card gluing).  Evidence only, never a result.

  python3 tools/search/small_graphs.py counterexample --claim <this file> --n-min 4 --n-max 6

Relaxed, single-graph forms of the two paper lemmas (no deck is presupposed, so the test is
not vacuous below n = 14).  For a graph G, a triple T = {u, v, w} and every graph H that agrees
with G off u (H = G - u with u re-attached to an arbitrary set N'; this is the normalization
f_u = id, sigma u = u), call H *triple-matched* by tau (tau = id or the swap of v, w) if there are
isomorphisms f_v : G - v -> H - tau v and f_w : G - w -> H - tau w mapping T minus the deleted
vertex onto T minus the deleted vertex.  (This is what the unique-copy census gives for a
hypomorphic H.)

  S   (straightness): if G - x - y is not isomorphic to G - x - z, then f_x(y) = tau y for every
      such f_x (for x = u: tau = id).
  G3  (three-card gluing): if every x in T is straight-by-type or has a card automorphism
      swapping the other two, and (OI) holds at some role assignment, then H is isomorphic to G.
  M   (containment form): if H is fully anchored (tau = id, f_v fixes u and w, f_w fixes u and v)
      and every automorphism of K = G - T preserving the trace of N(w) preserves the trace of
      N(u), then H = G as labelled graphs.
"""
import itertools
import os
import sys

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import t1tri_lib as L  # noqa: E402

STATS = {"graphs": 0, "matched": 0, "matched_noniso": 0, "S_inst": 0, "G3_inst": 0, "M_inst": 0,
         "crossed": 0}


def isos_T(G, H, x, tx, T):
    """Isomorphisms G - x -> H - tx mapping T - x onto T - tx (as sets)."""
    A = G.subgraph([y for y in G if y != x]).copy()
    B = H.subgraph([y for y in H if y != tx]).copy()
    if sorted(d for _, d in A.degree()) != sorted(d for _, d in B.degree()):
        return []
    for y in A:
        A.nodes[y]["m"] = int(y in T)
    for y in B:
        B.nodes[y]["m"] = int(y in T)
    return list(GraphMatcher(A, B, node_match=lambda a, b: a["m"] == b["m"]).isomorphisms_iter())


def claim(G):
    n = G.number_of_nodes()
    if n < 4:
        return True
    STATS["graphs"] += 1
    V = sorted(G.nodes())
    cG = L.canon(G)
    for T in itertools.combinations(V, 3):
        sr = {}
        for x in T:
            y, z = [t for t in T if t != x]
            sr[x] = (L.type_straight(G, x, y, z), L.card_swap(G, x, y, z))
        all_straight = all(a or b for a, b in sr.values())
        oi_any = any(L.orbit_intersection(G, x, *[t for t in T if t != x]) or
                     L.orbit_intersection(G, x, *[t for t in T if t != x][::-1]) for x in T)
        for u in T:
            v, w = [t for t in T if t != u]
            R, A, U, Vs, W = L.stab_data(G, u, v, w)
            m_wu = all(L.img(g, U) == U for g in A if L.img(g, W) == W)
            rest = [x for x in V if x != u]
            Gu = G.subgraph(rest)
            for k in range(len(rest) + 1):
                for Np in itertools.combinations(rest, k):
                    H = nx.Graph(Gu)
                    H.add_node(u)
                    H.add_edges_from((u, y) for y in Np)
                    for tau in ({v: v, w: w}, {v: w, w: v}):
                        Iv = isos_T(G, H, v, tau[v], set(T))
                        if not Iv:
                            continue
                        Iw = isos_T(G, H, w, tau[w], set(T))
                        if not Iw:
                            continue
                        STATS["matched"] += 1
                        crossed = tau[v] != v
                        if crossed:
                            STATS["crossed"] += 1
                        iso = L.canon(H) == cG
                        if not iso:
                            STATS["matched_noniso"] += 1
                        # S at u
                        if sr[u][0]:
                            STATS["S_inst"] += 1
                            if crossed:
                                print("S fails at u", L.g6(G), T, u, Np)
                                return False
                        if sr[v][0]:
                            STATS["S_inst"] += 1
                            if any(f[u] != u or f[w] != tau[w] for f in Iv):
                                print("S fails at v", L.g6(G), T, u, Np)
                                return False
                        if sr[w][0]:
                            STATS["S_inst"] += 1
                            if any(f[u] != u or f[v] != tau[v] for f in Iw):
                                print("S fails at w", L.g6(G), T, u, Np)
                                return False
                        if all_straight and oi_any:
                            STATS["G3_inst"] += 1
                            if not iso:
                                print("G3 fails", L.g6(G), T, u, Np)
                                return False
                        if (not crossed) and m_wu and any(f[u] == u and f[w] == w for f in Iv) \
                                and any(f[u] == u and f[v] == v for f in Iw):
                            STATS["M_inst"] += 1
                            if set(Np) != set(G[u]):
                                print("M fails", L.g6(G), T, u, Np)
                                return False
    return True


if __name__ == "__main__":
    import time
    from small_graphs import all_graphs
    for n in [int(a) for a in sys.argv[1:]] or [4, 5, 6]:
        t0 = time.time()
        for k in STATS:
            STATS[k] = 0
        ok = all(claim(G) for G in all_graphs(n))
        print(n, "ok" if ok else "WITNESS", dict(STATS), round(time.time() - t0, 1), "s", flush=True)
