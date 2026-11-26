"""Claim file for tools/search/small_graphs.py counterexample.

Triple twist lemma (sketch t3, section 3), single-graph form, both directions.
For every graph G, every ordered triple (u, v, w) and every set N' in S = V - {u, v, w} with
|N'| = |N(u) & S|, let G' be G with u re-attached to N' inside S (adjacency to v, w kept).
CLAIM: G' is 3-anchored to G at (u, v, w) -> (u, v, w), i.e. there are isomorphisms
(G - v; u, w) -> (G' - v; u, w) and (G - w; u, v) -> (G' - w; u, v)   [G - u = G' - u],
IFF N' = g2(Nu) = g3(Nu) for automorphisms g2, g3 of F = G[S] with g2(Nw) = Nw, g3(Nv) = Nv.
Also: if N' = h(Nu) with h(Nv) = Nv and h(Nw) = Nw, then G' is isomorphic to G.
Evidence only.
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3o_lib import (auts, canon, img, pointed_isos, triangles, trivial_images, triple_data,
                     twist_graph)


def claim(G):
    V = sorted(G.nodes())
    if len(V) < 4:
        return True
    cG = canon(G)
    for u, v, w in itertools.permutations(V, 3):
        if v > w:
            continue
        S, A, Nu, Nv, Nw = triple_data(G, u, v, w)
        tri = triangles(A, Nu, Nv, Nw)
        triv = trivial_images(A, Nu, Nv, Nw)
        for Np in itertools.combinations(S, len(Nu)):
            Np = frozenset(Np)
            K = twist_graph(G, u, Np, S)
            anchored = (pointed_isos(G, (v, u, w), K, (v, u, w), first_only=True)
                        and pointed_isos(G, (w, u, v), K, (w, u, v), first_only=True))
            if anchored != (Np in tri):
                return False
            if Np in triv and canon(K) != cG:
                return False
    return True
