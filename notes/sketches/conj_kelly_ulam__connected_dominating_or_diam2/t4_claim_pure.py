"""Lemma P of sketch t4, strong single-card form (non-vacuous: no deck is presupposed).

Let a be a pure degree of G: for every graph F on n - 2 vertices, the ordered pairs (x, y)
with deg x = a and G - x - y isomorphic to F are all adjacent or all non-adjacent.
Let u have degree a. Claim: every graph H' obtained from the card G - u by adding a new
vertex of degree a, with the degree sequence of G and the pair table pi of G
(pi_j(F) for every degree j and type F), has the new vertex attached to exactly N_G(u).

These are the only facts about H that the paper argument uses.
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import pair_table, pure_degrees, degseq  # noqa: E402


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    pi, e = pair_table(G)
    pure = set(pure_degrees(G, pi, e))
    if not pure:
        return True
    deg = dict(G.degree())
    target = degseq(G)
    for u in G.nodes():
        if deg[u] not in pure:
            continue
        N = frozenset(G[u])
        others = [w for w in G.nodes() if w != u]
        base = G.copy()
        base.remove_node(u)
        for S in itertools.combinations(others, deg[u]):
            if frozenset(S) == N:
                continue
            H = base.copy()
            H.add_node(u)
            H.add_edges_from((u, s) for s in S)
            if degseq(H) != target:
                continue
            pi_h, _ = pair_table(H)
            if pi_h == pi:
                return False
    return True
