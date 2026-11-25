"""Lemmas A1-A3 and the double-coset gluing lemma of sketch t4, strong two-card form
(non-vacuous: no deck is presupposed).

Let (u, v) be an anchored pair of G, F = G - u - v, S = V - {u, v}, N_x = N(x) minus {u, v}.
Let H' be obtained from the card G - u by adding a new vertex u' of degree deg u, such that
  * H' has the degree sequence of G,
  * some vertex z != u' of H' has degree deg v and H' - z is isomorphic to G - v,
  * (anchor A1: G - u - v has a unique induced copy)       H' has exactly one induced copy of F,
  * (anchor A2: degree-typed uniqueness)                   H' has the pair table pi of G,
  * (anchor A3: every other vertex has degree >= 2 away from deg u and from deg v)  nothing more.
Claims:
  (twist)  the new neighbourhood is g(N_u) (plus v iff u ~ v) for some automorphism g of F;
  (glue)   if Aut(F) = Stab(N_u) Stab(N_v), then H' is isomorphic to G.

These are exactly the facts about H that the paper argument uses.
"""
import itertools
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import (pair_table, degseq, ctype, automorphisms, factorizes, gap_anchored_pairs,
                    typed_anchored_pairs, unique_copy_pairs)  # noqa: E402


def check(G, u, v, kind, pi):
    deg = dict(G.degree())
    target = degseq(G)
    S = [x for x in G.nodes() if x not in (u, v)]
    Nu = frozenset(set(G[u]) - {v})
    adj_uv = G.has_edge(u, v)
    orbit = None
    fact = None
    others = [w for w in G.nodes() if w != u]
    base = G.copy()
    base.remove_node(u)
    card_v = ctype(G, (v,))
    F = ctype(G, (u, v))
    for T in itertools.combinations(others, deg[u]):
        if frozenset(T) == frozenset(G[u]):
            continue
        H = base.copy()
        H.add_node(u)
        H.add_edges_from((u, t) for t in T)
        if degseq(H) != target:
            continue
        if not any(z != u and H.degree(z) == deg[v] and ctype(H, (z,)) == card_v
                   for z in H.nodes()):
            continue
        if kind == "A1":
            copies = sum(1 for x, y in itertools.combinations(sorted(H.nodes()), 2)
                         if ctype(H, (x, y)) == F)
            if copies != 1:
                continue
        elif kind == "A2":
            if pair_table(H)[0] != pi:
                continue
        # H' passes every hypothesis the paper argument uses
        if orbit is None:
            A = automorphisms(G, S)
            orbit = {frozenset(g[x] for x in Nu) for g in A}
            fact = factorizes(G, u, v)[0]
        if (v in T) != adj_uv:
            return False
        if frozenset(T) - {v} not in orbit:
            return False
        if fact and not nx.is_isomorphic(G, H):
            return False
    return True


def claim(G):
    n = G.number_of_nodes()
    if n < 4:
        return True
    pi, e = pair_table(G)
    for kind, pairs in (("A1", unique_copy_pairs(G)), ("A2", typed_anchored_pairs(G, pi, e)),
                        ("A3", gap_anchored_pairs(G))):
        for (u, v) in pairs:
            if not check(G, u, v, kind, pi) or not check(G, v, u, kind, pi):
                return False
    return True
