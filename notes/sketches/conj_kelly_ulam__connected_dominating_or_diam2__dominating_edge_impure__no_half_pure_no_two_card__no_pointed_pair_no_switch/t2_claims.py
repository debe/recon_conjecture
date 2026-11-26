"""Single-graph forms of the lemmas of sketch t2 (triple pointed census), for
  python3 tools/search/small_graphs.py counterexample --claim <this file> --n-min 3 --n-max 7 --random 60 --random-n 8 9
Evidence only. None of the claims presupposes a deck, so none is vacuous for small n.

For every ordered pair (u, v), S = V - {u, v}, every automorphism g of F = G[S], and the twist
G_g (u re-attached to {x in S : u ~ g x}, plus v if u ~ v):
  A  (twists are anchored)  for every w in S with g(w) = w:
       (G_g - u; v, w) = (G - u; v, w)   and   (G_g - v; u, w) ~ (G - v; u, w)   as doubly pointed cards.
  B  (degree formula)  deg_{G_g} x = deg x + [u ~ g x] - [u ~ x] on S; deg u, deg v unchanged.
  C  (kill)  if  [g preserves N(u) on S]  or  [g preserves G-degrees on S]  or
       [MW: sum of deg x over {x in S : u ~ g x}  >=  sum of deg x over N(u) cap S],
       and G_g has the sum of squared degrees of G, then G_g = G (same edge set).
  D  (the triple census implies the pair census)  every doubly pointed class passing the triple
       window census projects to a pointed pair class passing the pair window census.
"""
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2_lib import *  # noqa


def claim(G):
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    if n < 3:
        return True
    C = Census(G)
    sq = sum(d * d for _, d in G.degree())
    for (u, v) in C.ty:
        S, A, Nu, Nv, Ku, Kv = C.pd(u, v)
        for g in A:
            H = twist_graph(G, u, v, S, Nu, g)
            # B
            if H.degree(u) != G.degree(u) or H.degree(v) != G.degree(v):
                return False
            if any(H.degree(x) != G.degree(x) + int(g[x] in Nu) - int(x in Nu) for x in S):
                return False
            # A
            for w in S:
                if g[w] != w:
                    continue
                if canon_marked(H, (u,), (v, w)) != C.c3[(u, v, w)]:
                    return False
                if canon_marked(H, (v,), (u, w)) != C.c3[(v, u, w)]:
                    return False
            # C
            triv = k_trivial(G, u, v, S, Nu, g)
            dp = k_DP(G, S, g)
            mw = sum(G.degree(x) for x in S if g[x] in Nu) >= sum(G.degree(x) for x in Nu)
            if (triv or dp or mw) and sum(d * d for _, d in H.degree()) == sq:
                if set(map(frozenset, H.edges())) != set(map(frozenset, G.edges())):
                    return False
    # D
    pw = {C.c2[Acl[0]] for _, Acl in pair_census_w(G, C)}
    for _, Acl in triple_census_w(G, C):
        (u, v, w) = Acl[0]
        if C.c2[(u, v)] not in pw:
            return False
    return True
