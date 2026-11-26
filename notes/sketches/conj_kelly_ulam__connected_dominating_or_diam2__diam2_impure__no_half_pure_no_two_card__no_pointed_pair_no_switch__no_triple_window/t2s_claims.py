"""Single-graph forms of the lemmas of sketch t2 (structure of the remainder outside W3), for
  python3 tools/search/small_graphs.py counterexample --claim <this file> --n-min 3 --n-max 7 --random 60 --random-n 8 9
Evidence only.  No deck is presupposed, so nothing here is vacuous for small n.

For every ordered pair (u, v), S = V - {u, v}, F = G[S], every automorphism g of F and the twist
G_g (u re-attached to {x in S : u ~ g x}, plus v iff u ~ v), with
   eps_x = [u ~ g x] - [u ~ x],  k = #{x : eps_x = +1} = #{x : eps_x = -1},
   c = #{x in S : u ~ g x and v ~ x} - #{x in S : u ~ x and v ~ x}   (codegree change of the pair u, v):
  CD1  sum_S deg(x) eps_x = c - k
  CD2  (sum of squared degrees of G_g) - (sum of squared degrees of G) = 2 c
  CD3  hence  K-sq  <=>  K-cd  (twist trivial or c != 0)
  CD4  if g preserves G-degrees on S then c = k            (Lemma B is the case c = k = 0)
  CD5  w2 at u and at v:  w2_{G_g}(u) - w2_G(u) = c = w2_{G_g}(v) - w2_G(v)
  SL   G_g and G have the same pointed cards at the pair: (G_g - u, v) = (G - u, v) and
       (G_g - v, u) ~ (G - v, u)  (so a twist is an anchored graph; used for the dichotomy).
"""
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa


def w2(G, x):
    return sum(G.degree(y) for y in G[x])


def claim(G):
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    if n < 3:
        return True
    C = Census(G, triples=False)
    sq = sum(d * d for _, d in G.degree())
    for (u, v) in C.ty:
        S, A, Nu, Nv, Ku, Kv = C.pd(u, v)
        for g in A:
            e = eps_of(S, Nu, g)
            k = sum(1 for x in S if e[x] == 1)
            if k != sum(1 for x in S if e[x] == -1):
                return False
            c = codeg_change(S, Nu, Nv, g)
            if sum(G.degree(x) * e[x] for x in S) != c - k:
                return False
            H = twist_graph(G, u, v, S, Nu, g)
            if sum(d * d for _, d in H.degree()) - sq != 2 * c:
                return False
            if k_SQ(G, u, v, S, Nu, g) != k_CD(G, u, v, S, Nu, Nv, g):
                return False
            if k_DP(G, S, g) and c != k:
                return False
            if w2(H, u) - w2(G, u) != c or w2(H, v) - w2(G, v) != c:
                return False
            if canon_marked(H, (u,), (v,)) != C.c2[(u, v)] or canon_marked(H, (v,), (u,)) != C.c2[(v, u)]:
                return False
    return True
