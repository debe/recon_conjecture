"""Transfer law for twists (single-graph identities), for
  python3 tools/search/small_graphs.py counterexample --claim <this file> --n-min 3 --n-max 7 --random 40 --random-n 8 9
Evidence only.

For every ordered pair (u, v), S = V - {u, v}, F = G[S], A = adjacency matrix of F,
n = indicator of N(u) in S, m = indicator of N(v) in S, g in Aut(F), n' = n o g (indicator of
g^{-1} N(u)), eps = n' - n, and the twist G_g:
   Delta_j = eps^T A^j m      (change of the number of walks u -> v of length j + 2 through F)
  TR1  Delta_0 = codegree change;  sum of squared degrees changes by 2 Delta_0        (as CD2)
  TR2  if Delta_0 = 0:  W3(G_g) - W3(G) = 2 Delta_1,   W3(X) = sum over ordered adjacent pairs of
       deg x deg y = number of walks of length 3
  TR3  charpoly(G_g) = charpoly(G)   <=>   Delta_j = 0 for all 0 <= j <= |S| - 1
  TR4  if g fixes N(v) (as a set) then Delta_j = 0 for all j  (and G_g is isomorphic to G)
"""
import os
import sys

import networkx as nx
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa


def W3(G):
    return sum(G.degree(x) * G.degree(y) for x in G for y in G[x])


def charpoly(G):
    """The power sums tr A^k, k = 1..n (exact integers); by Newton's identities two graphs on n
    vertices have the same characteristic polynomial iff these agree."""
    V = sorted(G)
    M = np.array([[1 if G.has_edge(a, b) else 0 for b in V] for a in V], dtype=object)
    P = M.copy()
    out = []
    for _ in range(len(V)):
        out.append(int(sum(P[i][i] for i in range(len(V)))))
        P = P.dot(M)
    return tuple(out)


def deltas(G, S, Nu, Nv, g):
    idx = {x: i for i, x in enumerate(S)}
    k = len(S)
    eps = [int(g[x] in Nu) - int(x in Nu) for x in S]
    vec = [int(x in Nv) for x in S]
    out = []
    for _ in range(k):
        out.append(sum(e * w for e, w in zip(eps, vec)))
        vec = [sum(vec[idx[y]] for y in G[x] if y in idx) for x in S]
    return out


def claim(G):
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    if n < 3:
        return True
    C = Census(G, triples=False)
    sq = sum(d * d for _, d in G.degree())
    w3 = W3(G)
    cp = charpoly(G)
    cG = canon(G)
    for (u, v) in C.ty:
        S, A, Nu, Nv, Ku, Kv = C.pd(u, v)
        for g in A:
            D = deltas(G, S, Nu, Nv, g)
            H = twist_graph(G, u, v, S, Nu, g)
            if D and D[0] != codeg_change(S, Nu, Nv, g):
                return False
            if D and sum(d * d for _, d in H.degree()) - sq != 2 * D[0]:
                return False
            if len(D) > 1 and D[0] == 0 and W3(H) - w3 != 2 * D[1]:
                return False
            if (charpoly(H) == cp) != (not any(D)):
                return False
            if frozenset(g[x] for x in Nv) == Nv and (any(D) or canon(H) != cG):
                return False
    return True
