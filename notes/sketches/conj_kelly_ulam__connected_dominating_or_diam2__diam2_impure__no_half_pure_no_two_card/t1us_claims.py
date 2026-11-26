"""Claims behind sketch t1 (class US, unique switch). Evidence only; used to try to kill lemmas.

  python3 tools/search/small_graphs.py counterexample --claim <this file> --n-min 3 --n-max 7

claim(G) checks, for every graph G:
  W1  (single-graph identity behind "w2 is card-tied"):
        sum of squared degrees of the card G - x  =  Q(G) - deg(x)^2 - 2 w2(x) + deg(x).
  REL (switch relation). If G is two-walk (a,b)-linear, u a vertex and S a subset of V - u with
      |S| = deg u such that G_S (= G - u with u re-attached to S) is two-walk (a,b)-linear, then
      z = 1_N(u) - 1_S satisfies  sum_{y ~ x} z(y) = (a - deg u) z(x)  for all x != u  and
      sum_{y ~ u} z(y) = |N(u) minus S|.
  U   (unique switch). If moreover A_G - (a - deg u) is nonsingular, there is at most one such
      S != N(u).
  US  (the class, strong single-card form). If moreover some automorphism of G - u moves N(u),
      or some isomorphism G - u'' -> G - u does not map N(u'') onto N(u), then every such S
      gives a graph isomorphic to G.
"""
import itertools
import os
import sys
from fractions import Fraction

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1us_lib import two_walk_linear, w2, canon, _kernel  # noqa: E402


def nonsingular(G, lam):
    nodes = sorted(G.nodes())
    idx = {x: i for i, x in enumerate(nodes)}
    n = len(nodes)
    M = [[Fraction(0)] * n for _ in range(n)]
    for x in nodes:
        M[idx[x]][idx[x]] -= lam
        for y in G[x]:
            M[idx[x]][idx[y]] += 1
    return not _kernel(M, n)[0]


def moving_card_iso(G, u):
    """some u'' and iso G - u'' -> G - u that does not map N(u'') onto N(u)."""
    Cu = G.copy()
    Cu.remove_node(u)
    Nu = set(G[u])
    for w in G:
        if G.degree(w) != G.degree(u):
            continue
        Cw = G.copy()
        Cw.remove_node(w)
        for m in GraphMatcher(Cw, Cu).isomorphisms_iter():
            if {m[x] for x in G[w]} != Nu:
                return True
    return False


def claim(G):
    n = G.number_of_nodes()
    deg = dict(G.degree())
    w = w2(G)
    Q = sum(d * d for d in deg.values())
    for x in G:
        N = set(G[x])
        q = sum((deg[y] - (1 if y in N else 0)) ** 2 for y in G if y != x)
        if q != Q - deg[x] ** 2 - 2 * w[x] + deg[x]:
            return False
    ab = two_walk_linear(G)
    if ab is None:
        return True
    a, b = ab
    cg = canon(G)
    for u in G:
        N = frozenset(G[u])
        others = [x for x in G if x != u]
        base = G.copy()
        base.remove_node(u)
        lam = a - deg[u]
        alts = []
        for S in itertools.combinations(others, len(N)):
            S = frozenset(S)
            if S == N:
                continue
            H = base.copy()
            H.add_node(u)
            H.add_edges_from((u, s) for s in S)
            if two_walk_linear(H) != (a, b):
                continue
            z = {x: (1 if x in N else 0) - (1 if x in S else 0) for x in others}
            z[u] = 0
            for x in others:
                if sum(z[y] for y in G[x]) != lam * z[x]:
                    return False
            if sum(z[y] for y in G[u]) != len(N - S):
                return False
            alts.append(H)
        if nonsingular(G, lam):
            if len(alts) > 1:
                return False
            if alts and moving_card_iso(G, u):
                if canon(nx.convert_node_labels_to_integers(alts[0])) != cg:
                    return False
    return True
