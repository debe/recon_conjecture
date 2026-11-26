"""Single-graph forms of the intermediate lemmas of Zinchenko, arXiv:2611.13728v1.

Evidence only, never a result. These are private checks used to locate a broken step in the
audit `debe_zinchenko.md`; they say nothing about the theorem for all n.

  python3 tools/search/small_graphs.py counterexample \
      --claim notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/debe_zinchenko_claims.py

The paper's lemmas are about a hypothetical counterexample, so they cannot be tested as stated
(no hypomorphic non-isomorphic pair exists for 3 <= n <= 13). Each check below replaces
"K is hypomorphic to G" by the only consequence the paper's proof uses at that point:

  dbe-graph   degrees are exactly {d, d+1}, every low vertex has b high neighbours, every high
              vertex has e high neighbours (paper Lemma 2.4; theta = e - b).
  dbe-extension of G at u: a dbe-graph with the same (d, b, e) that agrees with G off u.

Checks (the names are the paper's):
  L24   t(G) = 2 with two degrees d, d+1  ==>  dbe-graph.
  L31c  (A - (theta - s) I) z = k eps_u for every dbe-extension, z = a_G(u) - a_K(u).
  L33   if u has a dbe-extension K != G, every (theta - s)-eigenvector of A_G vanishes at u.
  L34r  for two dbe-extensions K1, K2 != G at u: y = k2 z1 - k1 z2 is in ker(A - (theta - s) I)
        and y(x) = 0 at every x of the class of u that has its own dbe-extension != G.
  L92   F regular, r a vertex, the cards F - v (v != r) pairwise isomorphic ==> F - r is
        isomorphic to them.
  T93   endgame: degrees {d, d+1}, |L| = d + 1, G_v := (G - v) + a new vertex joined to
        L \\ {v}; if the G_v are pairwise isomorphic then G is isomorphic to them.
"""
import itertools
import os
import sys

import networkx as nx
import sympy

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon  # noqa: E402

STATS = {"dbe": 0, "dbe_with_ext": 0, "ext_pairs": 0, "L34_instances": 0, "L92_hyp": 0,
         "T93_hyp": 0, "t2_two_deg": 0}


def dbe(G):
    """(d, b, e, L, U) if G is a dbe-graph, else None."""
    deg = dict(G.degree())
    ds = sorted(set(deg.values()))
    if len(ds) != 2 or ds[1] != ds[0] + 1:
        return None
    d = ds[0]
    U = {x for x in G if deg[x] == d + 1}
    L = set(G) - U
    bs = {len(U & set(G[x])) for x in L}
    es = {len(U & set(G[x])) for x in U}
    if len(bs) != 1 or len(es) != 1:
        return None
    return d, bs.pop(), es.pop(), L, U


def extensions(G, u, par):
    """All dbe-extensions K != G of G at u, as (z, k) with z = a_G(u) - a_K(u)."""
    d, b, e, L, U = par
    N = set(G[u])
    lose = sorted(N & U)
    gain = sorted(L - N - {u})
    out = []
    for k in range(1, min(len(lose), len(gain)) + 1):
        for S in itertools.combinations(lose, k):
            for R in itertools.combinations(gain, k):
                K = G.copy()
                K.remove_edges_from((u, x) for x in S)
                K.add_edges_from((u, x) for x in R)
                p2 = dbe(K)
                if p2 is None or p2[:3] != (d, b, e):
                    continue
                z = {x: 0 for x in G}
                for x in S:
                    z[x] = 1
                for x in R:
                    z[x] = -1
                out.append((z, k))
    return out


def check_dbe(G):
    par = dbe(G)
    if par is None:
        return True
    STATS["dbe"] += 1
    d, b, e, L, U = par
    theta = e - b
    nodes = sorted(G)
    A = nx.to_numpy_array(G, nodelist=nodes, dtype=int)
    idx = {x: i for i, x in enumerate(nodes)}
    ext = {u: extensions(G, u, par) for u in nodes}
    if any(ext.values()):
        STATS["dbe_with_ext"] += 1
    for u in nodes:
        s = 1 if u in U else 0
        lam = theta - s
        M = A - lam * __import__("numpy").eye(len(nodes), dtype=int)
        for z, k in ext[u]:
            zv = [z[x] for x in nodes]
            lhs = M.dot(zv)
            rhs = [k if x == u else 0 for x in nodes]
            if list(lhs) != rhs:
                return False                      # L31c
        if ext[u]:
            SM = sympy.Matrix(M.tolist())
            for f in SM.nullspace():
                if f[idx[u]] != 0:
                    return False                  # L33
        for (z1, k1), (z2, k2) in itertools.combinations(ext[u], 2):
            STATS["ext_pairs"] += 1
            y = [k2 * z1[x] - k1 * z2[x] for x in nodes]
            if any(M.dot(y)):
                return False                      # L34r, kernel part
            cls = U if u in U else L
            for x in cls:
                if ext[x]:
                    STATS["L34_instances"] += 1
                    if y[idx[x]] != 0:
                        return False              # L34r, vanishing part
    return True


def check_l24(G):
    deg = dict(G.degree())
    ds = sorted(set(deg.values()))
    if len(ds) != 2 or ds[1] != ds[0] + 1:
        return True
    types = {}
    for v in G:
        H = G.copy()
        H.remove_node(v)
        types[v] = canon(H)
    if len(set(types.values())) != 2:
        return True
    STATS["t2_two_deg"] += 1
    if dbe(G) is None:
        return False
    return all(types[x] == types[y] for x in G for y in G if deg[x] == deg[y])


def check_l92(G):
    deg = set(dict(G.degree()).values())
    if len(deg) != 1 or G.number_of_nodes() < 3:
        return True
    types = {}
    for v in G:
        H = G.copy()
        H.remove_node(v)
        types[v] = canon(H)
    for r in G:
        rest = {types[v] for v in G if v != r}
        if len(rest) == 1:
            STATS["L92_hyp"] += 1
            if types[r] not in rest:
                return False
    return True


def check_t93(G):
    deg = dict(G.degree())
    ds = sorted(set(deg.values()))
    if len(ds) != 2 or ds[1] != ds[0] + 1:
        return True
    d = ds[0]
    L = {x for x in G if deg[x] == d}
    if len(L) != d + 1:
        return True
    types = set()
    for v in G:
        K = G.copy()
        K.remove_node(v)
        K.add_node(v)
        K.add_edges_from((v, x) for x in L if x != v)
        types.add(canon(K))
    if len(types) != 1:
        return True
    STATS["T93_hyp"] += 1
    return canon(G) in types


def claim(G):
    if G.number_of_nodes() < 3:
        return True
    return check_l24(G) and check_dbe(G) and check_l92(G) and check_t93(G)


import atexit  # noqa: E402

atexit.register(lambda: print("debe_zinchenko_claims stats:", STATS))
