"""Shared helpers for sketch t2 of
conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card.

Evidence only, never a result. Graphs are networkx graphs on 0..n-1.

remainder(G)  = the class of the frozen step, clause by clause from the Lean body:
  D2, no pure degree class, no unique-copy factorizing pair, no level-wise half-pure vertex,
  not in the narrow two-card class N.
"""
import itertools
import os
import sys
from collections import Counter, defaultdict

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2")
sys.path.insert(0, PARENT)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "search"))
from small_graphs import canon, g6  # noqa: E402,F401
from t4_lib import ctype, in_D2, pair_table, pure_degrees, unique_copy_pairs, factorizes  # noqa: E402


def from_g6(s):
    return nx.convert_node_labels_to_integers(nx.from_graph6_bytes(s.encode()))


def pair_types(G):
    ty = {}
    for x, y in itertools.combinations(sorted(G.nodes()), 2):
        F = ctype(G, (x, y))
        ty[(x, y)] = F
        ty[(y, x)] = F
    return ty


def forced(G, ty=None):
    """forced[(u, y)] = True iff every ordered pair (x', y') of the type of (u, y) with
    deg x' = deg u has the adjacency of (u, y) (the 'forced' of Theorem D)."""
    if ty is None:
        ty = pair_types(G)
    deg = dict(G.degree())
    pi, e = Counter(), Counter()
    for (x, y), F in ty.items():
        pi[(F, deg[x])] += 1
        if G.has_edge(x, y):
            e[(F, deg[x])] += 1
    out = {}
    for (u, y), F in ty.items():
        k = (F, deg[u])
        out[(u, y)] = (e[k] == pi[k]) if G.has_edge(u, y) else (e[k] == 0)
    return out


def half_pure_vertices(G, fo=None):
    """Vertices u with the predicate of level_half_pure (Theorem D)."""
    if fo is None:
        fo = forced(G)
    deg = dict(G.degree())
    out = []
    for u in G.nodes():
        ok = True
        nb = set(G[u])
        levels = set(deg[y] - (1 if y in nb else 0) for y in G.nodes() if y != u)
        for j in levels:
            a = all(fo[(u, y)] for y in nb if deg[y] == j + 1)
            b = all(fo[(u, y)] for y in G.nodes() if y != u and y not in nb and deg[y] == j)
            if not (a or b):
                ok = False
                break
        if ok:
            out.append(u)
    return out


def card(G, u):
    H = G.copy()
    H.remove_node(u)
    return H


def card_isos(G, u, v):
    """All isomorphisms G - u -> G - v as dicts."""
    return list(GraphMatcher(card(G, u), card(G, v)).isomorphisms_iter())


def in_N(G):
    """Narrow two-card class, clause by clause."""
    deg = dict(G.degree())
    ds = sorted(set(deg.values()))
    if not (len(ds) == 1 or (len(ds) == 2 and ds[1] == ds[0] + 1)):
        return False
    ct = {v: ctype(G, (v,)) for v in G.nodes()}
    if any(ct[x] != ct[y] for x in G for y in G if deg[x] == deg[y]):
        return False
    for u in G.nodes():
        for v in G.nodes():
            if ct[u] != ct[v]:
                continue
            Nu, Nv = set(G[u]), set(G[v])
            for a in card_isos(G, u, v):
                if any(a[x] not in Nv for x in Nu):
                    return True
    return False


def has_glue(G):
    for (u, v) in unique_copy_pairs(G):
        if factorizes(G, u, v)[0] or factorizes(G, v, u)[0]:
            return True
    return False


def remainder(G, need_glue=True):
    if not in_D2(G):
        return False
    pi, e = pair_table(G)
    if pure_degrees(G, pi, e):
        return False
    if half_pure_vertices(G):
        return False
    if in_N(G):
        return False
    if need_glue and has_glue(G):
        return False
    return True


def triv(G, u):
    """Triv(u): the neighbourhoods alpha(N(u')) for card isomorphisms alpha : G - u' -> G - u.
    Re-attaching u to any of them gives a graph isomorphic to G."""
    out = set()
    cu = ctype(G, (u,))
    for v in G.nodes():
        if ctype(G, (v,)) != cu:
            continue
        Nv = set(G[v])
        for a in card_isos(G, v, u):
            out.add(frozenset(a[x] for x in Nv))
    return out


def reattach(G, u, S):
    H = G.copy()
    H.remove_edges_from([(u, w) for w in list(H[u])])
    H.add_edges_from((u, w) for w in S)
    return H


def equitable_two_degrees(G):
    """Degrees in {d, d+1} (both occurring) and the number of high neighbours depends only
    on the degree. Returns (d, b, e) or None."""
    deg = dict(G.degree())
    ds = sorted(set(deg.values()))
    if not (len(ds) == 2 and ds[1] == ds[0] + 1):
        return None
    hi = ds[1]
    h = {v: sum(1 for w in G[v] if deg[w] == hi) for v in G}
    lo_vals = {h[v] for v in G if deg[v] == ds[0]}
    hi_vals = {h[v] for v in G if deg[v] == hi}
    if len(lo_vals) != 1 or len(hi_vals) != 1:
        return None
    return ds[0], lo_vals.pop(), hi_vals.pop()


def has_nonextending(G, v):
    """Some card isomorphism alpha : G - u -> G - v with alpha(N(u)) != N(v)."""
    cv = ctype(G, (v,))
    Nv = frozenset(G[v])
    for u in G.nodes():
        if ctype(G, (u,)) != cv:
            continue
        Nu = set(G[u])
        for a in GraphMatcher(card(G, u), card(G, v)).isomorphisms_iter():
            if frozenset(a[x] for x in Nu) != Nv:
                return True
    return False


def in_Nplus(G):
    """Class N+ of the sketch: degrees d, d+1, equitable degree partition, and every vertex
    of one degree class has a non-extending incoming card isomorphism.
    Returns '' or a string naming the class(es) ('low', 'high')."""
    eq = equitable_two_degrees(G)
    if eq is None:
        return ''
    d = eq[0]
    deg = dict(G.degree())
    out = []
    if all(has_nonextending(G, v) for v in G if deg[v] == d):
        out.append('low')
    if all(has_nonextending(G, v) for v in G if deg[v] == d + 1):
        out.append('high')
    return '+'.join(out)
