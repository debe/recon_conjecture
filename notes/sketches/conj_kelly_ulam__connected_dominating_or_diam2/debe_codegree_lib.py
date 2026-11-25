"""Shared helpers for sketch debe_codegree (triangle / co-triangle vertex keys).

Evidence only, never a result. Graphs are networkx graphs on 0..n-1.

Vertex key  kappa(x) = (deg x, t(x), tbar(x)):
  t(x)    = number of triangles through x      = edges inside N(x)
  tbar(x) = number of independent triples through x = non-edges inside V - N[x]
Pair statistics: codeg(x, y) = common neighbours, cocodeg(x, y) = common non-neighbours
(outside {x, y}).
"""
import itertools
import os
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import ctype  # noqa: E402


def tri(G, x):
    N = list(G[x])
    return sum(1 for a, b in itertools.combinations(N, 2) if G.has_edge(a, b))


def cotri(G, x):
    M = [w for w in G.nodes() if w != x and not G.has_edge(x, w)]
    return sum(1 for a, b in itertools.combinations(M, 2) if not G.has_edge(a, b))


def keys(G):
    return {x: (G.degree(x), tri(G, x), cotri(G, x)) for x in G.nodes()}


def codeg(G, x, y):
    return len(set(G[x]) & set(G[y]))


def cocodeg(G, x, y):
    return sum(1 for w in G.nodes()
               if w not in (x, y) and not G.has_edge(x, w) and not G.has_edge(y, w))


def cond_R(key):
    """(R): among vertices of equal degree, t(x) = t(x') iff tbar(x) = tbar(x')."""
    f, g = {}, {}
    for (a, t, tb) in set(key.values()):
        if f.setdefault((a, t), tb) != tb:
            return False
        if g.setdefault((a, tb), t) != t:
            return False
    return True


def pair_types(G):
    """type id of G - x - y for unordered pairs, as dict on ordered pairs."""
    ty = {}
    for x, y in itertools.combinations(sorted(G.nodes()), 2):
        F = ctype(G, (x, y))
        ty[(x, y)] = F
        ty[(y, x)] = F
    return ty


def ref_table(G, key=None, ty=None):
    """pi[(F, k)] = ordered pairs (x, y) of type F with kappa(x) = k; e[...] = adjacent ones."""
    if key is None:
        key = keys(G)
    if ty is None:
        ty = pair_types(G)
    pi, e = Counter(), Counter()
    for (x, y), F in ty.items():
        pi[(F, key[x])] += 1
        if G.has_edge(x, y):
            e[(F, key[x])] += 1
    return pi, e


def deg_table(G, ty=None):
    if ty is None:
        ty = pair_types(G)
    pi, e = Counter(), Counter()
    for (x, y), F in ty.items():
        pi[(F, G.degree(x))] += 1
        if G.has_edge(x, y):
            e[(F, G.degree(x))] += 1
    return pi, e


def forced_pairs(G):
    """For every ordered pair (u, y): which per-pair forcing conditions hold.

    Returns dict (u, y) -> set of labels among
      'deg'  : all type-F pairs with first degree deg u have the adjacency of (u, y)
      'ref'  : (R) holds and all type-F pairs with first key kappa(u) have that adjacency
      'esc'  : escape: no type-F pair (z, w) whose first vertex has the phantom partner key
    """
    key = keys(G)
    ty = pair_types(G)
    R = cond_R(key)
    pi, e = ref_table(G, key, ty)
    dpi, de = deg_table(G, ty)
    # first-vertex partial keys present per type
    has_dt = set()   # (F, deg, t)
    has_dtb = set()  # (F, deg, tbar)
    for (x, y), F in ty.items():
        a, t, tb = key[x]
        has_dt.add((F, a, t))
        has_dtb.add((F, a, tb))
    out = {}
    for (u, y), F in ty.items():
        lab = set()
        adj = G.has_edge(u, y)
        a = G.degree(u)
        if de[(F, a)] == (dpi[(F, a)] if adj else 0):
            lab.add('deg')
        if R and e[(F, key[u])] == (pi[(F, key[u])] if adj else 0):
            lab.add('ref')
        ay, ty_, tby = key[y]
        if adj:
            if (F, ay - 1, ty_ - codeg(G, u, y)) not in has_dt:
                lab.add('esc')
        else:
            if (F, ay + 1, tby - cocodeg(G, u, y)) not in has_dtb:
                lab.add('esc')
        out[(u, y)] = lab
    return out, R


def classes(G):
    """Membership of G in the classes of the sketch (single-graph facts)."""
    fp, R = forced_pairs(G)
    nodes = sorted(G.nodes())

    def some_u(labels):
        return any(all(fp[(u, y)] & labels for y in nodes if y != u) for u in nodes)

    return {
        'R': R,
        'P': some_u({'deg'}),                  # per-pair form of Lemma P at one vertex
        'CR': R and some_u({'ref'}),           # (R) + refined purity  [Theorem A]
        'CE': some_u({'esc'}),                 # escape class          [Theorem B]
        'CRE': some_u({'ref', 'esc'}),         # mixed, per pair
        'ALL': some_u({'deg', 'ref', 'esc'}),
    }
