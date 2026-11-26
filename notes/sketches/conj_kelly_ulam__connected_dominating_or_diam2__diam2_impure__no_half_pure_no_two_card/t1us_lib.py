"""Shared helpers for sketch t1 (two-main-eigenvalue switching class). Evidence only.

Graphs are networkx graphs on 0..n-1.

Remainder predicate = clause-by-clause transcription of the Lean body of
conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card
(and of its dominating-edge twin), built from the earlier sketch libraries.

New objects of this sketch:
  two_walk_linear(G)   -> (a, b) rational with  sum_{y ~ x} deg y = a deg x + b  for all x, or None
  switch_vectors(G, u, a) -> all admissible z (see sketch, class SW): z in {-1,0,1}^V, z(u)=0,
      z=1 only on N(u), z=-1 only off N[u], sum z = 0, z != 0,
      sum_{y ~ x} z(y) = (a - deg u) z(x) for every x != u.
"""
import itertools
import os
import sys
from fractions import Fraction

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2")
sys.path.insert(0, PARENT)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "search"))
from small_graphs import canon, g6  # noqa: E402,F401
from t4_lib import (ctype, diam_le2, pair_table, pure_degrees, factorizes,  # noqa: E402
                    unique_copy_pairs)
from t4_stats import dom_edge  # noqa: E402
from debe_codegree_lib import deg_table, pair_types  # noqa: E402


# ----------------------------------------------------------------------------- old classes
def level_half_pure(G):
    """Theorem D predicate (degree-typed forcing), some vertex u."""
    ty = pair_types(G)
    dpi, de = deg_table(G, ty)
    deg = dict(G.degree())
    nodes = sorted(G.nodes())
    for u in nodes:
        a = deg[u]
        levels = {}
        for y in nodes:
            if y == u:
                continue
            adj = G.has_edge(u, y)
            F = ty[(u, y)]
            forced = de[(F, a)] == (dpi[(F, a)] if adj else 0)
            levels.setdefault(deg[y] - (1 if adj else 0), ([], []))[0 if adj else 1].append(forced)
        if all(all(nb) or all(nn) for nb, nn in levels.values()):
            return True
    return False


def card_types(G):
    out = {}
    for v in G:
        H = G.copy()
        H.remove_node(v)
        out[v] = canon(H)
    return out


def normal_form(G):
    deg = dict(G.degree())
    ds = sorted(set(deg.values()))
    if not (len(ds) <= 2 and ds[-1] - ds[0] <= 1):
        return False
    ty = card_types(G)
    return all(ty[x] == ty[y] for x in G for y in G if deg[x] == deg[y])


def narrow_two_card(G):
    """Lean clause N: degrees in {d, d+1}; equal degree => isomorphic cards; some card
    isomorphism G-u -> G-u' moves a neighbour of u to a non-neighbour of u'."""
    if not normal_form(G):
        return False
    deg = dict(G.degree())
    for u in G:
        Cu = G.copy()
        Cu.remove_node(u)
        Nu = set(G[u])
        for w in G:
            if deg[w] != deg[u]:
                continue
            Cw = G.copy()
            Cw.remove_node(w)
            Nw = set(G[w])
            for m in GraphMatcher(Cu, Cw).isomorphisms_iter():
                if any(m[x] not in Nw for x in Nu):
                    return True
    return False


def branch(G):
    Gc = nx.complement(G)
    if not (nx.is_connected(G) and nx.is_connected(Gc)):
        return None
    if diam_le2(G) and diam_le2(Gc):
        return "D2"
    if dom_edge(G):
        return "DE"
    return None


def classify(G):
    """dict of memberships; 'rem' = in the frozen remainder of its branch."""
    out = {"branch": branch(G)}
    pi, e = pair_table(G)
    out["pure"] = bool(pure_degrees(G, pi, e))
    out["D"] = level_half_pure(G)
    out["N"] = narrow_two_card(G)
    out["NF"] = normal_form(G)
    out["glue"] = None
    out["rem"] = False
    if out["branch"] and not out["pure"] and not out["D"] and not out["N"]:
        out["glue"] = any(factorizes(G, u, v)[0] for (u, v) in unique_copy_pairs(G))
        out["rem"] = not out["glue"]
    return out


# ----------------------------------------------------------------------------- new objects
def w2(G):
    deg = dict(G.degree())
    return {x: sum(deg[y] for y in G[x]) for x in G}


def two_walk_linear(G):
    """(a, b) with w2(x) = a deg x + b for all x; None if no such pair or G is regular."""
    deg = dict(G.degree())
    w = w2(G)
    ds = sorted(set(deg.values()))
    if len(ds) < 2:
        return None
    val = {}
    for x in G:
        if val.setdefault(deg[x], w[x]) != w[x]:
            return None
    d0, d1 = ds[0], ds[1]
    a = Fraction(val[d1] - val[d0], d1 - d0)
    b = val[d0] - a * d0
    if all(val[d] == a * d + b for d in ds):
        return a, b
    return None


def _kernel(M, ncols):
    """Reduced-echelon kernel basis of a rational matrix (list of rows of Fractions)."""
    M = [row[:] for row in M]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [v * inv for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [vi - f * vr for vi, vr in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [Fraction(0)] * ncols
        v[fc] = Fraction(1)
        for i, pc in enumerate(piv):
            v[pc] = -M[i][fc]
        basis.append(v)
    return basis, free


def card_kernel(G, u, lam):
    """Kernel of A_{G-u} - lam (vectors indexed by the sorted vertices != u)."""
    others = [x for x in sorted(G.nodes()) if x != u]
    idx = {x: i for i, x in enumerate(others)}
    m = len(others)
    M = [[Fraction(0)] * m for _ in range(m)]
    for x in others:
        M[idx[x]][idx[x]] -= lam
        for y in G[x]:
            if y != u:
                M[idx[x]][idx[y]] += 1
    basis, free = _kernel(M, m)
    return others, basis, free


def switch_vectors(G, u, a):
    """All admissible switching vectors at u (dicts vertex -> -1/0/1), see module docstring."""
    lam = a - G.degree(u)
    others, basis, free = card_kernel(G, u, lam)
    if not basis:
        return []
    N = set(G[u])
    out = []
    for vals in itertools.product((-1, 0, 1), repeat=len(free)):
        if not any(vals):
            continue
        z = [sum(v * b[i] for v, b in zip(vals, basis)) for i in range(len(others))]
        if any(t not in (-1, 0, 1) for t in z) or sum(z) != 0:
            continue
        if any((t == 1 and x not in N) or (t == -1 and x in N) for t, x in zip(z, others)):
            continue
        out.append({x: int(t) for x, t in zip(others, z)})
    return out


def sw_class(G):
    """Class SW: two-walk-linear and some vertex without admissible switching vector.
    Returns (in_class, (a, b), number of vertices without switching vector)."""
    ab = two_walk_linear(G)
    if ab is None:
        return False, None, 0
    free = sum(1 for u in G if not switch_vectors(G, u, ab[0]))
    return free > 0, ab, free


def eig_class(G):
    """Class EIG (smaller, cheaper): two-walk-linear and some u such that a - deg u is not an
    eigenvalue of the card G - u."""
    ab = two_walk_linear(G)
    if ab is None:
        return False
    return any(not card_kernel(G, u, ab[0] - G.degree(u))[1] for u in G)


# ----------------------------------------------------------------------------- named graphs
def paley(q):
    sq = {(x * x) % q for x in range(1, q)}
    G = nx.Graph()
    G.add_nodes_from(range(q))
    G.add_edges_from((a, b) for a, b in itertools.combinations(range(q), 2) if (a - b) % q in sq)
    return G


def clebsch():
    G = nx.Graph()
    G.add_nodes_from(range(16))
    G.add_edges_from((a, b) for a, b in itertools.combinations(range(16), 2)
                     if bin(a ^ b).count("1") in (1, 4))
    return G


def shrikhande():
    pts = [(a, b) for a in range(4) for b in range(4)]
    S = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
    G = nx.Graph()
    G.add_nodes_from(range(16))
    for (i, p), (j, q) in itertools.combinations(enumerate(pts), 2):
        if ((p[0] - q[0]) % 4, (p[1] - q[1]) % 4) in S:
            G.add_edge(i, j)
    return G


def rook(m):
    pts = [(a, b) for a in range(m) for b in range(m)]
    G = nx.Graph()
    G.add_nodes_from(range(m * m))
    for (i, p), (j, q) in itertools.combinations(enumerate(pts), 2):
        if p[0] == q[0] or p[1] == q[1]:
            G.add_edge(i, j)
    return G


def minus(G, v=0):
    H = G.copy()
    H.remove_node(v)
    return nx.convert_node_labels_to_integers(H)


FACE = ["GhdYLc", "GhEKzW", "GhEJ]o", "K[N_ZpBVe`q{", "KbcrMZwA~c@r", "OpyHvCM]IFJpsMdwu`pJp"]
N8_LEFT_DE = ["GH?gmg", "GxckIs", "GKYZ}{", "Gl]o^[", "GHvT~o", "GLvnnw"]


def named():
    out = [(s, nx.convert_node_labels_to_integers(nx.from_graph6_bytes(s.encode())))
           for s in FACE + N8_LEFT_DE]
    out += [("Paley13-v", minus(paley(13))), ("Paley17-v", minus(paley(17))),
            ("Clebsch-v", minus(clebsch())), ("coClebsch-v", minus(nx.complement(clebsch()))),
            ("Shrikhande-v", minus(shrikhande())), ("Rook4-v", minus(rook(4))),
            ("coRook4-v", minus(nx.complement(rook(4))))]
    return out
