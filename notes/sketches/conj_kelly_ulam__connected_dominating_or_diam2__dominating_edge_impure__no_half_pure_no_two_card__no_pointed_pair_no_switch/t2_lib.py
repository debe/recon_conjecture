"""Helpers for sketch t2 (triple pointed census) of
conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch.
Evidence only, never a result."""
import itertools
import os
import sys
from collections import Counter, defaultdict

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card"))
import t3_lib as L  # noqa: E402
from t3_lib import from_g6, auts, pair_types, pointed_classes, pair_data, deg_preserving, factor_ok, T_pairs, Tplus_pairs, canon, g6  # noqa: E402


def marked_isos(G, del1, marks1, del2, marks2):
    """All isomorphisms G - del1 -> G - del2 mapping marks1[i] to marks2[i]."""
    A = G.subgraph([w for w in G if w not in del1]).copy()
    B = G.subgraph([w for w in G if w not in del2]).copy()
    for w in A:
        A.nodes[w]["m"] = (marks1.index(w) + 1) if w in marks1 else 0
    for w in B:
        B.nodes[w]["m"] = (marks2.index(w) + 1) if w in marks2 else 0
    return list(GraphMatcher(A, B, node_match=lambda a, b: a["m"] == b["m"]).isomorphisms_iter())


def marked_iso_exists(G, del1, marks1, del2, marks2, H=None):
    H = H or G
    A = G.subgraph([w for w in G if w not in del1]).copy()
    B = H.subgraph([w for w in H if w not in del2]).copy()
    for w in A:
        A.nodes[w]["m"] = (marks1.index(w) + 1) if w in marks1 else 0
    for w in B:
        B.nodes[w]["m"] = (marks2.index(w) + 1) if w in marks2 else 0
    return GraphMatcher(A, B, node_match=lambda a, b: a["m"] == b["m"]).is_isomorphic()


# ---------------------------------------------------------------------------
# pointed classes of pairs and triples, with witnesses
# ---------------------------------------------------------------------------

def first_iso(G, del1, marks1, del2, marks2):
    A = G.subgraph([w for w in G if w not in del1]).copy()
    B = G.subgraph([w for w in G if w not in del2]).copy()
    for w in A:
        A.nodes[w]["m"] = (marks1.index(w) + 1) if w in marks1 else 0
    for w in B:
        B.nodes[w]["m"] = (marks2.index(w) + 1) if w in marks2 else 0
    for m in GraphMatcher(A, B, node_match=lambda a, b: a["m"] == b["m"]).isomorphisms_iter():
        return m
    return None


from small_graphs import _leaves  # noqa: E402


def canon_marked(G, drop, marks):
    """Canonical form of (G - drop; marks): the marked vertices are individualised in order,
    so two results are equal iff there is an isomorphism matching the marks in order."""
    keep = [x for x in sorted(G.nodes()) if x not in drop]
    idx = {x: i for i, x in enumerate(keep)}
    adj = [frozenset(idx[y] for y in G[x] if y in idx) for x in keep]
    edges = [(idx[a], idx[b]) for a, b in G.edges() if a in idx and b in idx]
    cells = [[idx[m]] for m in marks]
    rest = [idx[x] for x in keep if x not in marks]
    if rest:
        cells.append(rest)
    best = None
    for order in _leaves(adj, cells):
        pos = {v: i for i, v in enumerate(order)}
        b = tuple(sorted((min(pos[a], pos[b]), max(pos[a], pos[b])) for a, b in edges))
        if best is None or b < best:
            best = b
    return (len(keep), len(marks), best or ())


class Census:
    """All pointed data of one graph, as canonical forms (comparable across graphs).
    c2[(x,y)]      type of the pointed card (G-x, y)
    c3[(x,y,z)]    type of the doubly pointed card (G-x; y, z)
    p3[(x,y,z)]    type of the pointed two-deleted graph (G-x-y; z)   (symmetric in x, y)
    ty[(x,y)]      type of G-x-y
    """

    def __init__(self, G, triples=True):
        self.G = G
        V = sorted(G.nodes())
        self.V = V
        self.ty = pair_types(G)
        self.c2 = {(x, y): canon_marked(G, (x,), (y,)) for (x, y) in self.ty}
        self.c3 = {}
        self.p3 = {}
        if triples:
            for (x, y) in self.ty:
                for z in V:
                    if z in (x, y):
                        continue
                    self.c3[(x, y, z)] = canon_marked(G, (x,), (y, z))
                    if x < y:
                        p = canon_marked(G, (x, y), (z,))
                        self.p3[(x, y, z)] = p
                        self.p3[(y, x, z)] = p
        self._pd = {}

    def pd(self, u, v):
        """S, Aut(F), Nu, Nv, K_u (restrictions of Aut(G-u)_v), K_v."""
        if (u, v) not in self._pd:
            S, A, Nu, Nv = pair_data(self.G, u, v)
            Ku = [g for g in A if L.img(g, Nv) == Nv]
            Kv = [g for g in A if L.img(g, Nu) == Nu]
            self._pd[(u, v)] = (S, A, Nu, Nv, Ku, Kv)
        return self._pd[(u, v)]


# ---------------------------------------------------------------------------
# twist kills.  Twist of G at u by g in Aut(G-u-v): u re-attached to
# {x in S : u ~ g x} (+ v if u ~ v).
# ---------------------------------------------------------------------------

def twist_graph(G, u, v, S, Nu, g):
    H = G.copy()
    H.remove_edges_from([(u, x) for x in list(G[u])])
    H.add_edges_from((u, x) for x in S if g[x] in Nu)
    if G.has_edge(u, v):
        H.add_edge(u, v)
    return H


def k_trivial(G, u, v, S, Nu, g):
    return all((g[x] in Nu) == (x in Nu) for x in S)


def k_DP(G, S, g):
    return deg_preserving(G, S, g)


def k_DC(G, S, g, Ku, Kv):
    for ku in Ku:
        for kv in Kv:
            if all(G.degree(kv[g[ku[x]]]) == G.degree(x) for x in S):
                return True
    return False


def k_SQ(G, u, v, S, Nu, g):
    """twist trivial or the sum of squared degrees changes."""
    eps = {x: int(g[x] in Nu) - int(x in Nu) for x in S}
    if not any(eps.values()):
        return True
    return 2 * sum(G.degree(x) * e for x, e in eps.items()) + sum(e * e for e in eps.values()) != 0


def k_SEQ(G, u, v, S, Nu, g, cG=None):
    """twist isomorphic to G or its degree multiset differs."""
    H = twist_graph(G, u, v, S, Nu, g)
    if sorted(d for _, d in H.degree()) != sorted(d for _, d in G.degree()):
        return True
    return canon(H) == (cG or canon(G))


def deck(G):
    return sorted(str(L.ctype(G, (v,))) for v in G)


def k_ISO(G, u, v, S, Nu, g, cG=None):
    """twist isomorphic to G or not hypomorphic to G (the ceiling of any twist kill)."""
    H = twist_graph(G, u, v, S, Nu, g)
    if canon(H) == (cG or canon(G)):
        return True
    return deck(H) != deck(G)


def _inv(g):
    return {b: a for a, b in g.items()}


def kill_all(G, C, x, y, mode, fix=None):
    S, A, Nu, Nv, Ku, Kv = C.pd(x, y)
    cG = canon(G)
    for g in A:
        if fix is not None and g[fix] != fix:
            continue
        if mode == "DP":
            ok = k_DP(G, S, g)
        elif mode == "DPF":
            ok = k_DP(G, S, g) or factor_ok(A, Nu, Nv, g)
        elif mode == "DC":
            ok = k_DC(G, S, g, Ku, Kv)
        elif mode == "SQ":
            ok = k_SQ(G, x, y, S, Nu, g)
        elif mode == "SEQ":
            ok = k_SEQ(G, x, y, S, Nu, g, cG)
        elif mode == "ISO":
            ok = k_ISO(G, x, y, S, Nu, g, cG)
        elif mode == "TRIV":
            ok = k_trivial(G, x, y, S, Nu, g)
        elif mode == "K":      # the clause of class C3: trivial at x, or trivial at y, or degree preserving
            ok = k_trivial(G, x, y, S, Nu, g) or k_trivial(G, y, x, S, Nv, g) or k_DP(G, S, g)
        elif mode == "LVF":
            ok = (not L.adm_deg(G, S, Nu, _inv(g))) or factor_ok(A, Nu, Nv, g)
        elif mode == "SQF":
            ok = k_SQ(G, x, y, S, Nu, g) or factor_ok(A, Nu, Nv, g)
        elif mode == "NONE":
            ok = True
        else:
            raise ValueError(mode)
        if not ok:
            return False
    return True


def cond_i(G, u, v):
    alpha = int(G.has_edge(u, v))
    return G.degree(u) - G.degree(v) not in (-alpha, 1 - alpha)


def pair_census(G, C):
    """Pointed classes (rep pairs) passing the unified pair census:
    ((i) or A subset of C) and #(P minus (A union C)) < #A."""
    members = defaultdict(list)
    for p, r in C.c2.items():
        members[r].append(p)
    tsize = Counter(C.ty.values())
    out = []
    for r, Acl in members.items():
        chat = {C.c2[(y, x)] for (x, y) in Acl}
        sym = r in chat
        if not (sym or cond_i(G, Acl[0][0], Acl[0][1])):
            continue
        sz = sum(len(members[j]) for j in chat | {r})
        if tsize[C.ty[Acl[0]]] - sz < len(Acl):
            out.append((r, Acl))
    return out


def triple_census(G, C):
    """Doubly pointed classes passing the unified triple census (swap of the first two entries):
    ((i) or A subset of C) and #(P3 minus (A union C)) < #A,
    P3 = triples with the pointed two-deleted type (G-u-v; w)."""
    members = defaultdict(list)
    for t, r in C.c3.items():
        members[r].append(t)
    psize = Counter(C.p3.values())
    out = []
    for r, Acl in members.items():
        (u, v, w) = Acl[0]
        chat = {C.c3[(y, x, z)] for (x, y, z) in Acl}
        sym = r in chat
        if not (sym or cond_i(G, u, v)):
            continue
        sz = sum(len(members[j]) for j in chat | {r})
        if psize[C.p3[(u, v, w)]] - sz < len(Acl):
            out.append((r, Acl))
    return out


def in_pair_class(G, C, mode):
    for r, Acl in pair_census(G, C):
        if all(kill_all(G, C, x, y, mode) for (x, y) in Acl):
            return Acl[0]
    return None


def in_triple_class(G, C, mode):
    for r, Acl in triple_census(G, C):
        if all(kill_all(G, C, x, y, mode, fix=z) for (x, y, z) in Acl):
            return Acl[0]
    return None


# ---------------------------------------------------------------------------
# refined census: degree window instead of clause (i)
# R* = {t in P, class not in C, deg(first) - deg_{G-u}(v) in {0, 1}};  #R* < #A
# ---------------------------------------------------------------------------

def pair_census_w(G, C):
    members = defaultdict(list)
    for p, r in C.c2.items():
        members[r].append(p)
    bytype = defaultdict(list)
    for p, F in C.ty.items():
        bytype[F].append(p)
    out = []
    for r, Acl in members.items():
        u, v = Acl[0]
        dv = G.degree(v) - int(G.has_edge(u, v))
        chat = {C.c2[(y, x)] for (x, y) in Acl}
        Rs = [p for p in bytype[C.ty[(u, v)]] if C.c2[p] not in chat and G.degree(p[0]) - dv in (0, 1)]
        if len(Rs) < len(Acl):
            out.append((r, Acl))
    return out


def triple_census_w(G, C):
    members = defaultdict(list)
    for t, r in C.c3.items():
        members[r].append(t)
    byport = defaultdict(list)
    for t, p in C.p3.items():
        byport[p].append(t)
    out = []
    for r, Acl in members.items():
        (u, v, w) = Acl[0]
        dv = G.degree(v) - int(G.has_edge(u, v))
        chat = {C.c3[(y, x, z)] for (x, y, z) in Acl}
        Rs = [t for t in byport[C.p3[(u, v, w)]] if C.c3[t] not in chat and G.degree(t[0]) - dv in (0, 1)]
        if len(Rs) < len(Acl):
            out.append((r, Acl))
    return out


def in_pair_class_w(G, C, mode, cen=None):
    for r, Acl in (cen if cen is not None else pair_census_w(G, C)):
        if all(kill_all(G, C, x, y, mode) for (x, y) in Acl):
            return Acl[0]
    return None


def in_triple_class_w(G, C, mode, cen=None):
    for r, Acl in (cen if cen is not None else triple_census_w(G, C)):
        if all(kill_all(G, C, x, y, mode, fix=z) for (x, y, z) in Acl):
            return Acl[0]
    return None
