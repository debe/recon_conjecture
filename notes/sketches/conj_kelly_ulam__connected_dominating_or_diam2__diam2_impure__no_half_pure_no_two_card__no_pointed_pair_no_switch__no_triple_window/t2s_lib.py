"""Helpers for sketch t2 (structure of the remainder outside W3: slices, phantoms, codegree kill).
Evidence only, never a result.  Re-uses the round-12 library of the W3 sketch."""
import os
import sys
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
W3DIR = os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch")
sys.path.insert(0, W3DIR)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "search"))
from t2_lib import *  # noqa: E402,F401
from t2_lib import Census, canon, twist_graph, k_trivial, k_DP, k_SQ, kill_all, triple_census_w, pair_census_w  # noqa: E402


def eps_of(S, Nu, g):
    """eps_x = [u ~ g x] - [u ~ x] on S for the twist by g (u re-attached to g^{-1} N_u)."""
    return {x: int(g[x] in Nu) - int(x in Nu) for x in S}


def codeg_change(S, Nu, Nv, g):
    """c = #{x in S : u ~ g x, v ~ x} - #{x in S : u ~ x, v ~ x}."""
    return sum(1 for x in S if g[x] in Nu and x in Nv) - len(Nu & Nv)


def k_CD(G, u, v, S, Nu, Nv, g):
    """kill clause (K-cd): the twist is trivial at u, or it changes the codegree of (u, v)."""
    return k_trivial(G, u, v, S, Nu, g) or codeg_change(S, Nu, Nv, g) != 0


def kill_all_cd(G, C, x, y, fix=None, mode="CD"):
    """per-twist kill clauses at (x, y), over Aut(G-x-y) or over the stabiliser of `fix`:
    K2  = g fixes N(x), or g preserves G-degrees            (the frozen Lean body of W3)
    CD  = g fixes N(x), or g changes the codegree of (x, y)  (class W3cd of the sketch)
    CD3 = CD, or g fixes N(y)                                (to compare with the round-12 mode "K")"""
    S, A, Nu, Nv, Ku, Kv = C.pd(x, y)
    for g in A:
        if fix is not None and g[fix] != fix:
            continue
        if mode == "K2":
            ok = k_trivial(G, x, y, S, Nu, g) or k_DP(G, S, g)
        elif mode == "CD":
            ok = k_CD(G, x, y, S, Nu, Nv, g)
        elif mode == "CD3":
            ok = k_CD(G, x, y, S, Nu, Nv, g) or k_trivial(G, y, x, S, Nv, g)
        else:
            raise ValueError(mode)
        if not ok:
            return False
    return True


def slices(G, C=None):
    """F -> Counter(pointed type of (G-x, y)) over the ordered pairs (x, y) with G-x-y of type F.
    This is the slice of the pointed deck over F (it contains the number of ordered pairs of type F)."""
    C = C or Census(G, triples=False)
    out = defaultdict(Counter)
    for p, F in C.ty.items():
        out[F][C.c2[p]] += 1
    return out


def degseq(G):
    return tuple(sorted(d for _, d in G.degree()))


def graphs_n(n):
    """All graphs on n vertices: the atlas for n <= 7; for n = 8 one-vertex extensions of the
    atlas graphs on 7 vertices, deduplicated by canonical form (expected 12346)."""
    import itertools
    import networkx as nx
    from small_graphs import all_graphs
    if n <= 7:
        return [nx.convert_node_labels_to_integers(G) for G in all_graphs(n)]
    if n != 8:
        raise ValueError(n)
    seen, out = set(), []
    for G in all_graphs(7):
        G = nx.convert_node_labels_to_integers(G)
        for k in range(8):
            for N in itertools.combinations(range(7), k):
                H = G.copy()
                H.add_node(7)
                H.add_edges_from((7, x) for x in N)
                c = canon(H)
                if c not in seen:
                    seen.add(c)
                    out.append(H)
    return out
