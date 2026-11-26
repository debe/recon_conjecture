"""Helpers for sketch t3 (structure: what a structure theorem must allow) of
conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch__no_triple_window.
Evidence only, never a result.

W3 here is the class of the checked statement pointed_triple_window: window census (W) at a doubly
pointed class and kill clause (K) = per pinned twist "fixes N(x) minus y" or "preserves G-degrees".
(t2_lib's mode "K" has a third disjunct that the Lean body does not have; it is not used here.)
"""
import os
import sys
from collections import defaultdict

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
T2DIR = os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch")
sys.path.insert(0, T2DIR)
from t2_lib import Census, canon_marked, k_trivial, k_DP, cond_i, canon, g6, auts  # noqa: E402,F401


def kill_exact(G, C, x, y, z):
    """(K) of the Lean body at one member (x, y, z): every automorphism of G-x-y fixing z
    fixes N(x) minus y, or preserves G-degrees.  Returns (ok, n_stab, n_bad)."""
    S, A, Nu, Nv, Ku, Kv = C.pd(x, y)
    n_stab = n_bad = 0
    for g in A:
        if g[z] != z:
            continue
        n_stab += 1
        if not (k_trivial(G, x, y, S, Nu, g) or k_DP(G, S, g)):
            n_bad += 1
    return n_bad == 0, n_stab, n_bad


def classes(G, C=None):
    """All doubly pointed classes with their census data.
    Returns a list of dicts: rep, A (members), nR, W (census holds), K (kill holds at every member),
    i (clause (i) at the representative pair)."""
    C = C or Census(G)
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
        W = len(Rs) < len(Acl)
        K = None
        if W:
            K = all(kill_exact(G, C, x, y, z)[0] for (x, y, z) in Acl)
        out.append(dict(rep=(u, v, w), A=Acl, nA=len(Acl), nR=len(Rs), W=W, K=K, i=cond_i(G, u, v), R=Rs))
    return out


def in_w3(G, C=None):
    for c in classes(G, C):
        if c["W"] and c["K"]:
            return c
    return None


def w3_set(G, C=None):
    """Set of all ordered triples (u, v, w) at which W3 holds."""
    out = set()
    for c in classes(G, C):
        if c["W"] and c["K"]:
            out.update(c["A"])
    return out


def lex(X, A):
    """Lexicographic product X[A] on integer labels; returns (G, fibre, coord)."""
    X = nx.convert_node_labels_to_integers(X)
    A = nx.convert_node_labels_to_integers(A)
    m = A.number_of_nodes()
    G = nx.Graph()
    lab = {(p, a): p * m + a for p in X for a in A}
    G.add_nodes_from(lab.values())
    for p in X:
        for a, b in A.edges():
            G.add_edge(lab[(p, a)], lab[(p, b)])
    for p, q in X.edges():
        for a in A:
            for b in A:
                G.add_edge(lab[(p, a)], lab[(q, b)])
    inv = {i: pa for pa, i in lab.items()}
    return G, lab, inv


def corona(H):
    H = nx.convert_node_labels_to_integers(H)
    n = H.number_of_nodes()
    G = H.copy()
    for h in range(n):
        G.add_edge(h, n + h)
    return G
