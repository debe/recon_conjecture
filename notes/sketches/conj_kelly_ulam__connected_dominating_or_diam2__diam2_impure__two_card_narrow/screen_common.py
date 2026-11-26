"""Shared helpers for the red-team screens of the four proposed children of
conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__two_card_narrow.

Evidence only, never a result.

Model.  A labelled graph on V = {0..n-1} is a networkx graph.  The Lean class
`Recon.Hypomorphic G K` (a bijection sigma with G - x ~= K - sigma x) is tested exactly by deck
equality (`deck_key`), with no appeal to McKay's verification.  For K in the hypomorphism
class, the set C_K(u) of extensions (labelled graphs hypomorphic to G that agree with K on all
pairs avoiding u) is enumerated by trying all 2^(n-1) neighbourhoods of u.

Relabelling.  Every condition in the children is invariant under a simultaneous relabelling
of all graphs and vertices involved (theta and d are global numbers).  So a statement
"for all K in the class, ..." only needs one representative K per isomorphism class occurring
in the hypomorphism class.  The callers pass those representatives.
"""
import itertools
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon, deck_key  # noqa: E402,F401


def nf_ds(G):
    """All d (Lean: universally quantified) for which G is in NF(d): every degree is d or
    d + 1, and equal degrees give isomorphic cards.  Empty if G is not in NF for any d."""
    deg = dict(G.degree())
    vals = set(deg.values())
    if not vals:
        return []
    lo, hi = min(vals), max(vals)
    if hi - lo > 1:
        return []
    # equal-degree vertices must have isomorphic cards
    cards = {}
    for x in G:
        H = G.copy()
        H.remove_node(x)
        c = canon(nx.convert_node_labels_to_integers(H))
        if deg[x] in cards and cards[deg[x]] != c:
            return []
        cards[deg[x]] = c
    if lo == hi:
        return [d for d in (lo - 1, lo) if d >= 0]
    return [lo]


def reattach(K, u, N):
    """K with the neighbourhood of u replaced by N (a set avoiding u)."""
    X = K.copy()
    X.remove_edges_from([(u, y) for y in list(K[u])])
    X.add_edges_from((u, y) for y in N)
    return X


def nbhd(K, u):
    return frozenset(K[u])


def extensions(K, u, deck):
    """C_K(u): neighbourhoods N of u such that reattach(K, u, N) has deck `deck`.
    K's own neighbourhood is included when K itself is in the class."""
    others = [y for y in K if y != u]
    # necessary condition for equal decks: equal degree multisets (deg = e(G) - e(G - v))
    degs_of_deck = deck_degrees(deck)
    out = []
    for r in range(len(others) + 1):
        for N in itertools.combinations(others, r):
            X = reattach(K, u, N)
            if sorted(d for _, d in X.degree()) != degs_of_deck:
                continue
            if deck_key(X) == deck:
                out.append(frozenset(N))
    return out


def deck_degrees(deck):
    """Degree multiset recovered from a deck (Kelly): m = sum m_i / (n - 2), deg = m - m_i."""
    n = len(deck)
    ms = [len(c[1]) for c in deck]
    m = sum(ms) // (n - 2)
    return sorted(m - mi for mi in ms)


def ind(S, y):
    return 1 if y in S else 0


def stage_a(reps, deck, d):
    """Evaluate (a), (b), (c), (d) of child extension_eigen with the hypomorphism class
    given by `deck` and representatives `reps`.  Returns (ok_a, ok_b, ok_c, ok_d, info)."""
    info = {"theta": set(), "pairs": 0, "dpairs": 0, "fail": None}
    ok_a = ok_b = ok_c = ok_d = True
    theta_cons = []          # list of (lhs, z, s): need lhs == (theta - s) * z
    for K in reps:
        n = K.number_of_nodes()
        degK = dict(K.degree())
        # (a)
        if any(degK[x] not in (d, d + 1) for x in K):
            ok_a = False
            info["fail"] = info["fail"] or ("a", K)
        for u in K:
            C = extensions(K, u, deck)
            own = nbhd(K, u)
            # (b)
            if not any(N != own for N in C):
                ok_b = False
                info["fail"] = info["fail"] or ("b", u)
            # (c): K1 = K (representative), K2 ranges over C_K(u)
            s = 1 if degK[u] == d + 1 else 0
            for N2 in C:
                info["pairs"] += 1
                K2 = reattach(K, u, N2)
                deg2 = dict(K2.degree())
                z = {y: ind(own, y) - ind(N2, y) for y in K}
                for x in K:
                    if degK[x] != deg2[x] + z[x]:
                        ok_c = False
                        info["fail"] = info["fail"] or ("c-deg", u, x)
                    if x != u:
                        lhs = sum(z[y] for y in K[x])
                        theta_cons.append((lhs, z[x], s, u, x))
            # (d): K1, K2 in C_K(u) minus {K}
            proper = [N for N in C if N != own]
            for N1, N2 in itertools.product(proper, repeat=2):
                info["dpairs"] += 1
                lost1 = len([y for y in own if y not in N1])
                lost2 = len([y for y in own if y not in N2])
                if lost1 != lost2:
                    ok_d = False
                    info["fail"] = info["fail"] or ("d-lost", u)
                for x in K:
                    if degK[x] == degK[u] and ind(N1, x) != ind(N2, x):
                        ok_d = False
                        info["fail"] = info["fail"] or ("d-adj", u, x)
    # (c) theta: a single integer theta for all constraints
    cand = None
    for lhs, zx, s, u, x in theta_cons:
        if zx == 0:
            if lhs != 0:
                ok_c = False
                info["fail"] = info["fail"] or ("c-zero", u, x, lhs)
        else:
            if lhs % zx != 0:
                ok_c = False
                continue
            t = lhs // zx + s
            info["theta"].add(t)
    if len(info["theta"]) > 1:
        ok_c = False
        info["fail"] = info["fail"] or ("c-theta", sorted(info["theta"]))
    return ok_a, ok_b, ok_c, ok_d, info


def low_bound(reps_G, deck, d):
    """Child low_extension_pair conclusion for G = reps_G: every u of degree d has
    |C_G(u)| <= 2 (any three extensions agreeing with G off u have two equal)."""
    G = reps_G
    deg = dict(G.degree())
    for u in G:
        if deg[u] == d and len(extensions(G, u, deck)) > 2:
            return False, u
    return True, None


def all_bound(G, deck):
    for u in G:
        if len(extensions(G, u, deck)) > 2:
            return False, u
    return True, None
