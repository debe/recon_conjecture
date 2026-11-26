"""Helpers for sketch t1 (triple-card angle) of
conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch.
Evidence only, never a result."""
import importlib.util
import itertools
import os
import sys
from collections import Counter, defaultdict

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
_D2 = os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card")
sys.path.insert(0, os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2"))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "search"))
_spec = importlib.util.spec_from_file_location("d2_t3_lib", os.path.join(_D2, "t3_lib.py"))
L = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(L)
from_g6, auts, pair_types, pointed_classes = L.from_g6, L.auts, L.pair_types, L.pointed_classes
T_pairs, Tplus_pairs, card_types, pointed_iso = L.T_pairs, L.Tplus_pairs, L.card_types, L.pointed_iso
from small_graphs import canon, g6  # noqa: E402

MEMBERS = ["Ffk}W", "Ff]mw", "Gl]o^["]


def sub_type(G, T):
    """Canonical form of G - T."""
    return canon(G.subgraph([x for x in G if x not in T]))


def triple_types(G):
    return {T: sub_type(G, T) for T in itertools.combinations(sorted(G.nodes()), 3)}


def stab_data(G, u, v, w):
    R = [x for x in sorted(G.nodes()) if x not in (u, v, w)]
    A = auts(G, R)
    U = frozenset(x for x in R if G.has_edge(u, x))
    Vs = frozenset(x for x in R if G.has_edge(v, x))
    W = frozenset(x for x in R if G.has_edge(w, x))
    return R, A, U, Vs, W


def img(g, X):
    return frozenset(g[x] for x in X)


def orbit_intersection(G, u, v, w):
    """(OI) at (u; v, w): A_W.U  cap  A_V.U  ==  (A_V cap A_W).U  for the action of Aut(G-u-v-w)
    on subsets of R, U/V/W the traces of N(u), N(v), N(w)."""
    R, A, U, Vs, W = stab_data(G, u, v, w)
    oW = {img(g, U) for g in A if img(g, W) == W}
    oV = {img(g, U) for g in A if img(g, Vs) == Vs}
    oVW = {img(g, U) for g in A if img(g, Vs) == Vs and img(g, W) == W}
    return (oW & oV) == oVW


def unique_triples(G, tt=None):
    tt = tt or triple_types(G)
    cnt = Counter(tt.values())
    return [T for T, K in tt.items() if cnt[K] == 1]


def tri_class(G):
    """Triples (u, v, w) (u = the vertex re-attached) with: unique triple-deleted type,
    three pairwise non-isomorphic two-deleted types, and (OI) at (u; v, w)."""
    out = []
    for T in unique_triples(G):
        f = [sub_type(G, P) for P in itertools.combinations(T, 2)]
        if len(set(f)) < 3:
            continue
        for u in T:
            v, w = [x for x in T if x != u]
            if orbit_intersection(G, u, v, w):
                out.append((u, v, w))
    return out


def cross_possible_deg(G, u, v, w):
    """Can a card isomorphism G-u -> H-a (H hypomorphic, a ~ u, and the vertices b ~ v, c ~ w
    of H having the degrees of v, w) map v -> c, w -> b?  Degree test only:
    deg w - deg v in ({0,1} - [u~v]) cap ([u~w] - {0,1})."""
    d = G.degree(w) - G.degree(v)
    uv, uw = int(G.has_edge(u, v)), int(G.has_edge(u, w))
    return d in ({0 - uv, 1 - uv} & {uw - 0, uw - 1})


def card_swap(G, u, v, w):
    """Some automorphism of G-u swaps v and w."""
    S = [x for x in G if x != u]
    return any(g[v] == w and g[w] == v for g in auts(G, S))


def patterns_left(G, u, v, w):
    """Crossing patterns (s_u, s_v, s_w) in {S, C}^3 that survive the two-deleted-type test and
    the degree test (a crossing that is undone by a card automorphism counts as harmless and is
    dropped)."""
    p, q, r = sub_type(G, (v, w)), sub_type(G, (u, w)), sub_type(G, (u, v))
    cu = cross_possible_deg(G, u, v, w) and not card_swap(G, u, v, w)
    cv = cross_possible_deg(G, v, u, w) and not card_swap(G, v, u, w)
    cw = cross_possible_deg(G, w, u, v) and not card_swap(G, w, u, v)
    left = []
    for su, sv, sw in itertools.product("SC", repeat=3):
        if (su == "C" and not cu) or (sv == "C" and not cv) or (sw == "C" and not cw):
            continue
        ab = {r if su == "S" else q, r if sv == "S" else p}
        ac = {q if su == "S" else r, q if sw == "S" else p}
        bc = {p if sv == "S" else r, p if sw == "S" else q}
        if len(ab) == len(ac) == len(bc) == 1:
            left.append(su + sv + sw)
    return left


def deg_straight(G, x, y, z):
    """D(x; y, z): deg y != deg z and card degrees of y, z in G - x differ."""
    return G.degree(y) != G.degree(z) and \
        G.degree(y) - int(G.has_edge(x, y)) != G.degree(z) - int(G.has_edge(x, z))


def type_straight(G, x, y, z):
    """G - x - y  not isomorphic to  G - x - z."""
    return sub_type(G, (x, y)) != sub_type(G, (x, z))


def straight_reasons(G, x, y, z):
    return dict(swap=card_swap(G, x, y, z), typ=type_straight(G, x, y, z), deg=deg_straight(G, x, y, z))


def containments(G, u, v, w):
    """Which of the trace stabilizers in Aut(G-u-v-w) are contained in which."""
    R, A, U, Vs, W = stab_data(G, u, v, w)
    st = {}
    for name, X in (("u", U), ("v", Vs), ("w", W)):
        st[name] = {tuple(sorted(g.items())) for g in A if img(g, X) == X}
    return [a + "<=" + b for a in st for b in st if a != b and st[a] <= st[b]], {k: len(s) for k, s in st.items()}, len(A)


def straight(G, x, y, z):
    """(S) at x: G-x-y not isomorphic to G-x-z, or some automorphism of G-x swaps y and z."""
    return type_straight(G, x, y, z) or card_swap(G, x, y, z)


def c3_triples(G, mode="M"):
    """Ordered triples (u, v, w) witnessing the class C3:
    (U) G-{u,v,w} has a unique copy; (S) at each of u, v, w;
    mode 'M' : every automorphism of K preserving the trace of N(w) preserves that of N(u);
    mode 'OI': orbit intersection at (u; v, w)."""
    out = []
    for T in unique_triples(G):
        if not all(straight(G, x, *[t for t in T if t != x]) for x in T):
            continue
        for u, v, w in itertools.permutations(T):
            if mode == "M":
                R, A, U, Vs, W = stab_data(G, u, v, w)
                ok = all(img(g, U) == U for g in A if img(g, W) == W)
            else:
                ok = orbit_intersection(G, u, v, w)
            if ok:
                out.append((u, v, w))
    return out
