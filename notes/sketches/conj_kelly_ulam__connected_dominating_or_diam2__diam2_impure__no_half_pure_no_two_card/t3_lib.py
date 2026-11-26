"""Shared helpers for sketch t3 of
conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card.

Evidence only, never a result. Graphs are networkx graphs on 0..n-1.

Remainder predicate (clause by clause from the frozen Lean body):
  D2      both diameters <= 2
  PURE    some degree class is pure (checked class pure_degree_class)
  GLUE    some pair with a unique copy of F = G - u - v and Aut(F) = Stab(N_v) Stab(N_u)
  LHP     level-wise half purity at some vertex (checked class level_half_pure)
  NARROW  normal form (degrees d, d+1, one card type per degree) + a card isomorphism
          that does not extend
New classes of the sketch: see filtered_glue().
"""
import itertools
import os
import sys
from collections import Counter, defaultdict

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2"))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "search"))
from t4_lib import ctype, in_D2, pair_table, pure_degrees  # noqa: E402
from small_graphs import canon, g6  # noqa: E402


def from_g6(s):
    return nx.from_graph6_bytes(s.encode())


def auts(G, S=None):
    """All automorphisms of G[S] (dicts)."""
    H = G if S is None else G.subgraph(S)
    return list(GraphMatcher(H, H).isomorphisms_iter())


def pair_types(G):
    ty = {}
    for x, y in itertools.combinations(sorted(G.nodes()), 2):
        F = ctype(G, (x, y))
        ty[(x, y)] = F
        ty[(y, x)] = F
    return ty


def deg_table(G, ty):
    pi, e = Counter(), Counter()
    for (x, y), F in ty.items():
        pi[(F, G.degree(x))] += 1
        if G.has_edge(x, y):
            e[(F, G.degree(x))] += 1
    return pi, e


def forced(G, ty, pi, e, u, y):
    """Every ordered pair of type G-u-y with first degree deg u has the adjacency of (u, y)."""
    F = ty[(u, y)]
    a = G.degree(u)
    return e[(F, a)] == (pi[(F, a)] if G.has_edge(u, y) else 0)


def has_pure(G, ty=None):
    ty = ty or pair_types(G)
    pi, e = deg_table(G, ty)
    for a in set(d for _, d in G.degree()):
        if all(e[(F, b)] in (0, c) for (F, b), c in pi.items() if b == a):
            return True
    return False


def lhp_vertices(G, ty=None):
    ty = ty or pair_types(G)
    pi, e = deg_table(G, ty)
    V = sorted(G.nodes())
    out = []
    for u in V:
        ok = True
        for j in range(len(V)):
            nb = [y for y in V if y != u and G.has_edge(u, y) and G.degree(y) == j + 1]
            nn = [y for y in V if y != u and not G.has_edge(u, y) and G.degree(y) == j]
            if all(forced(G, ty, pi, e, u, y) for y in nb):
                continue
            if all(forced(G, ty, pi, e, u, y) for y in nn):
                continue
            ok = False
            break
        if ok:
            out.append(u)
    return out


def unique_copy_pairs(G, ty=None):
    ty = ty or pair_types(G)
    cnt = Counter(F for (x, y), F in ty.items() if x < y)
    return [(x, y) for (x, y), F in ty.items() if x < y and cnt[F] == 1]


def pair_data(G, u, v):
    S = [x for x in sorted(G.nodes()) if x not in (u, v)]
    A = auts(G, S)
    Nu = frozenset(set(G[u]) - {v})
    Nv = frozenset(set(G[v]) - {u})
    return S, A, Nu, Nv


def img(g, X):
    return frozenset(g[x] for x in X)


def factor_ok(A, Nu, Nv, g):
    """exists h in A: h(Nv) = Nv and g(h(x)) in Nu <-> x in Nu  (the checked GLUE clause)."""
    for h in A:
        if img(h, Nv) != Nv:
            continue
        if all((g[h[x]] in Nu) == (x in Nu) for x in h):
            return True
    return False


def adm_deg(G, S, Nu, g):
    """T2 / degree filter at u for the twist by g:
    for all k: #{x in S: u~x, u!~g x, deg x = k+1} = #{x in S: u!~x, u~g x, deg x = k}."""
    lost = Counter(G.degree(x) - 1 for x in S if x in Nu and g[x] not in Nu)
    gained = Counter(G.degree(x) for x in S if x not in Nu and g[x] in Nu)
    return lost == gained


def adm_codeg(S, Nu, Nv, g):
    """codegree filter: #{x in S: u ~ g x and v ~ x} = #{x in S: u ~ x and v ~ x}."""
    return sum(1 for x in S if g[x] in Nu and x in Nv) == len(Nu & Nv)


def glue_pairs(G, ty=None, filt=None):
    """Unique-copy pairs (u, v) such that every g in Aut(F) passing `filt` factorizes.
    filt(G, S, Nu, Nv, g) -> bool; None = no filter (checked GLUE class)."""
    out = []
    for (u, v) in unique_copy_pairs(G, ty):
        S, A, Nu, Nv = pair_data(G, u, v)
        ok = True
        for g in A:
            if filt is not None and not filt(G, S, Nu, Nv, g):
                continue
            if not factor_ok(A, Nu, Nv, g):
                ok = False
                break
        if ok:
            out.append((u, v))
    return out


def f_deg(G, S, Nu, Nv, g):
    return adm_deg(G, S, Nu, g)


def f_deg_codeg(G, S, Nu, Nv, g):
    return adm_deg(G, S, Nu, g) and adm_codeg(S, Nu, Nv, g)


def card_types(G):
    return {v: ctype(G, (v,)) for v in G.nodes()}


def narrow(G):
    deg = dict(G.degree())
    ds = sorted(set(deg.values()))
    if not (len(ds) == 2 and ds[1] == ds[0] + 1):
        return False
    ct = card_types(G)
    if not all(ct[x] == ct[y] for x in G for y in G if deg[x] == deg[y]):
        return False
    A = auts(G)
    orbits = {frozenset(a[v] for a in A) for v in G}
    if len(orbits) != 2:
        return True
    for v in G:
        S = [x for x in G if x != v]
        if len(auts(G, S)) != sum(1 for a in A if a[v] == v):
            return True
    return False


def remainder_flags(G):
    ty = pair_types(G)
    fl = {}
    fl["D2"] = in_D2(G)
    fl["PURE"] = has_pure(G, ty)
    fl["GLUE"] = bool(glue_pairs(G, ty))
    fl["LHP"] = bool(lhp_vertices(G, ty))
    fl["NARROW"] = narrow(G)
    fl["REM"] = fl["D2"] and not (fl["PURE"] or fl["GLUE"] or fl["LHP"] or fl["NARROW"])
    return fl, ty


# ---------------------------------------------------------------------------
# Theorem T of the sketch: majority-anchored pair with degree-filtered twists
# ---------------------------------------------------------------------------

def pointed_iso(G, x, y, u, v):
    """Is there an isomorphism G - x -> G - u mapping y to v?"""
    A = G.subgraph([w for w in G if w != x]).copy()
    B = G.subgraph([w for w in G if w != u]).copy()
    for w in A:
        A.nodes[w]["m"] = int(w == y)
    for w in B:
        B.nodes[w]["m"] = int(w == v)
    return GraphMatcher(A, B, node_match=lambda a, b: a["m"] == b["m"]).is_isomorphic()


def pointed_classes(G, ty=None):
    """Partition of ordered pairs (x, y) by the isomorphism type of the pointed card (G - x, y).
    Returns dict pair -> class id."""
    ty = ty or pair_types(G)
    ct = card_types(G)
    buckets = defaultdict(list)
    for (x, y), F in ty.items():
        buckets[(ct[x], F)].append((x, y))
    cid = {}
    nxt = 0
    for key, pairs in buckets.items():
        reps = []
        for (x, y) in pairs:
            for (r, i) in reps:
                if pointed_iso(G, x, y, r[0], r[1]):
                    cid[(x, y)] = i
                    break
            else:
                reps.append(((x, y), nxt))
                cid[(x, y)] = nxt
                nxt += 1
    return cid


def deg_preserving(G, S, g):
    return all(G.degree(g[x]) == G.degree(x) for x in S)


def T_pairs(G, ty=None, cid=None, mode="star"):
    """Ordered pairs (u, v) with the hypotheses of Theorem T.
    (a+) (G-u, v) ~ (G-v, u) as pointed cards;
    (b+) #{(x,y): (G-x,y) ~ (G-u,v)}  >  #{(x,y): G-x-y ~ G-u-v, (G-x,y) !~ (G-u,v)};
    (d)  mode 'star': every g in Aut(F) preserves G-degrees on S or factorizes;
         mode 'adm' : every g in Aut(F) passing the degree filter factorizes;
         mode 'rigid': every g in Aut(F) preserves G-degrees on S."""
    ty = ty or pair_types(G)
    cid = cid or pointed_classes(G, ty)
    csize = Counter(cid.values())
    tsize = Counter(ty.values())  # ordered pairs per two-deleted type
    out = []
    for (u, v) in ty:
        if u > v:
            continue
        if cid[(u, v)] != cid[(v, u)]:
            continue
        a = csize[cid[(u, v)]]
        if not (a > tsize[ty[(u, v)]] - a):
            continue
        S, A, Nu, Nv = pair_data(G, u, v)
        ok = True
        for g in A:
            if mode == "rigid":
                if not deg_preserving(G, S, g):
                    ok = False
                    break
            elif mode == "star":
                if not (deg_preserving(G, S, g) or factor_ok(A, Nu, Nv, g)):
                    ok = False
                    break
            else:
                if adm_deg(G, S, Nu, g) and not factor_ok(A, Nu, Nv, g):
                    ok = False
                    break
        if ok:
            out.append((u, v))
    return out


# ---------------------------------------------------------------------------
# Theorem T+ of the sketch: asymmetric pointed pair (degree-asymmetric)
# ---------------------------------------------------------------------------

def Tplus_pairs(G, ty=None, cid=None):
    """Ordered pairs (u, v) with the hypotheses of Theorem T+.
    alpha = [u ~ v];  (i) deg u - deg v not in {-alpha, 1 - alpha};
    A = pointed class of (u, v);  Chat = union of the pointed classes of (y, x), (x, y) in A;
    (ii) #{ordered pairs of type F outside A and Chat} < #A;
    (iii) for every (x, y) in A every automorphism of G - x - y preserves G-degrees."""
    ty = ty or pair_types(G)
    cid = cid or pointed_classes(G, ty)
    members = defaultdict(list)
    for p, i in cid.items():
        members[i].append(p)
    tsize = Counter(ty.values())
    out = []
    done = {}
    for (u, v) in ty:
        alpha = int(G.has_edge(u, v))
        if G.degree(u) - G.degree(v) in (-alpha, 1 - alpha):
            continue
        i = cid[(u, v)]
        if i in done:
            if done[i]:
                out.append((u, v))
            continue
        A = members[i]
        chat = {cid[(y, x)] for (x, y) in A}
        size_chat = sum(len(members[j]) for j in chat)
        ok = tsize[ty[(u, v)]] - len(A) - size_chat < len(A)
        if ok:
            for (x, y) in A:
                S, Au, Nx, Ny = pair_data(G, x, y)
                if not all(deg_preserving(G, S, g) for g in Au):
                    ok = False
                    break
        done[i] = ok
        if ok:
            out.append((u, v))
    return out
