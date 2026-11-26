"""Helpers for sketch t3 (obstruction and structure) of
conj_kelly_ulam__connected_dominating_or_diam2__dominating_edge_impure__no_half_pure_no_two_card__no_pointed_pair_no_switch.

Evidence only, never a result. Graphs are networkx graphs on 0..n-1.

k-pointed card of an ordered k-tuple p = (x, y_1, .., y_{k-1}) of distinct vertices:
(G - x; y_1, .., y_{k-1}).  Type = isomorphism class with the points kept in order.
"""
import itertools
import os
import sys
from collections import Counter, defaultdict

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "search"))
from small_graphs import canon, g6  # noqa: E402


def from_g6(s):
    return nx.from_graph6_bytes(s.encode())


def auts(G, S=None):
    H = G if S is None else G.subgraph(S)
    return list(GraphMatcher(H, H).isomorphisms_iter())


def sub(G, removed):
    return G.subgraph([w for w in G if w not in removed])


def ctype(G, removed):
    return canon(nx.convert_node_labels_to_integers(sub(G, removed)))


def pointed_isos(G, p, H, q, first_only=False):
    """Isomorphisms (G - p[0]; p[1:]) -> (H - q[0]; q[1:]) as dicts."""
    A = G.subgraph([w for w in G if w != p[0]]).copy()
    B = H.subgraph([w for w in H if w != q[0]]).copy()
    for w in A:
        A.nodes[w]["m"] = 0
    for w in B:
        B.nodes[w]["m"] = 0
    for i, w in enumerate(p[1:], 1):
        A.nodes[w]["m"] = i
    for i, w in enumerate(q[1:], 1):
        B.nodes[w]["m"] = i
    gm = GraphMatcher(A, B, node_match=lambda a, b: a["m"] == b["m"])
    if first_only:
        return gm.is_isomorphic()
    return list(gm.isomorphisms_iter())


def pointed_classes(G, k):
    """dict: ordered k-tuple -> class id of the k-pointed card type."""
    V = sorted(G.nodes())
    ct = {v: ctype(G, (v,)) for v in V}
    buckets = defaultdict(list)
    for p in itertools.permutations(V, k):
        # invariants of the pointed card only: degrees INSIDE the card, bits among the points
        key = (ct[p[0]], ctype(G, p),
               tuple(G.degree(y) - int(G.has_edge(p[0], y)) for y in p[1:]),
               tuple(int(G.has_edge(a, b)) for a, b in itertools.combinations(p[1:], 2)),
               tuple(ctype(G, (p[0], y)) for y in p[1:]))
        buckets[key].append(p)
    cid = {}
    nxt = 0
    for key in sorted(buckets, key=repr):
        reps = []
        for p in buckets[key]:
            for (r, i) in reps:
                if pointed_isos(G, p, G, r, first_only=True):
                    cid[p] = i
                    break
            else:
                reps.append((p, nxt))
                cid[p] = nxt
                nxt += 1
    return cid


def rot(p):
    return p[1:] + p[:1]


def profile(cid, p):
    """Cyclic profile of an ordered k-tuple: types of p, rot p, rot^2 p, ..."""
    out = []
    q = p
    for _ in range(len(p)):
        out.append(cid[q])
        q = rot(q)
    return tuple(out)


def full_profile(cid, p):
    """Types of all orderings, indexed by the permutation of positions."""
    k = len(p)
    return tuple(cid[tuple(p[i] for i in pi)] for pi in itertools.permutations(range(k)))


def regular_completion(G):
    """If degrees are {d-1, d} with exactly d vertices of degree d-1 (or G regular of
    degree d = 0), return X = G + r, r joined to the low vertices; else None."""
    degs = sorted(set(d for _, d in G.degree()))
    n = G.number_of_nodes()
    if len(degs) != 2 or degs[1] != degs[0] + 1:
        return None
    low = [v for v in G if G.degree(v) == degs[0]]
    if len(low) != degs[1]:
        return None
    X = G.copy()
    X.add_node(n)
    for v in low:
        X.add_edge(n, v)
    return X


def vertex_orbits(G):
    A = auts(G)
    return sorted({tuple(sorted({a[v] for a in A})) for v in G}), len(A)


def is_vt(G):
    orb, _ = vertex_orbits(G)
    return len(orb) == 1


# ---------------------------------------------------------------------------
# Triple anchors: coset triangles in Aut(F3), F3 = G - u - v - w
# ---------------------------------------------------------------------------

def triple_data(G, u, v, w):
    S = [x for x in sorted(G.nodes()) if x not in (u, v, w)]
    A = auts(G, S)
    Nu = frozenset(set(G[u]) - {v, w})
    Nv = frozenset(set(G[v]) - {u, w})
    Nw = frozenset(set(G[w]) - {u, v})
    return S, A, Nu, Nv, Nw


def img(g, X):
    return frozenset(g[x] for x in X)


def triangles(A, Nu, Nv, Nw):
    """Images g2(Nu) over coset triangles (1, g2, g3): g2 Nw = Nw, g3 Nv = Nv, g2 Nu = g3 Nu.
    Returns the set of possible new neighbourhoods N'(u) in S."""
    via_w = {img(g, Nu) for g in A if img(g, Nw) == Nw}
    via_v = {img(g, Nu) for g in A if img(g, Nv) == Nv}
    return via_w & via_v


def trivial_images(A, Nu, Nv, Nw):
    """Images h(Nu), h in A stabilising Nv and Nw (twists that are visibly trivial)."""
    return {img(g, Nu) for g in A if img(g, Nw) == Nw and img(g, Nv) == Nv}


def helly(G, u, v, w):
    """Helly condition with u as the re-attached vertex."""
    S, A, Nu, Nv, Nw = triple_data(G, u, v, w)
    return triangles(A, Nu, Nv, Nw) <= trivial_images(A, Nu, Nv, Nw)


def twist_graph(G, u, newN_S, S):
    K = G.copy()
    for x in S:
        if K.has_edge(u, x):
            K.remove_edge(u, x)
    for x in newN_S:
        K.add_edge(u, x)
    return K


def triple_types(G):
    ty = {}
    for t in itertools.combinations(sorted(G.nodes()), 3):
        ty[t] = ctype(G, t)
    return ty


def pair_types_u(G):
    return {p: ctype(G, p) for p in itertools.combinations(sorted(G.nodes()), 2)}


def T3_triples(G, mode="helly", ty3=None, ty2=None):
    """Unordered triples with the hypotheses of Theorem T3:
    (a) G - u - v - w has a unique copy;
    (b) the three two-deleted subgraphs inside the triple are pairwise non-isomorphic
        (mode 'helly') or have pairwise distinct edge numbers (mode 'edges');
    (c) Helly (for one choice of the re-attached vertex; the condition is symmetric, see sketch).
    """
    ty3 = ty3 or triple_types(G)
    ty2 = ty2 or pair_types_u(G)
    cnt = Counter(ty3.values())
    out = []
    for t, F in ty3.items():
        if cnt[F] != 1:
            continue
        u, v, w = t
        if mode == "edges":
            s = {G.degree(a) + G.degree(b) - int(G.has_edge(a, b))
                 for a, b in ((u, v), (u, w), (v, w))}
            if len(s) != 3:
                continue
        else:
            if len({ty2[(u, v)], ty2[(u, w)], ty2[(v, w)]}) != 3:
                continue
        if helly(G, u, v, w):
            out.append(t)
    return out


# ---------------------------------------------------------------------------
# Class T3 of the sketch (apex form)
# ---------------------------------------------------------------------------

def pointed2del_key(G, x, y, z, cache={}):
    """Isomorphism type of the pointed two-deleted graph (G - x - y; z)."""
    K = G.subgraph([w for w in G if w not in (x, y)]).copy()
    n = G.number_of_nodes()
    # mark z by a pendant gadget: a new vertex joined to z and to n + 2 new leaves
    hub = n
    K.add_edge(z, hub)
    for i in range(n + 2):
        K.add_edge(hub, n + 1 + i)
    return canon(nx.convert_node_labels_to_integers(K))


def cond_i(G, u, v):
    a = int(G.has_edge(u, v))
    return G.degree(u) - G.degree(v) not in (-a, 1 - a)


def T3_apex(G, cid3=None, mode="helly"):
    """Ordered triples (u, v, w) with the hypotheses of Theorem T3 (apex u):
    (a1) every (x; y, z) with (G-x-y; z) ~ (G-u-v; w) is of 2-pointed type (u; v, w) or (v; u, w);
    (a2) every (x; y, z) with (G-x-y; z) ~ (G-u-w; v) is of 2-pointed type (u; w, v) or (w; u, v);
    (b)  for (u, v) and for (u, w): degree clause (i), or the two types in (a1) resp. (a2) coincide;
    (c)  mode 'helly': every coset triangle is visibly trivial;
         mode 'iso'  : every triangle twist is isomorphic to G (weakest, for diagnostics);
         mode 'none' : census clauses only."""
    V = sorted(G.nodes())
    cid3 = cid3 or pointed_classes(G, 3)
    p2 = {}
    for (x, y, z) in cid3:
        p2[(x, y, z)] = pointed2del_key(G, x, y, z)
    by_p2 = defaultdict(set)
    for t, key in p2.items():
        by_p2[key].add(cid3[t])
    cG = canon(G)
    out = []
    for (u, v, w) in cid3:
        t1 = by_p2[p2[(u, v, w)]]
        if not t1 <= {cid3[(u, v, w)], cid3[(v, u, w)]}:
            continue
        t2 = by_p2[p2[(u, w, v)]]
        if not t2 <= {cid3[(u, w, v)], cid3[(w, u, v)]}:
            continue
        if not (cond_i(G, u, v) or cid3[(u, v, w)] == cid3[(v, u, w)]):
            continue
        if not (cond_i(G, u, w) or cid3[(u, w, v)] == cid3[(w, u, v)]):
            continue
        if mode != "none":
            S, A, Nu, Nv, Nw = triple_data(G, u, v, w)
            tri = triangles(A, Nu, Nv, Nw)
            if mode == "helly":
                if not tri <= trivial_images(A, Nu, Nv, Nw):
                    continue
            else:
                if any(canon(twist_graph(G, u, N, S)) != cG for N in tri):
                    continue
        out.append((u, v, w))
    return out
