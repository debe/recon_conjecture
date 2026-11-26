"""t1 (round 13, structure sweep): switchable pairs and balanced switch sets.

Evidence only. Definitions follow t1.md section 4.

Sw(G): unordered pairs {w, y} for which there are y1, w1 outside {w, y} with
    deg_{G-w}(y1) = deg y - 1 + [w~y],  deg_{G-y}(w1) = deg w - 1 + [w~y],
    G - w - y1  isomorphic to  G - y - w1.
A switch set D (a set of pairs) is degree-balanced if for every vertex v and every degree k
    #{y : vy in D, v~y, deg y = k} = #{y : vy in D, v!~y, deg y = k}.
"""
import itertools
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "search"))
from small_graphs import canon, all_graphs, from_g6, g6, card  # noqa: E402,F401


def port_canon(G):
    """canon of G - a - b for every unordered pair."""
    out = {}
    for a, b in itertools.combinations(sorted(G.nodes()), 2):
        H = G.copy()
        H.remove_nodes_from([a, b])
        out[(a, b)] = canon(H)
    return out


def sw_pairs(G, pc=None, viewer=False):
    """Set of switchable pairs (as sorted tuples). viewer=True adds the third-vertex clause."""
    pc = pc or port_canon(G)
    V = sorted(G.nodes())
    deg = dict(G.degree())
    P = lambda a, b: pc[(a, b) if a < b else (b, a)]
    res = set()
    for w, y in itertools.combinations(V, 2):
        a = 1 if G.has_edge(w, y) else 0
        ty = deg[y] - 1 + a   # deg of y1 in G - w
        tw = deg[w] - 1 + a   # deg of w1 in G - y
        Y1 = [x for x in V if x not in (w, y) and deg[x] - (1 if G.has_edge(w, x) else 0) == ty]
        W1 = [x for x in V if x not in (w, y) and deg[x] - (1 if G.has_edge(y, x) else 0) == tw]
        if not Y1 or not W1:
            continue
        left = {P(w, x) for x in Y1}
        if any(P(y, x) in left for x in W1):
            if viewer and not viewer_ok(G, w, y, deg):
                continue
            res.add((w, y))
    return res


def viewer_ok(G, y, z, deg):
    """Third-vertex clause: every w outside {y, z} has y1 != z1 in V - w with the opposite
    adjacency and card degrees deg y - [w ~_H y], deg z - [w ~_H z] for some values of the two
    unknown H-bits."""
    a = G.has_edge(y, z)
    for w in G.nodes():
        if w in (y, z):
            continue
        ok = False
        cd = {x: deg[x] - (1 if G.has_edge(w, x) else 0) for x in G.nodes() if x != w}
        for y1, z1 in itertools.permutations(cd, 2):
            if G.has_edge(y1, z1) == a:
                continue
            if cd[y1] in (deg[y] - 1, deg[y]) and cd[z1] in (deg[z] - 1, deg[z]):
                ok = True
                break
        if not ok:
            return False
    return True


def prune(G, S, refined=True):
    """Iteratively delete pairs at a vertex/degree class that has only one colour."""
    deg = dict(G.degree()) if refined else {v: 0 for v in G.nodes()}
    S = set(S)
    changed = True
    while changed:
        changed = False
        cnt = {}
        for (w, y) in S:
            c = G.has_edge(w, y)
            cnt.setdefault((w, deg[y], c), 0)
            cnt[(w, deg[y], c)] += 1
            cnt.setdefault((y, deg[w], c), 0)
            cnt[(y, deg[w], c)] += 1
        for (w, y) in list(S):
            c = G.has_edge(w, y)
            if cnt.get((w, deg[y], not c), 0) == 0 or cnt.get((y, deg[w], not c), 0) == 0:
                S.discard((w, y))
                changed = True
    return S


def balanced_sets(G, S, limit=None, refined=True):
    """All nonempty degree-balanced subsets of S (DFS with pruning). limit: stop after that many."""
    deg = dict(G.degree()) if refined else {v: 0 for v in G.nodes()}
    S = sorted(prune(G, S, refined))
    out = []
    bal = {}

    def key(v, other):
        return (v, deg[other])

    def rec(i, chosen):
        if limit is not None and len(out) >= limit:
            return
        if i == len(S):
            if chosen and all(x == 0 for x in bal.values()):
                out.append(frozenset(chosen))
            return
        # feasibility: every nonzero balance must still be fixable by remaining pairs
        rem = S[i:]
        need = {k: v for k, v in bal.items() if v != 0}
        if need:
            cap = {}
            for (w, y) in rem:
                s = 1 if G.has_edge(w, y) else -1
                for k in (key(w, y), key(y, w)):
                    if k in need and (need[k] > 0) != (s > 0):
                        cap[k] = cap.get(k, 0) + 1
            for k, v in need.items():
                if cap.get(k, 0) < abs(v):
                    return
        w, y = S[i]
        rec(i + 1, chosen)
        s = 1 if G.has_edge(w, y) else -1
        for k in (key(w, y), key(y, w)):
            bal[k] = bal.get(k, 0) + s
        chosen.append((w, y))
        rec(i + 1, chosen)
        chosen.pop()
        for k in (key(w, y), key(y, w)):
            bal[k] -= s

    rec(0, [])
    return out


def has_balanced(G, S, refined=True):
    return bool(balanced_sets(G, S, limit=1, refined=refined))


def switch(G, D):
    H = G.copy()
    for (w, y) in D:
        if H.has_edge(w, y):
            H.remove_edge(w, y)
        else:
            H.add_edge(w, y)
    return H


def in_NS(G, viewer=False):
    return not has_balanced(G, sw_pairs(G, viewer=viewer))


def in_NSiso(G, viewer=False, limit=20000):
    """Every degree-balanced switch along switchable pairs is isomorphic to G.
    Returns True / False / None (None: more than `limit` balanced sets, not decided)."""
    S = sw_pairs(G, viewer=viewer)
    sets = balanced_sets(G, S, limit=limit)
    if len(sets) >= limit:
        return None
    c = canon(G)
    return all(canon(switch(G, D)) == c for D in sets)


def sw3_pairs(G):
    """Three-card form Sw3 (t1.md section 4.4): {w, y} with witnesses y1, w1 as in Sw such that
    for every z outside {w, y} there are w_z != y_z in V - z and z' in V - {w, y1} with
      [w_z ~ y_z] != [w ~ y],
      deg_{G-z}(w_z) in {deg w - 1, deg w},  deg_{G-z}(y_z) in {deg y - 1, deg y},
      deg_{G-w}(z')  in {deg z - 1, deg z},
      G - z - w_z - y_z  isomorphic to  G - w - y1 - z'."""
    V = sorted(G.nodes())
    deg = dict(G.degree())
    pc = port_canon(G)
    P = lambda a, b: pc[(a, b) if a < b else (b, a)]
    tc = {}

    def T(a, b, c):
        k = frozenset((a, b, c))
        if k not in tc:
            H = G.copy()
            H.remove_nodes_from(k)
            tc[k] = canon(H)
        return tc[k]

    adj = lambda a, b: 1 if G.has_edge(a, b) else 0
    res = set()
    for w, y in itertools.combinations(V, 2):
        a = adj(w, y)
        ty, tw = deg[y] - 1 + a, deg[w] - 1 + a
        Y1 = [x for x in V if x not in (w, y) and deg[x] - adj(w, x) == ty]
        W1 = [x for x in V if x not in (w, y) and deg[x] - adj(y, x) == tw]
        right = {P(y, x) for x in W1}
        found = False
        for y1 in Y1:
            if P(w, y1) not in right:
                continue
            ok = True
            for z in V:
                if z in (w, y):
                    continue
                views = set()
                for wz, yz in itertools.permutations([x for x in V if x != z], 2):
                    if adj(wz, yz) == a:
                        continue
                    if deg[wz] - adj(z, wz) in (deg[w] - 1, deg[w]) and deg[yz] - adj(z, yz) in (deg[y] - 1, deg[y]):
                        views.add(T(z, wz, yz))
                if not views:
                    ok = False
                    break
                if not any(T(w, y1, zp) in views for zp in V
                           if zp not in (w, y1) and deg[zp] - adj(w, zp) in (deg[z] - 1, deg[z])):
                    ok = False
                    break
            if ok:
                found = True
                break
        if found:
            res.add((w, y))
    return res
