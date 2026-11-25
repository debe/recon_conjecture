"""Shared helpers for sketch t4 (pair-type counts, pure degree classes, anchored gluing).

Evidence only, never a result. Graphs are networkx graphs on 0..n-1.
"""
import itertools
import os
import sys
from collections import Counter, defaultdict

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon  # noqa: E402

_CANON = {}


def ctype(G, drop):
    """Canonical form of G minus the vertices in `drop` (cached on the labelled graph)."""
    keep = [x for x in sorted(G.nodes()) if x not in drop]
    idx = {x: i for i, x in enumerate(keep)}
    bits = 0
    k = len(keep)
    for a, b in G.edges():
        if a in idx and b in idx:
            i, j = idx[a], idx[b]
            if i > j:
                i, j = j, i
            bits |= 1 << (i * k + j)
    key = (k, bits)
    c = _CANON.get(key)
    if c is None:
        c = canon(G.subgraph(keep))
        _CANON[key] = c
    return c


def diam_le2(G):
    nodes = list(G.nodes())
    for i, a in enumerate(nodes):
        Na = set(G[a])
        for b in nodes[i + 1:]:
            if b not in Na and not (Na & set(G[b])):
                return False
    return True


def in_D2(G):
    return G.number_of_nodes() >= 2 and diam_le2(G) and diam_le2(nx.complement(G))


def pair_table(G):
    """For every ordered pair (x, y), x != y: type F of G - x - y, deg x, adjacency.

    Returns (pi, e) with pi[(F, a)] = number of ordered pairs of type F with deg x = a and
    e[(F, a)] = number of those with x adjacent to y."""
    deg = dict(G.degree())
    pi, e = Counter(), Counter()
    for x, y in itertools.combinations(sorted(G.nodes()), 2):
        F = ctype(G, (x, y))
        adj = 1 if G.has_edge(x, y) else 0
        pi[(F, deg[x])] += 1
        pi[(F, deg[y])] += 1
        e[(F, deg[x])] += adj
        e[(F, deg[y])] += adj
    return pi, e


def pure_degrees(G, pi=None, e=None):
    """Degrees a (occurring in G) such that every type F is pure for the class D_a:
    all ordered pairs (x, y) of type F with deg x = a are adjacent, or none is."""
    if pi is None:
        pi, e = pair_table(G)
    bad = set()
    for (F, a), cnt in pi.items():
        if 0 < e[(F, a)] < cnt:
            bad.add(a)
    return sorted(set(d for _, d in G.degree()) - bad)


def star_vertices(G):
    """Vertices v with condition (star) of t1 / degree separation of t2."""
    deg = dict(G.degree())
    out = []
    for v in G.nodes():
        nb = set(G[v])
        dn = {deg[u] for u in nb}
        dw = {deg[w] + 1 for w in G.nodes() if w != v and w not in nb}
        if not (dn & dw):
            out.append(v)
    return out


def degseq(G):
    return tuple(sorted(d for _, d in G.degree()))


def automorphisms(G, S):
    """All automorphisms of G[S] as dicts (brute force; |S| <= 7)."""
    S = sorted(S)
    adj = {x: frozenset(set(G[x]) & set(S)) for x in S}
    dg = {x: len(adj[x]) for x in S}
    out = []

    def rec(i, m, used):
        if i == len(S):
            out.append(dict(m))
            return
        x = S[i]
        for y in S:
            if y in used or dg[y] != dg[x]:
                continue
            ok = True
            for j in range(i):
                z = S[j]
                if (z in adj[x]) != (m[z] in adj[y]):
                    ok = False
                    break
            if ok:
                m[x] = y
                used.add(y)
                rec(i + 1, m, used)
                used.discard(y)
                del m[x]

    rec(0, {}, set())
    return out


def factorizes(G, u, v):
    """Aut(F) = Stab(N_u) * Stab(N_v) for F = G - u - v, N_x = N(x) minus {u, v}.

    Equivalent: Stab(N_u) is transitive on the Aut(F)-orbit of N_v."""
    S = [x for x in G.nodes() if x not in (u, v)]
    A = automorphisms(G, S)
    Nu = frozenset(set(G[u]) - {v})
    Nv = frozenset(set(G[v]) - {u})
    orbit = {frozenset(g[x] for x in Nv) for g in A}
    stab_u = [g for g in A if frozenset(g[x] for x in Nu) == Nu]
    reach = {frozenset(g[x] for x in Nv) for g in stab_u}
    return reach == orbit, len(A), len(orbit)


def gap_anchored_pairs(G):
    """Pairs (u, v), u < v, such that every other vertex has degree at least 2 away from
    deg u and from deg v (anchor A3 of the sketch)."""
    deg = dict(G.degree())
    out = []
    nodes = sorted(G.nodes())
    for u, v in itertools.combinations(nodes, 2):
        if all(abs(deg[x] - deg[u]) >= 2 and abs(deg[x] - deg[v]) >= 2
               for x in nodes if x not in (u, v)):
            out.append((u, v))
    return out


def typed_anchored_pairs(G, pi=None, e=None):
    """Ordered pairs (u, v) meeting anchor A2: writing F = G - u - v, a = deg u and
    c = deg u - [u ~ v], every ordered pair (x, y) of type F with deg x = a or
    deg x - [x ~ y] = c is (u, v) or (v, u)."""
    deg = dict(G.degree())
    nodes = sorted(G.nodes())
    by_type = defaultdict(list)
    for x, y in itertools.permutations(nodes, 2):
        by_type[ctype(G, (x, y))].append((x, y))
    out = []
    for F, pairs in by_type.items():
        for (u, v) in pairs:
            a = deg[u]
            c = a - (1 if G.has_edge(u, v) else 0)
            ok = True
            for (x, y) in pairs:
                if (x, y) in ((u, v), (v, u)):
                    continue
                if deg[x] == a or deg[x] - (1 if G.has_edge(x, y) else 0) == c:
                    ok = False
                    break
            if ok:
                out.append((u, v))
    # both directions are needed
    s = set(out)
    return [(u, v) for (u, v) in out if u < v and (v, u) in s]


def unique_copy_pairs(G):
    """Unordered pairs {u, v} such that G - u - v has a unique induced copy (anchor A1)."""
    cnt = Counter()
    where = {}
    for x, y in itertools.combinations(sorted(G.nodes()), 2):
        F = ctype(G, (x, y))
        cnt[F] += 1
        where[F] = (x, y)
    return [where[F] for F, c in cnt.items() if c == 1]
