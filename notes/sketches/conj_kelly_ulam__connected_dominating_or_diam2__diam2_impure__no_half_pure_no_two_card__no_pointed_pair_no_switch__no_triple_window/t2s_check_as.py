"""Class AS (anchored, switch-free) in census form, and its single-graph lemma.  Evidence only.

G is 2wl(a, b):  w2(x) = a deg(x) + b for all x  (w2(x) = sum of the degrees of the neighbours).
PIN(x, y):  the only f : V -> Q with f(x) = f(y) = 0 and (A f)(t) = (a - deg x) f(t) for all t != x
            is f = 0.     (rank computation over Q; an integer solution is a rational one)

L (single graph)  for every ordered pair (u, v), g in Aut(G-u-v) such that the twist G_g is
   2wl(a, b) with the same (a, b):  z = 1_{N(u)} - 1_{g^{-1} N(u)} on S, z(u) = z(v) = 0, satisfies
   (A z)(t) = (a - deg u) z(t) for all t != u.     Hence PIN(u, v) forces the twist to be trivial.
C (census form of Theorem AS)  for every 2wl graph G, every pointed pair class A (of (G-u, v)) with
   the pair window census #R < #A and PIN at every member, and every graph H on n vertices with the
   multiset of (deg, w2) of G:   #R_H < #A_H  ==>  H isomorphic to G.
   Also counts the non-isomorphic H that pass the census when PIN is dropped (non-vacuity).

  python3 t2s_check_as.py 7 [all]      ('all': also classes of regular graphs, every (a, b) = (0, d^2)...)
"""
import os
import sys
from collections import Counter, defaultdict
from fractions import Fraction

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa


def w2(G, x):
    return sum(G.degree(y) for y in G[x])


def two_walk(G):
    """(a, b) integers with w2 = a deg + b, for a non-regular graph; None if not 2wl.
    For a regular graph of degree d returns (d, 0)."""
    pts = sorted({(G.degree(x), w2(G, x)) for x in G})
    ds = sorted({p[0] for p in pts})
    if len(ds) == 1:
        if len(pts) != 1:
            return None
        return (ds[0], 0)
    (d1, y1), (d2, y2) = [p for p in pts if p[0] == ds[0]][0], [p for p in pts if p[0] == ds[1]][0]
    a = Fraction(y2 - y1, d2 - d1)
    b = y1 - a * d1
    if a.denominator != 1 or b.denominator != 1:
        return None
    if any(y != a * d + b for d, y in pts):
        return None
    return (int(a), int(b))


def rank(M):
    M = [[Fraction(v) for v in row] for row in M]
    r = 0
    ncol = len(M[0]) if M else 0
    for cidx in range(ncol):
        piv = next((i for i in range(r, len(M)) if M[i][cidx] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(len(M)):
            if i != r and M[i][cidx] != 0:
                fac = M[i][cidx] / M[r][cidx]
                M[i] = [p - fac * q for p, q in zip(M[i], M[r])]
        r += 1
    return r


def pin(G, a, x, y):
    V = sorted(G)
    lam = a - G.degree(x)
    rows = []
    for t in V:
        if t == x:
            continue
        rows.append([(1 if G.has_edge(t, s) else 0) - (lam if s == t else 0) for s in V])
    rows.append([1 if s == x else 0 for s in V])
    rows.append([1 if s == y else 0 for s in V])
    return rank(rows) == len(V)


def main():
    nmax = int(sys.argv[1])
    c = Counter()
    for n in range(4, nmax + 1):
        graphs = graphs_n(n)
        cens = [Census(G, triples=False) for G in graphs]
        can = [canon(G) for G in graphs]
        keys = [tuple(sorted((G.degree(x), w2(G, x)) for x in G)) for G in graphs]
        by_key = defaultdict(list)
        tab = []
        for i, G in enumerate(graphs):
            by_key[keys[i]].append(i)
            C = cens[i]
            cnt = Counter()
            port = defaultdict(Counter)
            for t, ty in C.c2.items():
                cnt[ty] += 1
                port[(C.ty[t], G.degree(t[0]))][ty] += 1
            tab.append((cnt, port))
        for i, G in enumerate(graphs):
            ab = two_walk(G)
            if ab is None:
                continue
            a, b = ab
            regular = len(set(d for _, d in G.degree())) == 1
            c["2wl graphs (n=%d)" % n] += 1
            C = cens[i]
            # L
            V = sorted(G)
            for (u, v) in C.ty:
                S, A, Nu, Nv, Ku, Kv = C.pd(u, v)
                for g in A:
                    H = twist_graph(G, u, v, S, Nu, g)
                    if two_walk(H) != ab:
                        continue
                    z = {x: int(x in Nu) - int(g[x] in Nu) for x in S}
                    z[u] = 0
                    z[v] = 0
                    c["L: 2wl twists"] += 1
                    c["L: non-trivial 2wl twists"] += any(z.values())
                    for t in V:
                        if t != u and sum(z[s] for s in G[t]) != (a - G.degree(u)) * z[t]:
                            print("WITNESS L", g6(G), (u, v), g)
                            return
                    if any(z.values()) and pin(G, a, u, v):
                        print("WITNESS L-pin", g6(G), (u, v), g)
                        return
            if regular:
                continue
            # C
            for r, Acl in pair_census_w(G, C):
                c["census classes of 2wl non-regular graphs"] += 1
                full = all(pin(G, a, x, y) for (x, y) in Acl)
                c["... with PIN at every member"] += full
                u, v = Acl[0]
                ctypes = {C.c2[(y, x)] for (x, y) in Acl}
                pt = C.ty[(u, v)]
                dv = G.degree(v) - int(G.has_edge(u, v))
                for j in by_key[keys[i]]:
                    cnt, port = tab[j]
                    nA = cnt[r]
                    nR = sum(k for d in (dv, dv + 1) for ty, k in port[(pt, d)].items() if ty not in ctypes)
                    if nR < nA:
                        iso = can[j] == can[i]
                        if full:
                            c["C: H tested (pass census)"] += 1
                            if not iso:
                                print("WITNESS C", g6(G), Acl[0], g6(graphs[j]))
                                return
                        elif not iso:
                            c["C: non-isomorphic H passing without PIN"] += 1
            if any(all(pin(G, a, x, y) for (x, y) in Acl) for r, Acl in pair_census_w(G, C)):
                c["2wl non-regular graphs in AS (n=%d)" % n] += 1
            c["2wl non-regular graphs (n=%d)" % n] += 1
        print("n <=", n, dict(c), flush=True)
    print("NO WITNESS")


main()
