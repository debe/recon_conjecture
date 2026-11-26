"""Red-team of the generic part of the sketch in a setting where reconstruction FAILS.
Evidence only.

The unique-triple theorem T3u never uses that the structure is a graph:
  (a) D - u - v - w has a unique copy (as a 3-subset),
  (b) D - u - v, D - u - w, D - v - w are pairwise non-isomorphic,
  (c) Helly for (A_u, A_v, A_w) in Aut(D - u - v - w), stabilisers of the (out, in) attachments,
  =>  every hypomorph of D is isomorphic to D.
So on every non-reconstructible digraph no triple may satisfy (a), (b), (c), and at every triple
with (a), (b) every hypomorph must be 3-anchored at that triple.
This script finds ALL hypomorphic non-isomorphic pairs of digraphs on n = 4, 5 vertices
(brute force over labelled digraphs, numpy) and checks both statements on each.
"""
import itertools
import sys
from collections import defaultdict

import networkx as nx
import numpy as np
from networkx.algorithms.isomorphism import DiGraphMatcher


def arcs(n):
    return [(i, j) for i in range(n) for j in range(n) if i != j]


def canon_table(n):
    """canonical code (min over relabellings) for every labelled digraph on n vertices."""
    A = arcs(n)
    idx = {a: k for k, a in enumerate(A)}
    codes = np.arange(1 << len(A), dtype=np.int64)
    best = codes.copy()
    for perm in itertools.permutations(range(n)):
        new = np.zeros_like(codes)
        for k, (i, j) in enumerate(A):
            new |= ((codes >> k) & 1) << idx[(perm[i], perm[j])]
        np.minimum(best, new, out=best)
    return best


def card_codes(n, codes, v):
    """code (on n-1 vertices) of the card codes - v."""
    A = arcs(n)
    B = arcs(n - 1)
    idxB = {a: k for k, a in enumerate(B)}
    ren = {x: (x if x < v else x - 1) for x in range(n) if x != v}
    out = np.zeros_like(codes)
    for k, (i, j) in enumerate(A):
        if i == v or j == v:
            continue
        out |= ((codes >> k) & 1) << idxB[(ren[i], ren[j])]
    return out


def to_digraph(n, code):
    D = nx.DiGraph()
    D.add_nodes_from(range(n))
    for k, (i, j) in enumerate(arcs(n)):
        if (code >> k) & 1:
            D.add_edge(i, j)
    return D


def sub(D, drop):
    return nx.DiGraph(D.subgraph([w for w in D if w not in drop]))


def iso(A, B):
    return DiGraphMatcher(A, B).is_isomorphic()


def pointed_ok(T, x, pts, R, a, qts):
    A, B = sub(T, (x,)), sub(R, (a,))
    for w in A:
        A.nodes[w]["m"] = 0
    for w in B:
        B.nodes[w]["m"] = 0
    for i, w in enumerate(pts, 1):
        A.nodes[w]["m"] = i
    for i, w in enumerate(qts, 1):
        B.nodes[w]["m"] = i
    return DiGraphMatcher(A, B, node_match=lambda s, t: s["m"] == t["m"]).is_isomorphic()


def anchored3(T, p, R, q):
    for i in range(3):
        rp = [p[j] for j in range(3) if j != i]
        rq = [q[j] for j in range(3) if j != i]
        if not pointed_ok(T, p[i], rp, R, q[i], rq):
            return False
    return True


def helly(T, u, v, w):
    S = [x for x in sorted(T) if x not in (u, v, w)]
    H = sub(T, (u, v, w))
    A = list(DiGraphMatcher(H, H).isomorphisms_iter())

    def nb(z):
        return (frozenset(x for x in S if T.has_edge(z, x)), frozenset(x for x in S if T.has_edge(x, z)))

    def im(g, X):
        return (frozenset(g[x] for x in X[0]), frozenset(g[x] for x in X[1]))

    Nu, Nv, Nw = nb(u), nb(v), nb(w)
    via_w = {im(g, Nu) for g in A if im(g, Nw) == Nw}
    via_v = {im(g, Nu) for g in A if im(g, Nv) == Nv}
    triv = {im(g, Nu) for g in A if im(g, Nw) == Nw and im(g, Nv) == Nv}
    return (via_w & via_v) <= triv


def ab_triples(D):
    V = sorted(D)
    trip = list(itertools.combinations(V, 3))
    out = []
    for t in trip:
        F = sub(D, t)
        if sum(1 for s in trip if iso(sub(D, s), F)) != 1:
            continue
        u, v, w = t
        P = [sub(D, (u, v)), sub(D, (u, w)), sub(D, (v, w))]
        if iso(P[0], P[1]) or iso(P[0], P[2]) or iso(P[1], P[2]):
            continue
        out.append(t)
    return out


def us_triples(D):
    """Triples with (U) and (S) of sibling sketch t1 (class C3), digraph version:
    (U) unique copy of D - T;  (S) for each x in T with {y, z} = T - x:
    D - x - y not isomorphic to D - x - z, or an automorphism of the card D - x maps y to z."""
    V = sorted(D)
    trip = list(itertools.combinations(V, 3))
    out = []
    for t in trip:
        F = sub(D, t)
        if sum(1 for s in trip if iso(sub(D, s), F)) != 1:
            continue
        ok = True
        for x in t:
            y, z = [a for a in t if a != x]
            if not iso(sub(D, (x, y)), sub(D, (x, z))):
                continue
            if pointed_ok(D, x, [y], D, x, [z]):
                continue
            ok = False
            break
        if ok:
            out.append(t)
    return out


def main(n):
    can = canon_table(n)
    small = canon_table(n - 1)
    codes = np.arange(len(can), dtype=np.int64)
    reps = np.nonzero(can == codes)[0]
    decks = np.sort(np.stack([small[card_codes(n, reps, v)] for v in range(n)], axis=1), axis=1)
    groups = defaultdict(list)
    for code, dk in zip(reps.tolist(), map(tuple, decks.tolist())):
        groups[dk].append(code)
    bad = [g for g in groups.values() if len(g) > 1]
    print(f"n={n}: {len(reps)} digraphs, {len(bad)} deck classes with more than one digraph, "
          f"{sum(len(g) for g in bad)} non-reconstructible digraphs")
    n_ab = n_anch = n_helly = 0
    fail = []
    for g in bad:
        Ds = [to_digraph(n, c) for c in g]
        for i, D in enumerate(Ds):
            for t in (us_triples(D) if MODE == 'S' else ab_triples(D)):
                n_ab += 1
                h = helly(D, *t)
                n_helly += h
                for j, R in enumerate(Ds):
                    if i == j:
                        continue
                    anch = any(anchored3(D, t, R, q) for q in itertools.permutations(sorted(R), 3))
                    n_anch += anch
                    if not anch:
                        fail.append(("not anchored", g[i], g[j], t))
                    if h:
                        fail.append(("Helly holds on a non-reconstructible digraph", g[i], g[j], t))
    print(f"   mode {MODE}: triples with (a), (b) [mode b] or (U), (S) [mode S] on non-reconstructible digraphs: {n_ab}; "
          f"(digraph, hypomorph) pairs anchored there: {n_anch}; Helly holds at: {n_helly}")
    print("   VIOLATIONS of the generic theorem:", fail[:5] if fail else "none")


MODE = "b"

if __name__ == "__main__":
    args = sys.argv[1:]
    if args and args[0] == "S":
        MODE = "S"
        args = args[1:]
    for n in map(int, args):
        main(n)
