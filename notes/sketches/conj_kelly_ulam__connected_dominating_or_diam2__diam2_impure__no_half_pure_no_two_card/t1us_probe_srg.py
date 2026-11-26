"""More strongly regular graphs minus a vertex: are they in the frozen remainder, and in US?
Evidence only.   python3 .../t1us_probe_srg.py

Graphs: complements of the n = 16 SRGs, GQ(2,2) and complement, triangular graphs T(6), T(7),
Latin-square graphs of order 5 (cyclic = Paley(25), and a non-group square), the three Chang
graphs (Seidel switchings of T(8)).  For graphs that are not vertex-transitive several deleted
vertices are tried.
"""
import itertools
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1us_lib import (classify, two_walk_linear, minus, shrikhande, rook, canon)  # noqa: E402
from t1us_stats import us_vertices  # noqa: E402
from t1us_claims import nonsingular  # noqa: E402


def triangular(m):
    V = list(itertools.combinations(range(m), 2))
    G = nx.Graph()
    G.add_nodes_from(range(len(V)))
    for (i, p), (j, q) in itertools.combinations(enumerate(V), 2):
        if set(p) & set(q):
            G.add_edge(i, j)
    return G, V


def switch(G, S):
    H = G.copy()
    S = set(S)
    for a in S:
        for b in G.nodes():
            if b in S:
                continue
            if G.has_edge(a, b):
                H.remove_edge(a, b)
            else:
                H.add_edge(a, b)
    return H


def chang():
    T, V = triangular(8)
    idx = {p: i for i, p in enumerate(V)}
    e = lambda a, b: idx[(min(a, b), max(a, b))]
    s1 = [e(0, 1), e(2, 3), e(4, 5), e(6, 7)]
    s2 = [e(0, 1), e(1, 2), e(2, 0)] + [e(3 + i, 3 + (i + 1) % 5) for i in range(5)]
    s3 = [e(i, (i + 1) % 8) for i in range(8)]
    return [switch(T, s) for s in (s1, s2, s3)]


def latin_graph(L):
    m = len(L)
    pts = [(r, c) for r in range(m) for c in range(m)]
    G = nx.Graph()
    G.add_nodes_from(range(m * m))
    for (i, p), (j, q) in itertools.combinations(enumerate(pts), 2):
        if p[0] == q[0] or p[1] == q[1] or L[p[0]][p[1]] == L[q[0]][q[1]]:
            G.add_edge(i, j)
    return G


def gq22():
    # points = 2-subsets of {0..5}, lines = perfect matchings; collinear iff disjoint
    V = list(itertools.combinations(range(6), 2))
    G = nx.Graph()
    G.add_nodes_from(range(15))
    for (i, p), (j, q) in itertools.combinations(enumerate(V), 2):
        if not set(p) & set(q):
            G.add_edge(i, j)
    return G


def orbit_reps(G):
    """one vertex per card type (a cheap stand-in for vertex orbits)."""
    seen = {}
    for v in G:
        seen.setdefault(canon(minus(G, v)), v)
    return sorted(seen.values())


def report(name, S):
    for v in orbit_reps(S):
        G = minus(S, v)
        ab = two_walk_linear(G)
        cl = classify(G)
        us = us_vertices(G) if ab else None
        sing = [u for u in G if ab and not nonsingular(G, ab[0] - G.degree(u))]
        print(name, "minus", v, "n=%d" % G.number_of_nodes(),
              "branch=%s pure=%s D=%s NF=%s N=%s glue=%s REMAINDER=%s" % (
                  cl["branch"], cl["pure"], cl["D"], cl["NF"], cl["N"], cl["glue"], cl["rem"]),
              "2wl=%s" % (ab,), "US vertices=%s" % (len(us) if us is not None else None),
              "singular vertices=%d" % len(sing), flush=True)


def main():
    cyc5 = [[(r + c) % 5 for c in range(5)] for r in range(5)]
    non5 = [[0, 1, 2, 3, 4], [1, 0, 3, 4, 2], [2, 3, 4, 0, 1], [3, 4, 1, 2, 0], [4, 2, 0, 1, 3]]
    assert all(sorted(r) == list(range(5)) for r in non5)
    assert all(sorted(non5[r][c] for r in range(5)) == list(range(5)) for c in range(5))
    jobs = [("coShrikhande", nx.complement(shrikhande())), ("Shrikhande", shrikhande()),
            ("GQ(2,2)", gq22()), ("coGQ(2,2)", nx.complement(gq22())),
            ("T(6)", triangular(6)[0]), ("T(7)", triangular(7)[0]),
            ("L3(5) non-group", latin_graph(non5)), ("L3(5) cyclic", latin_graph(cyc5))]
    jobs += [("Chang%d" % (i + 1), C) for i, C in enumerate(chang())]
    only = sys.argv[1:]
    for name, S in jobs:
        if only and not any(o in name for o in only):
            continue
        d = sorted(set(dict(S.degree()).values()))
        print("#", name, "n=%d" % S.number_of_nodes(), "degrees", d,
              "same canon as cyclic L3(5):" if name.startswith("L3(5) non") else "",
              (canon(S) == canon(latin_graph(cyc5))) if name.startswith("L3(5) non") else "", flush=True)
        report(name, S)


if __name__ == "__main__":
    main()
