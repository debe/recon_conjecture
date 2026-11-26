"""One-card census on a graph (evidence only): for every vertex u, how many re-attachments S of
u survive each counting constraint, against Triv(u) = images of N(u') under card isomorphisms
G - u' -> G - u (re-attachments that give a copy of G).

  python3 notes/sketches/<step>/t2_probe_onecard.py '<graph6>'

Columns: level = level balance (T2); forced = and P1-forced pairs kept (Theorem D's input);
tri = and triangles through u (K0); nbrdeg = and neighbour-degree data (t2 Lemma B / one2);
jacobi = and characteristic polynomial equal up to its constant term (Jacobi, no Tutte);
tutte = and characteristic polynomials of G' and of its complement equal (Tutte 1979);
deck = G' hypomorphic to G; triv = |Triv(u)|.
"""
import itertools
import sys
import os
from collections import Counter

import numpy as np
import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2_lib import from_g6, forced, triv, reattach, half_pure_vertices  # noqa: E402
from small_graphs import deck_key  # noqa: E402


def charpoly(G):
    A = nx.to_numpy_array(G, nodelist=sorted(G.nodes()))
    return tuple(int(round(c)) for c in np.poly(A))


def nbrdeg_data(G):
    deg = dict(G.degree())
    return Counter((deg[v], tuple(sorted(deg[w] for w in G[v]))) for v in G)


def walk_rank(G):
    A = nx.to_numpy_array(G, nodelist=sorted(G.nodes()))
    n = len(A)
    cols = [np.ones(n)]
    for _ in range(n - 1):
        cols.append(A @ cols[-1])
    W = np.array(cols).T
    # exact rank over the integers via sympy would be safer; n is small
    import sympy
    return sympy.Matrix(W.astype(int).tolist()).rank()


def main():
    G = from_g6(sys.argv[1])
    deg = dict(G.degree())
    fo = forced(G)
    dk = deck_key(G)
    cp, cpc = charpoly(G), charpoly(nx.complement(G))
    nd = nbrdeg_data(G)
    print("n", G.number_of_nodes(), "walk-matrix rank", walk_rank(G), "half-pure vertices", half_pure_vertices(G, fo))
    print("u deg level forced tri nbrdeg jacobi tutte deck triv")
    for u in sorted(G.nodes()):
        N = frozenset(G[u])
        tN = sum(1 for a, b in itertools.combinations(N, 2) if G.has_edge(a, b))
        others = [y for y in G if y != u]
        lev = {y: deg[y] - (1 if y in N else 0) for y in others}
        prof = Counter(lev[y] for y in N)
        c = Counter()
        for S in itertools.combinations(others, len(N)):
            if Counter(lev[y] for y in S) != prof:
                continue
            c["level"] += 1
            S = frozenset(S)
            if not all((y in S) == (y in N) for y in others if fo[(u, y)]):
                continue
            c["forced"] += 1
            if sum(1 for a, b in itertools.combinations(S, 2) if G.has_edge(a, b)) != tN:
                continue
            c["tri"] += 1
            H = reattach(G, u, S)
            if nbrdeg_data(H) != nd:
                continue
            c["nbrdeg"] += 1
            ch = charpoly(H)
            if ch[:-1] != cp[:-1]:
                continue
            c["jacobi"] += 1
            if ch != cp or charpoly(nx.complement(H)) != cpc:
                continue
            c["tutte"] += 1
            if deck_key(H) == dk:
                c["deck"] += 1
        print(u, deg[u], c["level"], c["forced"], c["tri"], c["nbrdeg"], c["jacobi"], c["tutte"], c["deck"], len(triv(G, u)), flush=True)


if __name__ == "__main__":
    main()
