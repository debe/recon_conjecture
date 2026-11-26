"""Structure test: is G a vertex-deleted subgraph of a graph X with a large orbit through the
deleted vertex?  Evidence only.

For every R in V let X_R = G + r, N(r) = R.  Printed: the largest orbit of r in Aut(X_R) over
all R (brute force, n <= 9), the sets R attaining it, and the number of twisted vertices of G
(vertices u with a card isomorphism alpha : G - u' -> G - u, alpha(N(u')) != N(u)).
Sketch t3, section 6: G = X - r with X vertex-transitive iff some R has an R-swap into every
vertex; the orbit of r in Aut(X_R) is {r} + {targets of R-swaps}."""
import itertools
import sys

from networkx.algorithms.isomorphism import GraphMatcher

from t3o_lib import *


def twisted_vertices(G):
    V = sorted(G.nodes())
    ct = {v: ctype(G, (v,)) for v in V}
    out = []
    for u in V:
        Nu = frozenset(G[u])
        B = G.subgraph([w for w in V if w != u])
        tw = False
        for u2 in V:
            if ct[u2] != ct[u]:
                continue
            A = G.subgraph([w for w in V if w != u2])
            N2 = frozenset(G[u2])
            for al in GraphMatcher(A, B).isomorphisms_iter():
                if frozenset(al[x] for x in N2) != Nu:
                    tw = True
                    break
            if tw:
                break
        if tw:
            out.append(u)
    return out


def orbit_of_r(G, R):
    n = G.number_of_nodes()
    X = G.copy()
    X.add_node(n)
    for v in R:
        X.add_edge(n, v)
    orb = {n}
    deg = dict(X.degree())
    for a in GraphMatcher(X, X).isomorphisms_iter():
        orb.add(a[n])
    return orb


for s in sys.argv[1:]:
    G = from_g6(s)
    V = sorted(G.nodes())
    n = len(V)
    best, arg = 0, []
    for k in range(n + 1):
        for R in itertools.combinations(V, k):
            o = len(orbit_of_r(G, R))
            if o > best:
                best, arg = o, [R]
            elif o == best:
                arg.append(R)
    tw = twisted_vertices(G)
    print(s, "n", n, "twisted vertices", len(tw), "of", n,
          "| largest orbit of r over all one-vertex extensions:", best, "of", n + 1,
          "| number of R attaining it:", len(arg), "| examples:", arg[:4])
