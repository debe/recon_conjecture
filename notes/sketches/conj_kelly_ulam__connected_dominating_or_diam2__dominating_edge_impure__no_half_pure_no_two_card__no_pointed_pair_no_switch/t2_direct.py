"""Direct transcription of the Lean body of class C3 (t2_statement.lean) at a given (u, v, w),
clause by clause, with brute-force marked isomorphisms (no canonical forms, no t2_lib census).
Single-graph facts, evidence only.
  python3 t2_direct.py <g6> u v w        # one triple
  python3 t2_direct.py <g6>              # search all triples, print the first witness
"""
import itertools
import sys

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher


def isos(G, d1, m1, d2, m2):
    A = G.subgraph([x for x in G if x not in d1]).copy()
    B = G.subgraph([x for x in G if x not in d2]).copy()
    for x in A:
        A.nodes[x]["m"] = (m1.index(x) + 1) if x in m1 else 0
    for x in B:
        B.nodes[x]["m"] = (m2.index(x) + 1) if x in m2 else 0
    return GraphMatcher(A, B, node_match=lambda a, b: a["m"] == b["m"]).isomorphisms_iter()


def ex(G, d1, m1, d2, m2):
    return next(isos(G, d1, m1, d2, m2), None) is not None


def c3_at(G, u, v, w):
    V = sorted(G)
    deg = dict(G.degree())
    trip = [(x, y, z) for x in V for y in V for z in V if x != y and x != z and y != z]
    inA = lambda x, y, z: ex(G, (x,), (y, z), (u,), (v, w))
    A = [t for t in trip if inA(*t)]

    def window(x):
        if G.has_edge(u, v):
            return deg[x] + 1 == deg[v] or deg[x] == deg[v]
        return deg[x] == deg[v] or deg[x] == deg[v] + 1

    def inC(x, y, z):
        return any(ex(G, (x,), (y, z), (yp,), (xp, zp)) for (xp, yp, zp) in A)

    R = [(x, y, z) for (x, y, z) in trip
         if ex(G, (x, y), (z,), (u, v), (w,)) and window(x) and not inC(x, y, z)]
    if not len(R) < len(A):
        return False, len(A), len(R)
    for (x, y, z) in A:
        S = [t for t in V if t not in (x, y)]
        for g in isos(G, (x, y), (z,), (x, y), (z,)):
            triv = all(G.has_edge(x, g[t]) == G.has_edge(x, t) for t in S)
            dp = all(deg[g[t]] == deg[t] for t in S)
            if not (triv or dp):
                return False, len(A), len(R)
    return True, len(A), len(R)


G = nx.from_graph6_bytes(sys.argv[1].encode())
if len(sys.argv) > 2:
    print(sys.argv[1], sys.argv[2:], c3_at(G, *map(int, sys.argv[2:5])))
else:
    for u, v, w in itertools.permutations(sorted(G), 3):
        r = c3_at(G, u, v, w)
        if r[0]:
            print(sys.argv[1], "in C3 at", (u, v, w), "#A, #R =", r[1:])
            break
    else:
        print(sys.argv[1], "NOT in C3 (no triple)")
