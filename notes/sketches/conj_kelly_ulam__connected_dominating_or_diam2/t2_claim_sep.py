"""Degree-separation lemma, strong single-card form (non-vacuous: does not presuppose a deck).

If v is a vertex of G such that no neighbour u of v and non-neighbour w != v of v satisfy
deg w + 1 = deg u, then every graph obtained from the card G - v by adding one new vertex and
having the degree sequence of G is isomorphic to G.

Also checks N1: the multiset of G-degrees of the neighbours of v is the function of
(degree sequence of G, deg v, degree sequence of G - v) given by the recursion
a_{k+1} = a_k + c_k(G-v) - n_k(G) + [deg v = k],  a_0 = 0.
"""
import itertools
from collections import Counter
import networkx as nx
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t2_lib import sep_vertices, degseq


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    deg = dict(G.degree())
    nk = Counter(deg.values())
    sepv = set(sep_vertices(G))
    for v in G.nodes():
        C = G.copy(); C.remove_node(v)
        ck = Counter(d for _, d in C.degree())
        a = {0: 0}
        for k in range(0, n):
            a[k + 1] = a[k] + ck.get(k, 0) - nk.get(k, 0) + (1 if deg[v] == k else 0)
        actual = Counter(deg[u] for u in G[v])
        if any(a[k] != actual.get(k, 0) for k in range(0, n + 1)):
            return False
        if v in sepv:
            others = list(C.nodes())
            target = degseq(G)
            for S in itertools.combinations(others, deg[v]):
                H = C.copy()
                H.add_node(v)
                H.add_edges_from((v, s) for s in S)
                if degseq(H) == target and not nx.is_isomorphic(G, H):
                    return False
    return True
