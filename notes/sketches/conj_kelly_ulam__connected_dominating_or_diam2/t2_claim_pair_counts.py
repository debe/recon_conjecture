"""Pair-count identities behind 'D2 is recognizable' (not needed for the reduction).

q_j(G) = number of non-adjacent pairs with exactly j common neighbours. For every graph:
    sum over x of q_j(G - x) = (n - 2 - j) q_j(G) + (j + 1) q_{j+1}(G)      (0 <= j <= n - 3).
The solution space of this system is one-dimensional (kernel (-1)^j C(n-2, j)); it is pinned by
q_{n-2}(G), the number of K2 components of the complement, which is 0 when the complement is
connected and n >= 3.
"""
import itertools
from collections import Counter
import networkx as nx


def q(G):
    c = Counter()
    for u, v in itertools.combinations(G.nodes(), 2):
        if not G.has_edge(u, v):
            c[len(set(G[u]) & set(G[v]))] += 1
    return c


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    qG = q(G)
    tot = Counter()
    for x in G.nodes():
        C = G.copy(); C.remove_node(x)
        tot.update(q(C))
    for j in range(0, n - 2):
        if tot[j] != (n - 2 - j) * qG[j] + (j + 1) * qG[j + 1]:
            return False
    if nx.is_connected(nx.complement(G)) and qG[n - 2] != 0:
        return False
    return True
