"""Shared predicates for the t2 sketch (diameter-2 branch). Evidence only, never a result."""
import itertools
from collections import Counter
import networkx as nx


def dominating_edge(G):
    nodes = set(G.nodes())
    return any(nodes <= ({u, v} | set(G[u]) | set(G[v])) for u, v in G.edges())


def diam_le2(G):
    n = G.number_of_nodes()
    d = dict(nx.all_pairs_shortest_path_length(G, cutoff=2))
    return all(len(d[u]) == n for u in G.nodes())


def in_D2(G):
    """Second disjunct of the frozen class: every pair at distance <= 2 in G and in the complement."""
    return diam_le2(G) and diam_le2(nx.complement(G))


def is_regular(G):
    return len({d for _, d in G.degree()}) <= 1


def sep_vertices(G):
    """Vertices v such that no neighbour u and non-neighbour w != v have deg w + 1 = deg u."""
    out = []
    deg = dict(G.degree())
    for v in G.nodes():
        nb = set(G[v])
        dn = {deg[u] for u in nb}
        dw = {deg[w] + 1 for w in G.nodes() if w != v and w not in nb}
        if not (dn & dw):
            out.append(v)
    return out


def degseq(G):
    return tuple(sorted(d for _, d in G.degree()))
