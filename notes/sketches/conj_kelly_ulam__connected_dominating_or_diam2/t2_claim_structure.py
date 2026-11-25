"""Structural facts about the D2 class (single-graph claims, non-vacuous).

S1  D2  =>  n >= 5, min degree >= 2, max degree <= n-3.
S2  D2  =>  every card of G and of the complement is connected (G and complement 2-connected).
S3  D2  <=> neither G nor its complement has a dominating edge   (for n >= 2).
S4  G, complement connected and G has a dominating edge  =>  complement has a pair at distance >= 3
    (so the two disjuncts of the frozen class are disjoint).
"""
import networkx as nx
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t2_lib import dominating_edge, diam_le2, in_D2


def claim(G):
    n = G.number_of_nodes()
    Gc = nx.complement(G)
    d2 = in_D2(G)
    # S3
    if n >= 2 and d2 != ((not dominating_edge(G)) and (not dominating_edge(Gc))):
        return False
    # S4
    if nx.is_connected(G) and nx.is_connected(Gc) and dominating_edge(G) and diam_le2(Gc):
        return False
    if not d2:
        return True
    degs = [d for _, d in G.degree()]
    if n < 5 or min(degs) < 2 or max(degs) > n - 3:
        return False
    for X in (G, Gc):
        for v in X.nodes():
            Y = X.copy(); Y.remove_node(v)
            if not nx.is_connected(Y):
                return False
    return True
