"""Claims for sketch t2 on diam2_impure (structural angle). claim(G) -> bool.

S1: G, Gc connected, both diameter <= 2  ==>  G and Gc are 2-connected and
    2 <= deg v <= n-3 for every v (so block / end-vertex routes are vacuous).
S2: the class of the step is closed under complement (pure and glue are
    complement-invariant).
"""
import os
import sys

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'conj_kelly_ulam__connected_dominating_or_diam2'))
from screen_lib import has_pure_class, has_unique_copy_pair, diam2_both  # noqa: E402


def d2(G):
    return nx.is_connected(G) and nx.is_connected(nx.complement(G)) and diam2_both(G)


def claim(G):
    n = G.number_of_nodes()
    if n < 3 or not d2(G):
        return True
    Gc = nx.complement(G)
    if not (nx.is_biconnected(G) and nx.is_biconnected(Gc)):
        return False
    if any(d < 2 or d > n - 3 for _, d in G.degree()):
        return False
    if has_pure_class(G) != has_pure_class(Gc):
        return False
    if n <= 7 and has_unique_copy_pair(G) != has_unique_copy_pair(Gc):
        return False
    return True
