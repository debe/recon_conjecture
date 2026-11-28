"""Screen for child triangle_free_dominating_edge: in class => reconstructible.
claim_pair(G, H) is called by the tool for every hypomorphic pair (same deck); fails iff
G is in the child class and H is not isomorphic to G. Encoding faithful to the Lean
predicate (see screen_common.py); the n >= 3 guard of ClassReconstructible is in parent().
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from screen_common import parent, tf

_cache = {}
COUNT = {}


def inclass(G):
    k = nx.to_graph6_bytes(G)
    if k not in _cache:
        _cache[k] = parent(G) and tf(G)
        if _cache[k]:
            COUNT[len(G)] = COUNT.get(len(G), 0) + 1
    return _cache[k]


def claim_pair(G, H):
    if not inclass(G):
        return True
    return nx.is_isomorphic(G, H)
