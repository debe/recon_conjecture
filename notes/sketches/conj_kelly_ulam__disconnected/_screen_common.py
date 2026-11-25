"""Shared helpers for the screens of conj_kelly_ulam__disconnected children."""
import itertools
import os
import sys
from collections import Counter
from functools import lru_cache

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "search"))
from small_graphs import all_graphs, canon  # noqa: E402
import networkx as nx  # noqa: E402


def lean_connected(G):
    # Mathlib SimpleGraph.Connected = Preconnected ∧ Nonempty V
    return G.number_of_nodes() > 0 and nx.is_connected(G)


def induced_signature(G):
    """For each k < n: multiset of canonical forms of G[S], |S| = k.
    Equal signatures  <=>  for all k < n and all F on Fin k, the Lean ncard counts agree."""
    nodes = list(G.nodes())
    n = len(nodes)
    sig = []
    for k in range(n):
        c = Counter()
        for S in itertools.combinations(nodes, k):
            c[canon(nx.convert_node_labels_to_integers(G.subgraph(S)))] += 1
        sig.append(tuple(sorted(c.items())))
    return tuple(sig)


def component_signature(G):
    """Multiset of canonical forms of components (each connected, nonempty).
    Equal  <=>  for all k, all connected F on Fin k, the Lean component ncard counts agree."""
    return tuple(sorted(canon(nx.convert_node_labels_to_integers(G.subgraph(c)))
                        for c in nx.connected_components(G)))


@lru_cache(maxsize=None)
def graphs_with_sigs(n):
    return tuple((H, induced_signature(H), component_signature(H)) for H in all_graphs(n))
