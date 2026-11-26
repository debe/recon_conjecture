"""Relaxed screen of child extension_pair_compl: the complement mechanics.  Evidence only.

For every G in NF(d) and every u: compl G is in NF(n-2-d) (n-2-d >= 0 when some degree is
d+1), deg_{compl G} u = n-1-deg_G u, and K -> compl K is a bijection C_G(u) -> C_{compl G}(u)
(so |C| is preserved and low/high swap).
"""
import os, sys
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from screen_common import deck_key, nf_ds, extensions  # noqa: E402


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    ds = nf_ds(G)
    if not ds:
        return True
    Gc = nx.complement(G)
    dsc = nf_ds(Gc)
    deg = dict(G.degree())
    for d in ds:
        if any(deg[u] == d + 1 for u in G) and (n - 2 - d) not in dsc:
            return False
    dk, dkc = deck_key(G), deck_key(Gc)
    for u in G:
        C = set(extensions(G, u, dk))
        Cc = set(extensions(Gc, u, dkc))
        others = frozenset(y for y in G if y != u)
        if {others - N for N in C} != Cc:
            return False
    return True
