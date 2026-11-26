"""Ceiling of the first-vertex-key method (sketch debe_codegree, section on U_pi). Evidence only.

U(G; table) holds if for some vertex u every graph G' that agrees with G off u (new
neighbourhood S of u, |S| = deg u) and has the same table as G is isomorphic to G.
Tables: 'deg' = pi_a(F) (degree-typed two-deleted deck), 'key' = pi_k(F) with
k = (deg, t, tbar).  Every class obtained from pair-type counting with these keys lies in U.

  python3 .../debe_codegree_ceiling.py <graph6> [<graph6> ...]
"""
import itertools
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon  # noqa: E402
from t4_lib import degseq  # noqa: E402
from debe_codegree_lib import keys, ref_table, deg_table  # noqa: E402


def in_U(G, which, strong=False):
    """Returns (member, list of (u, number of non-isomorphic survivors))."""
    cg = canon(G)
    target = degseq(G)
    tab = deg_table(G)[0] if which == 'deg' else ref_table(G)[0]
    kms = sorted(keys(G).values())
    info = []
    member = False
    for u in sorted(G.nodes()):
        others = [w for w in G.nodes() if w != u]
        N = frozenset(G[u])
        base = G.copy()
        base.remove_node(u)
        bad = 0
        for S in itertools.combinations(others, len(N)):
            Ss = frozenset(S)
            if Ss == N:
                continue
            H = base.copy()
            H.add_node(u)
            H.add_edges_from((u, s) for s in Ss)
            if degseq(H) != target:
                continue
            if which == 'key' and sorted(keys(H).values()) != kms:
                continue
            th = deg_table(H)[0] if which == 'deg' else ref_table(H)[0]
            if th != tab:
                continue
            if strong or canon(H) != cg:
                bad += 1
        info.append((u, bad))
        if bad == 0:
            member = True
    return member, info


if __name__ == "__main__":
    for g6 in sys.argv[1:]:
        G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
        for which in ('deg', 'key'):
            m, info = in_U(G, which)
            print(g6, which, 'in U:', m, 'survivors per vertex:', [b for _, b in info], flush=True)
