"""Small members of the 'split near-twin' shapes of sketch t3, section 6 (where pinned twists that move
N(x) and degrees come from).  Evidence only.   python3 t3s_neartwin.py
For each graph: non-regular?, in W3?, number of classes with (W), number of those where (K) fails (F2),
and whether some class with (W) has u in each of the listed vertex groups.
"""
import itertools

import networkx as nx

from t3s_lib import *


def half(k):
    G = nx.Graph()
    for i in range(k):
        for j in range(i, k):
            G.add_edge(("a", i), ("b", j))
    return G


def half_doubled(k, both=False):
    G = nx.Graph()
    for i in range(k):
        for j in range(i, k):
            for s in (0, 1):
                for t in ((0, 1) if both else (0,)):
                    G.add_edge(("a", i, s), ("b", j, t))
    return G


def bit(N):
    G = nx.Graph()
    G.add_nodes_from(range(N))
    for j in range(N):
        for i in range(j):
            if (j >> i) & 1:
                G.add_edge(i, j)
    return G


def subsets(k, clique=False):
    G = nx.Graph()
    U = [("u", i) for i in range(k)]
    G.add_nodes_from(U)
    for r in range(k + 1):
        for S in itertools.combinations(range(k), r):
            G.add_node(("t", S))
            for i in S:
                G.add_edge(("u", i), ("t", S))
    if clique:
        G.add_edges_from(itertools.combinations(U, 2))
    return G


FAM = {"half3": half(3), "half4": half(4), "half5": half(5), "half6": half(6),
       "half3, a doubled": half_doubled(3), "half4, a doubled": half_doubled(4),
       "half3, both doubled": half_doubled(3, True),
       "bit9": bit(9), "bit10": bit(10), "bit11": bit(11), "bit12": bit(12),
       "subsets3": subsets(3), "subsets3, U clique": subsets(3, True),
       "C5[P3] with one fibre K3": None}
for name, G in FAM.items():
    if G is None:
        continue
    names = sorted(G.nodes(), key=str)
    G = nx.convert_node_labels_to_integers(G, ordering="sorted") if all(isinstance(x, int) for x in G) else nx.relabel_nodes(G, {x: i for i, x in enumerate(names)})
    reg = len(set(d for _, d in G.degree())) == 1
    cls = classes(G)
    nW = sum(1 for c in cls if c["W"])
    nF2 = sum(1 for c in cls if c["W"] and not c["K"])
    good = [c for c in cls if c["W"] and c["K"]]
    roles = sorted({str(names[c["rep"][0]])[:6] for c in good})[:8]
    print("%-22s n=%2d regular=%s classes=%d with W=%d of which F2=%d in W3=%s  u-roles of good classes: %s" % (
        name, G.number_of_nodes(), reg, len(cls), nW, nF2, bool(good), roles), flush=True)
