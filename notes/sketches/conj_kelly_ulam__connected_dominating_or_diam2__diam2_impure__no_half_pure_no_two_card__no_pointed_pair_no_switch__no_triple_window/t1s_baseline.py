"""Baseline (evidence only): how many graphs are determined up to isomorphism by their
induced-subgraph counts on <= 4 vertices alone (no labels, no Sw, no balance)?
Compare with BS_4.   python3 t1s_baseline.py 7"""
import itertools
import sys
from collections import Counter, defaultdict
import networkx as nx
import t1s_lib as L

n = int(sys.argv[1]) if len(sys.argv) > 1 else 7


def graphs8():
    seen = set()
    for G in L.all_graphs(7):
        G = nx.convert_node_labels_to_integers(G)
        for k in range(8):
            for N in itertools.combinations(range(7), k):
                H = G.copy(); H.add_node(7); H.add_edges_from((7, x) for x in N)
                cc = L.canon(H)
                if cc not in seen:
                    seen.add(cc)
                    yield H


def sig(G, k=4):
    c = Counter()
    for S in itertools.combinations(G.nodes(), k):
        c[tuple(sorted(d for _, d in G.subgraph(S).degree()))] += 1
    return tuple(sorted(c.items()))


cls = defaultdict(int)
tot = 0
for G in (graphs8() if n == 8 else L.all_graphs(n)):
    tot += 1
    cls[sig(G)] += 1
print(n, "graphs", tot, "determined by the 4-vertex counts alone:", sum(1 for v in cls.values() if v == 1))
