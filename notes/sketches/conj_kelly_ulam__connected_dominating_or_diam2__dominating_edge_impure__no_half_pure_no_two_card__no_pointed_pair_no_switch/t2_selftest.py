"""Self-test of the canonical-form census against brute-force marked isomorphism (GraphMatcher).
Evidence about the scripts only.   python3 t2_selftest.py
"""
import itertools
import random
from collections import defaultdict

import networkx as nx

from t2_lib import *
from small_graphs import all_graphs

rng = random.Random(3)
checked = 0
graphs = [nx.convert_node_labels_to_integers(G) for G in all_graphs(6)]
graphs += rng.sample([nx.convert_node_labels_to_integers(G) for G in all_graphs(7)], 60)
graphs += [from_g6(s) for s in ["Ffk}W", "Ff]mw", "Gl]o^[", "KbcrMZwA~c@r"]]
for G in graphs:
    C = Census(G)
    V = sorted(G)
    # pairs: canonical classes vs t3_lib.pointed_classes
    cid = pointed_classes(G, C.ty)
    a, b = defaultdict(set), defaultdict(set)
    for p in cid:
        a[cid[p]].add(p)
        b[C.c2[p]].add(p)
    assert set(map(frozenset, a.values())) == set(map(frozenset, b.values())), g6(G)
    # triples and pointed ports: random pairs of triples
    T = list(C.c3)
    for _ in range(40 if len(V) <= 8 else 15):
        s, t = rng.choice(T), rng.choice(T)
        same = marked_iso_exists(G, (s[0],), (s[1], s[2]), (t[0],), (t[1], t[2]))
        assert same == (C.c3[s] == C.c3[t]), (g6(G), s, t)
        same = marked_iso_exists(G, (s[0], s[1]), (s[2],), (t[0], t[1]), (t[2],))
        assert same == (C.p3[s] == C.p3[t]), (g6(G), s, t)
        checked += 2
print("self-test passed:", len(graphs), "graphs,", checked, "random triple comparisons")
