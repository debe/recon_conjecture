"""Check of Lemma J5 (sketch t3): for A on m >= 4 vertices without isolated vertices, the graph
C5[A, K1, K1, K1, K1] (substitute A for one vertex of C5) is in W3 at (p3, p2, w) for every w,
where p2 is a neighbour of the substituted vertex and p3 the next vertex of the cycle.
Evidence only.   python3 t3s_c5sub.py
"""
import networkx as nx

from t3s_lib import *

AS = {"P4": nx.path_graph(4), "C4": nx.cycle_graph(4), "K4": nx.complete_graph(4), "paw": nx.Graph([(0, 1), (1, 2), (0, 2), (2, 3)]),
      "claw": nx.star_graph(3), "2K2": nx.Graph([(0, 1), (2, 3)]), "diamond": nx.Graph([(0, 1), (1, 2), (0, 2), (1, 3), (2, 3)]),
      "bull": nx.Graph([(0, 1), (1, 2), (0, 2), (0, 3), (1, 4)]), "C5": nx.cycle_graph(5), "house": nx.Graph([(0, 1), (1, 2), (2, 3), (3, 0), (0, 4), (1, 4)]),
      "P5": nx.path_graph(5), "K23": nx.complete_bipartite_graph(2, 3), "Ffk}W": nx.from_graph6_bytes(b"Ffk}W"),
      "Ff]mw": nx.from_graph6_bytes(b"Ff]mw"), "Gl]o^[": nx.from_graph6_bytes(b"Gl]o^["), "Petersen": nx.petersen_graph(),
      "Frucht": nx.frucht_graph()}
for name, A in AS.items():
    A = nx.convert_node_labels_to_integers(A)
    m = A.number_of_nodes()
    assert m >= 4 and min(d for _, d in A.degree()) >= 1
    G = A.copy()
    p2, p3, p4, p5 = m, m + 1, m + 2, m + 3
    G.add_edges_from([(p2, p3), (p3, p4), (p4, p5)])
    G.add_edges_from((a, p) for a in range(m) for p in (p2, p5))
    C = Census(G)
    by = {t: c for c in classes(G, C) for t in c["A"]}
    want = [(p3, p2, w) for w in G if w not in (p2, p3)]
    miss = [t for t in want if not (by[t]["W"] and by[t]["K"])]
    d2 = nx.diameter(G) <= 2 and nx.diameter(nx.complement(G)) <= 2
    print(name, "n =", G.number_of_nodes(), "D2 ambient:", d2, "predicted classes", len(want), "missing", len(miss), flush=True)
