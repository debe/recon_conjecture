"""Check of Lemma C (sketch t3): for H with minimum degree >= 3, the corona H o K1 is in W3 at every
(h', v, w) with h' the pendant vertex of h, v a vertex of H other than h, w any third vertex.
Evidence only.   python3 t3s_corona.py
"""
import networkx as nx

from t3s_lib import *

HS = {"K4": nx.complete_graph(4), "K5": nx.complete_graph(5), "K5-e": nx.complete_graph(5), "W4": nx.wheel_graph(5),
      "K33": nx.complete_bipartite_graph(3, 3), "prism": nx.circular_ladder_graph(3), "W5": nx.wheel_graph(6),
      "octahedron": nx.octahedral_graph(), "K6-C6": nx.complement(nx.cycle_graph(6)),
      "W6": nx.wheel_graph(7), "K34": nx.complete_bipartite_graph(3, 4), "Q3": nx.hypercube_graph(3)}
HS["K5-e"].remove_edge(0, 1)
# a 4-regular H on 7 vertices
HS["reg4_7"] = nx.Graph([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (3, 5), (4, 6)])
for name, H in HS.items():
    H = nx.convert_node_labels_to_integers(H)
    assert min(d for _, d in H.degree()) >= 3
    nH = H.number_of_nodes()
    G = corona(H)
    got = w3_set(G)
    want = [(nH + h, v, w) for h in range(nH) for v in range(nH) if v != h for w in G if w not in (nH + h, v)]
    miss = [t for t in want if t not in got]
    print(name, "n =", G.number_of_nodes(), "|Aut H| =", len(auts(H)), "predicted classes", len(want), "missing", len(miss), miss[:3], flush=True)
