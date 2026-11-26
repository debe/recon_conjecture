"""Membership of symmetric graphs in the classes of the sketch. Single-graph facts, evidence only.
  python3 t2_probe_zoo.py
Columns: number of window-census classes (pair / triple); C2, C3t, C3 witnesses.
"""
import itertools
import sys
import time

import networkx as nx

from t2_lib import *
import t1us_lib as U


def zoo():
    yield "Petersen", nx.petersen_graph()
    for m in (5, 6, 7, 8, 9, 10):
        yield f"C{m}", nx.cycle_graph(m)
    yield "Q3", nx.convert_node_labels_to_integers(nx.hypercube_graph(3))
    yield "K33", nx.complete_bipartite_graph(3, 3)
    yield "K44-pm", nx.complement(nx.convert_node_labels_to_integers(nx.cartesian_product(nx.complete_graph(4), nx.complete_graph(2))))
    yield "Paley9", U.rook(3)
    yield "Paley13", U.paley(13)
    yield "Rook4", U.rook(4)
    yield "Shrikhande", U.shrikhande()
    yield "Clebsch", U.clebsch()
    yield "Paley13-v", U.minus(U.paley(13))
    yield "Shrikhande-v", U.minus(U.shrikhande())
    yield "coShrikhande-v", U.minus(nx.complement(U.shrikhande()))
    yield "Rook4-v", U.minus(U.rook(4))
    yield "Clebsch-v", U.minus(U.clebsch())
    yield "Petersen-v", U.minus(nx.petersen_graph())
    yield "C13(1,2,4)-v", U.minus(nx.circulant_graph(13, [1, 2, 4]))
    yield "C12(1,2,3)-v", U.minus(nx.circulant_graph(12, [1, 2, 3]))
    yield "C13(1,5)", nx.circulant_graph(13, [1, 5])
    for s in U.FACE + U.N8_LEFT_DE + ["Eht?", "Eju?", "ElfO", "Ffk}W", "Ff]mw", "JhCkmT`kIw_", "JUwkeXelqv?"]:
        yield s, from_g6(s)


for name, G in zoo():
    G = nx.convert_node_labels_to_integers(G)
    t0 = time.time()
    C = Census(G)
    pw, tw = pair_census_w(G, C), triple_census_w(G, C)
    res = {
        "C2": in_pair_class_w(G, C, "K", pw),
        "C3t": in_triple_class_w(G, C, "TRIV", tw),
        "C3": in_triple_class_w(G, C, "K", tw),
    }
    print(f"{name:22s} n={G.number_of_nodes():2d} census pair/triple {len(pw):3d}/{len(tw):4d}  {res}  [{time.time()-t0:.1f}s]", flush=True)
