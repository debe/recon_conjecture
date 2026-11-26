"""t1s_claim_perm.claim on structured graphs with many isomorphic cards (evidence only)."""
import networkx as nx
import t1s_lib as L
from t1s_claim_perm import claim

def minus(G, v):
    H = G.copy(); H.remove_node(v)
    return nx.convert_node_labels_to_integers(H)

tests = {s: L.from_g6(s) for s in ["GhEJ]o", "KbcrMZwA~c@r", "J~[ww[F_}B_", "JhCkmT`kIw_", "JUwkeXelqv?", "K[N_ZpBVe`q{",
                                    "GH?gmg", "GxckIs", "GKYZ}{", "GHvT~o", "GLvnnw", "Ffk}W", "Ff]mw", "Gl]o^["]}
tests["Petersen - v"] = minus(nx.petersen_graph(), 0)
tests["Petersen"] = nx.petersen_graph()
tests["Paley13 - v"] = minus(nx.paley_graph(13).to_undirected(), 0)
tests["C9(1,2) - 0"] = minus(nx.circulant_graph(9, [1, 2]), 0)
tests["C10(1,3) - 0 - 1"] = minus(minus(nx.circulant_graph(10, [1, 3]), 0), 0)
tests["K3,4"] = nx.complete_bipartite_graph(3, 4)
tests["P7"] = nx.path_graph(7)
for name, G in tests.items():
    G = nx.convert_node_labels_to_integers(G)
    print(f"{name:18s} n={G.number_of_nodes():2d} claim holds: {claim(G)}", flush=True)
