"""Named graphs (evidence only): former residual members and D2 test graphs."""
import sys
import networkx as nx
import t1s_lib as L

NAMED = {
    "Eht?": "Eht?", "Eju?": "Eju?", "ElfO": "ElfO",
    "Ffk}W": "Ffk}W", "Ff]mw": "Ff]mw", "Gl]o^[": "Gl]o^[",
    "GH?gmg": "GH?gmg", "GxckIs": "GxckIs", "GKYZ}{": "GKYZ}{", "GHvT~o": "GHvT~o", "GLvnnw": "GLvnnw",
    "GhEJ]o": "GhEJ]o", "GhdYLc": "GhdYLc", "GhEKzW": "GhEKzW",
    "C13(1,2,4)-0": "KbcrMZwA~c@r", "C12(1,2,3)-0": "J~[ww[F_}B_",
    "D6 member 1": "JhCkmT`kIw_", "D6 member 2": "JUwkeXelqv?",
    "K[N_ZpBVe`q{": "K[N_ZpBVe`q{",
    "ElEG": "ElEG", "E{CW": "E{CW", "EhNG": "EhNG", "EhUg": "EhUg",
}


def minus(G, v):
    H = G.copy(); H.remove_node(v)
    return nx.convert_node_labels_to_integers(H)


EXTRA = {
    "Petersen - v": minus(nx.petersen_graph(), 0),
    "Paley13 - v": minus(nx.paley_graph(13).to_undirected(), 0),
    "Shrikhande - v": minus(nx.Graph(nx.cayley_graph if False else nx.from_edgelist(
        [((a, b), ((a + da) % 4, (b + db) % 4)) for a in range(4) for b in range(4)
         for da, db in [(1, 0), (0, 1), (1, 1)]])), (0, 0)),
    "Frucht": nx.frucht_graph(),
}

for name, s in list(NAMED.items()) + list(EXTRA.items()):
    G = L.from_g6(s) if isinstance(s, str) else s
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    cards = len({L.canon(L.card(G, v)) for v in G.nodes()})
    S = L.sw_pairs(G)
    P = L.prune(G, S)
    sets = L.balanced_sets(G, S, limit=3000)
    c = L.canon(G)
    noniso = sum(1 for D in sets if L.canon(L.switch(G, D)) != c)
    print(f"{name:16s} n={n:2d} card types={cards:2d} pairs={n*(n-1)//2:3d} |Sw|={len(S):3d} core={len(P):3d} "
          f"balanced sets={'>=3000' if len(sets) >= 3000 else len(sets)} non-isomorphic switches={noniso}")
    sys.stdout.flush()
