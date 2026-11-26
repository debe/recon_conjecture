"""The graphs in TW but not in NS (n = 7): their balanced switch sets (evidence only)."""
import sys
import networkx as nx
import t1s_lib as L

for s in sys.argv[1:] or ["FKc`G", "F_{Og", "Fljwo", "FFzbw"]:
    G = nx.convert_node_labels_to_integers(L.from_g6(s))
    n = G.number_of_nodes()
    deg = dict(G.degree())
    cc = [L.canon(L.card(G, v)) for v in G.nodes()]
    S = L.sw_pairs(G)
    sets = L.balanced_sets(G, S)
    print(s, "degrees", sorted(deg.values()), "card types", len(set(cc)), "|Sw|", len(S), "balanced sets", len(sets),
          "connected", nx.is_connected(G), "co-connected", nx.is_connected(nx.complement(G)))
    for D in sets:
        H = L.switch(G, D)
        common = sum(1 for v in G.nodes() if L.canon(L.card(H, v)) == cc[v])
        print("   D =", sorted(D), "red/blue", [("r" if G.has_edge(*p) else "b") for p in sorted(D)],
              "G^D iso G:", L.canon(H) == L.canon(G), "aligned common cards:", common, "of", n)
