"""Looks for a K0-mate (a degree-balanced, key-preserving, non-isomorphic switch along Sw) of
structured graphs; a found mate shows the graph is outside BSK. Evidence only.
Search: the first LIMIT balanced sets in DFS order, so 'none found' decides nothing when the
limit is hit."""
import sys
import networkx as nx
import t1s_lib as L

LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 100000


def minus(G, v):
    H = G.copy(); H.remove_node(v)
    return nx.convert_node_labels_to_integers(H)


def keys(G):
    return (nx.triangles(G), nx.triangles(nx.complement(G)))


def ind(G, k):
    """Induced k-vertex subgraph counts (sorted degree sequence is a complete invariant for k <= 4)."""
    import itertools
    from collections import Counter
    c = Counter()
    for S in itertools.combinations(G.nodes(), k):
        c[tuple(sorted(d for _, d in G.subgraph(S).degree()))] += 1
    return c


shr = nx.from_edgelist([((a, b), ((a + da) % 4, (b + db) % 4)) for a in range(4) for b in range(4)
                        for da, db in [(1, 0), (0, 1), (1, 1)]])
tests = {
    "GhEJ]o": L.from_g6("GhEJ]o"),
    "GxckIs": L.from_g6("GxckIs"), "GKYZ}{": L.from_g6("GKYZ}{"), "GLvnnw": L.from_g6("GLvnnw"),
    "D6 member 2": L.from_g6("JUwkeXelqv?"),
    "GH?gmg": L.from_g6("GH?gmg"), "GHvT~o": L.from_g6("GHvT~o"),
    "Petersen - v": minus(nx.petersen_graph(), 0),
    "D6 member 1": L.from_g6("JhCkmT`kIw_"),
    "C12(1,2,3)-0": L.from_g6("J~[ww[F_}B_"),
    "C13(1,2,4)-0": L.from_g6("KbcrMZwA~c@r"),
    "K[N_ZpBVe`q{": L.from_g6("K[N_ZpBVe`q{"),
    "Paley13 - v": minus(nx.paley_graph(13).to_undirected(), 0),
    "Shrikhande - v": minus(shr, (0, 0)),
}
for name, G in tests.items():
    G = nx.convert_node_labels_to_integers(G)
    S = L.sw_pairs(G)
    sets = L.balanced_sets(G, S, limit=LIMIT)
    cG, kG = L.canon(G), keys(G)
    kept = [D for D in sets if keys(L.switch(G, D)) == kG]
    mates = [D for D in kept if L.canon(L.switch(G, D)) != cG]
    i3, i4 = ind(G, 3), ind(G, 4)
    m3 = [D for D in sets if ind(L.switch(G, D), 3) == i3 and L.canon(L.switch(G, D)) != cG]
    m4 = [D for D in m3 if ind(L.switch(G, D), 4) == i4]
    m4k = [D for D in m4 if keys(L.switch(G, D)) == kG]
    hyp = [D for D in mates if all(L.canon(L.card(L.switch(G, D), v)) == L.canon(L.card(G, v)) for v in G.nodes())]
    print(f"{name:16s} n={G.number_of_nodes():2d} |Sw|={len(S):3d} balanced sets seen={len(sets)}{'+' if len(sets) >= LIMIT else ''} "
          f"key-preserving={len(kept)} BSK-mates={len(mates)} BS3-mates={len(m3)} BS4-mates={len(m4)} BS4+keys-mates={len(m4k)} "
          f"(aligned-hypomorphic among BSK-mates: {len(hyp)})", flush=True)
