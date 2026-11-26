"""The four graphs on 8 vertices outside BS_4 (evidence only): which further filter removes their mates."""
import itertools
from collections import Counter
import networkx as nx
import t1s_lib as L


def ind(G, k):
    c = Counter()
    for S in itertools.combinations(G.nodes(), k):
        c[L.canon(G.subgraph(S))] += 1
    return c


def keys(G):
    return (nx.triangles(G), nx.triangles(nx.complement(G)))


for s in ["G`oovG", "GgqPlw", "GlfP@[", "GlUjC{"]:
    G = nx.convert_node_labels_to_integers(L.from_g6(s))
    cG = L.canon(G)
    S = L.sw_pairs(G); S3 = L.sw3_pairs(G)
    sets = L.balanced_sets(G, S)
    i = {k: ind(G, k) for k in (3, 4, 5, 6)}
    kG = keys(G)
    mates = [D for D in sets if L.canon(L.switch(G, D)) != cG]
    m4 = [D for D in mates if all(ind(L.switch(G, D), k) == i[k] for k in (3, 4))]
    m4k = [D for D in m4 if keys(L.switch(G, D)) == kG]
    m4s3 = [D for D in m4 if D <= S3]
    m5 = [D for D in m4 if ind(L.switch(G, D), 5) == i[5]]
    m6 = [D for D in m5 if ind(L.switch(G, D), 6) == i[6]]
    cc = [L.canon(L.card(G, v)) for v in G.nodes()]
    print(s, "degrees", sorted(d for _, d in G.degree()), "card types", len(set(cc)),
          "connected", nx.is_connected(G), "co-connected", nx.is_connected(nx.complement(G)),
          "|Sw|", len(S), "balanced", len(sets), "BS0-mates", len(mates), "BS4-mates", len(m4),
          "with keys", len(m4k), "inside Sw3", len(m4s3), "BS5-mates", len(m5), "BS6-mates", len(m6),
          "mate sizes", sorted(len(D) for D in m4))
