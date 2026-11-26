"""Instance counts for the relaxed claims of t2_claims.py on structured equitable two-degree
graphs (evidence only):  python3 notes/sketches/<step>/t2_stats.py
Families: strongly regular graphs minus a vertex, complete bipartite minus a vertex, the face
members of t4, plus every graph on 8 vertices (vertex-extension list of t1_stats)."""
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import t2_claims as C  # noqa: E402
from t2_model_check import cayley, minus_vertex  # noqa: E402
from t2_lib import from_g6  # noqa: E402


def families():
    for q in (5, 9, 13, 17):
        yield "Paley%d-v" % q, minus_vertex(nx.paley_graph(q).to_undirected())
    for m in (3, 4):
        yield "rook%d-v" % m, minus_vertex(nx.cartesian_product(nx.complete_graph(m), nx.complete_graph(m)))
    for m in (5, 6):
        T = nx.line_graph(nx.complete_graph(m))
        yield "T(%d)-v" % m, minus_vertex(nx.convert_node_labels_to_integers(T))
        yield "coT(%d)-v" % m, minus_vertex(nx.convert_node_labels_to_integers(nx.complement(T)))
    for m in (3, 4, 5):
        yield "K%d,%d-v" % (m, m), minus_vertex(nx.complete_bipartite_graph(m, m))
    shr = cayley(4, 4, [(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)])
    yield "Shrikhande-v", minus_vertex(shr)
    yield "coShrikhande-v", minus_vertex(nx.complement(shr))
    cl = nx.Graph()
    import itertools
    V = list(itertools.product((0, 1), repeat=4))
    for a in V:
        for b in V:
            dist = sum(x != y for x, y in zip(a, b))
            if dist in (1, 4):
                cl.add_edge(V.index(a), V.index(b))
    yield "Clebsch-v", minus_vertex(cl)
    for s in ["GhEJ]o", "K[N_ZpBVe`q{", "OpyHvCM]IFJpsMdwu`pJp"]:
        yield s, from_g6(s)


def main():
    for name, G in families():
        G = nx.convert_node_labels_to_integers(G)
        before = dict(C.STATS)
        ok = C.claim(G)
        delta = {k: C.STATS[k] - before[k] for k in C.STATS if C.STATS[k] != before[k]}
        print(name, "n=%d" % G.number_of_nodes(), "claim", ok, delta, flush=True)
        if not ok:
            print("WITNESS", name)
    if len(sys.argv) > 1 and sys.argv[1] == "8":
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                                        "conj_kelly_ulam__connected_dominating_or_diam2"))
        from t1_stats import graphs
        before = dict(C.STATS)
        bad = 0
        for G in graphs(8):
            if not C.claim(G):
                bad += 1
                print("WITNESS n=8", nx.to_graph6_bytes(G, header=False))
        print("n=8 exhaustive: witnesses", bad, {k: C.STATS[k] - before[k] for k in C.STATS})


if __name__ == "__main__":
    main()
