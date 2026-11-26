"""Non-vacuous check of the relaxed lemmas of t2_claims.py on graphs that carry a relaxed
extension at every vertex (evidence only).

  python3 notes/sketches/<step>/t2_model_check.py

For each graph: remainder / N / N+ membership, number of relaxed extensions per vertex,
relations Z and V, and the conclusion of the descent (some low vertex has <= 1 extension).
"""
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2_lib import (from_g6, in_D2, pair_table, pure_degrees, half_pure_vertices, in_N,  # noqa: E402
                    in_Nplus, has_glue, ctype, triv, unique_copy_pairs)
import t2_claims as C  # noqa: E402


def cayley(m1, m2, conn):
    G = nx.Graph()
    V = [(a, b) for a in range(m1) for b in range(m2)]
    idx = {v: i for i, v in enumerate(V)}
    G.add_nodes_from(range(len(V)))
    for (a, b) in V:
        for (s, t) in conn:
            G.add_edge(idx[(a, b)], idx[((a + s) % m1, (b + t) % m2)])
    return G


def minus_vertex(P, v=0):
    H = nx.convert_node_labels_to_integers(P)
    H.remove_node(v)
    return nx.convert_node_labels_to_integers(H)


def graphs():
    shr = cayley(4, 4, [(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)])
    rook = cayley(4, 4, [(1, 0), (2, 0), (3, 0), (0, 1), (0, 2), (0, 3)])
    yield "Shrikhande - v", minus_vertex(shr)
    yield "co-Shrikhande - v", minus_vertex(nx.complement(shr))
    yield "rook4x4 - v", minus_vertex(rook)
    yield "Paley13 - v", minus_vertex(nx.paley_graph(13).to_undirected())
    yield "Petersen - v", minus_vertex(nx.petersen_graph())
    for s in ["GhEJ]o", "K[N_ZpBVe`q{", "KbcrMZwA~c@r", "GhdYLc"]:
        yield s, from_g6(s)


def main():
    for name, G in graphs():
        deg = dict(G.degree())
        pi, e = pair_table(G)
        rem = (in_D2(G) and not pure_degrees(G, pi, e) and not half_pure_vertices(G)
               and not in_N(G) and not has_glue(G))
        print(name, "n=%d" % G.number_of_nodes(), "degrees", sorted(Counter(deg.values()).items()),
              "D2", in_D2(G), "unique-copy pairs", len(unique_copy_pairs(G)),
              "card types", len(set(ctype(G, (v,)) for v in G)), flush=True)
        print("   remainder", rem, "| N", in_N(G), "| N+", in_Nplus(G) or "no", flush=True)
        par = C.params(G)
        if par is None:
            print("   not equitable two-degree")
            continue
        d = par[0]
        ext = {u: C.extensions(G, u, par) for u in G.nodes()}
        okZ = all(C.check_Z(G, u, z, k, par) for u, lst in ext.items() for (_, z, k) in lst)
        cnt_low = sorted(len(ext[v]) for v in G if deg[v] == d)
        cnt_high = sorted(len(ext[v]) for v in G if deg[v] == d + 1)
        tr_low = sorted(len(triv(G, v)) - 1 for v in G if deg[v] == d)
        tr_high = sorted(len(triv(G, v)) - 1 for v in G if deg[v] == d + 1)
        print("   params (d,b,e,q)", par, "Z holds", okZ)
        print("   relaxed extensions per low vertex", cnt_low, "of which isomorphic copies of G", tr_low)
        print("   relaxed extensions per high vertex", cnt_high, "of which isomorphic copies of G", tr_high)
        print("   claim (Z, V, B) holds:", C.claim(G), flush=True)


if __name__ == "__main__":
    main()
