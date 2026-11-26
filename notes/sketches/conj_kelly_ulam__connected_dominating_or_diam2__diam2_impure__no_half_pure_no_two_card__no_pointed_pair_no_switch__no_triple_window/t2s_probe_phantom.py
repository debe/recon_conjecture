"""Details of the phantoms (with keys) of given graphs.  Evidence only.
  python3 t2s_probe_phantom.py '<graph6>' ...
For each phantom (G, F, K): copies of F in G, twisted / re-paired, and for a twisted one an anchor
(x, y), |Aut(G-x-y)|, the transfer coefficients Delta_j of the twist, cospectrality, the triangle
keys, the number of shared slices and of common cards.
"""
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa
from t2s_hunt import key_twins, keys  # noqa
from t2s_claim_transfer import deltas, charpoly  # noqa
from t2s_phantoms import keys_tri  # noqa
from t2_lib import deck  # noqa


def common_cards(G, K):
    a, b = Counter(deck(G)), Counter(deck(K))
    return sum((a & b).values())


def main():
    for s in sys.argv[1:]:
        G = nx.convert_node_labels_to_integers(from_g6(s))
        C = Census(G, triples=False)
        sl = slices(G, C)
        _, twins = key_twins(G)
        print("==", s, "n =", G.number_of_nodes(), "degrees", degseq(G), "|Aut G| =", len(auts(G)),
              "types", len(sl), "key twins", len(twins))
        for K in twins:
            K = nx.convert_node_labels_to_integers(K)
            CK = Census(K, triples=False)
            slK = slices(K, CK)
            shared = [F for F, cnt in sl.items() if slK.get(F) == cnt]
            if not shared:
                continue
            print("  phantom K =", g6(K), "| shared slices:", len(shared), "| common cards:", common_cards(G, K), "of", G.number_of_nodes(),
                  "| cospectral:", charpoly(K) == charpoly(G), "| triangle keys equal:", keys_tri(K) == keys_tri(G))
            for F in shared:
                pairsG = [p for p, t in C.ty.items() if t == F]
                swapG = {(C.c2[(x, y)], C.c2[(y, x)]): (x, y) for (x, y) in pairsG}
                anchors = [(a, b) for (a, b), t in CK.ty.items() if t == F and (CK.c2[(a, b)], CK.c2[(b, a)]) in swapG]
                print("    F: copies in G (unordered) =", len(pairsG) // 2, "| pointed types over F:", len(sl[F]),
                      "|", "TWISTED" if anchors else "RE-PAIRED")
                if anchors:
                    a, b = anchors[0]
                    x, y = swapG[(CK.c2[(a, b)], CK.c2[(b, a)])]
                    S, A, Nx, Ny, _, _ = C.pd(x, y)
                    cK = canon(K)
                    for g in A:
                        if canon(twist_graph(G, x, y, S, Nx, g)) == cK:
                            D = deltas(G, S, Nx, Ny, g)
                            k = sum(1 for t in S if g[t] in Nx and t not in Nx)
                            print("      anchor (x, y) =", (x, y), "adjacent" if G.has_edge(x, y) else "non-adjacent",
                                  "deg", (G.degree(x), G.degree(y)), "| |Aut(G-x-y)| =", len(A), "| k =", k, "| Delta =", D)
                            break


main()
