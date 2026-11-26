"""Census form of Theorem T, exhaustive for small n. Evidence only.

For every graph G on n vertices and every pair (u, v) with the hypotheses of Theorem T
(mode given on the command line), and for every graph H on n vertices with the degree
sequence of G:  if  #A_H > #B_H  then  H ~ G,  where
   A_H = {(a, b) : (H - a, b) ~ (G - u, v) as pointed graphs},
   B_H = {(a, b) : H - a - b ~ G - u - v} minus A_H.
No deck is presupposed, so the test is not vacuous (all hypomorphic pairs on n <= 7 vertices
are isomorphic anyway).  Also counts how often the conclusion would fail WITHOUT the degree
hypothesis on Aut(F) (pairs with (a+), (b+) only), to show that clause (d) is doing work.

  python3 .../t3_check_census.py 7 star
"""
import os
import sys
from collections import defaultdict, Counter

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import *  # noqa
from small_graphs import all_graphs  # noqa: E402


def pointed_iso2(G, u, v, H, a, b):
    A = G.subgraph([w for w in G if w != u]).copy()
    B = H.subgraph([w for w in H if w != a]).copy()
    for w in A:
        A.nodes[w]["m"] = int(w == v)
    for w in B:
        B.nodes[w]["m"] = int(w == b)
    return GraphMatcher(A, B, node_match=lambda p, q: p["m"] == q["m"]).is_isomorphic()


def census(G, u, v, H):
    cu = ctype(G, (u,))
    F = ctype(G, (u, v))
    nA = nB = 0
    for a in H:
        ca = ctype(H, (a,))
        for b in H:
            if a == b or ctype(H, (a, b)) != F:
                continue
            if ca == cu and pointed_iso2(G, u, v, H, a, b):
                nA += 1
            else:
                nB += 1
    return nA, nB


def main():
    nmax = int(sys.argv[1])
    mode = sys.argv[2] if len(sys.argv) > 2 else "star"
    for n in range(4, nmax + 1):
        graphs = [nx.convert_node_labels_to_integers(G) for G in all_graphs(n)]
        by_ds = defaultdict(list)
        for G in graphs:
            by_ds[tuple(sorted(d for _, d in G.degree()))].append(G)
        c = Counter()
        for G in graphs:
            ty = pair_types(G)
            cid = pointed_classes(G, ty)
            good = set(T_pairs(G, ty, cid, mode))
            csize = Counter(cid.values())
            tsize = Counter(ty.values())
            cG = canon(G)
            ds = tuple(sorted(d for _, d in G.degree()))
            for (u, v) in ty:
                if u > v or cid[(u, v)] != cid[(v, u)]:
                    continue
                a = csize[cid[(u, v)]]
                if not a > tsize[ty[(u, v)]] - a:
                    continue
                c["pairs with (a+),(b+)"] += 1
                full = (u, v) in good
                c["pairs with all hypotheses"] += full
                for H in by_ds[ds]:
                    nA, nB = census(G, u, v, H)
                    if nA > nB:
                        iso = canon(H) == cG
                        if full:
                            c["H tested"] += 1
                            if not iso:
                                print("WITNESS", g6(G), (u, v), g6(H))
                                c["WITNESS"] += 1
                        elif not iso:
                            c["non-isomorphic H when (d) fails"] += 1
        print("n =", n, mode, dict(c), flush=True)


if __name__ == "__main__":
    main()
