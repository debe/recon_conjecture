"""Census form of Theorem T+ (asymmetric pointed pair), exhaustive for small n. Evidence only.

For every graph G on n vertices, every ordered pair (u, v) with the hypotheses of Theorem T+
and every graph H on n vertices with the degree sequence of G:
   if  #A_H > #(type-F pairs of H outside A_H and Chat_H)  then  H ~ G,
where A_H, Chat_H are the ordered pairs of H whose pointed card has the type of (G - u, v),
resp. of (G - y, x) for some (x, y) in A_G. No deck is presupposed.
Also counts the non-isomorphic H that pass when clause (iii) (degree-preserving automorphisms)
is dropped.

  python3 .../t3_check_census_plus.py 7
"""
import os
import sys
from collections import defaultdict, Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import *  # noqa
from small_graphs import all_graphs  # noqa: E402
from t3_check_census import pointed_iso2  # noqa: E402


def main():
    nmax = int(sys.argv[1])
    for n in range(4, nmax + 1):
        graphs = [nx.convert_node_labels_to_integers(G) for G in all_graphs(n)]
        by_ds = defaultdict(list)
        for G in graphs:
            by_ds[tuple(sorted(d for _, d in G.degree()))].append(G)
        c = Counter()
        for G in graphs:
            ty = pair_types(G)
            cid = pointed_classes(G, ty)
            members = defaultdict(list)
            for p, i in cid.items():
                members[i].append(p)
            good = set(Tplus_pairs(G, ty, cid))
            tsize = Counter(ty.values())
            cG = canon(G)
            ds = tuple(sorted(d for _, d in G.degree()))
            seen_cls = set()
            for (u, v) in ty:
                alpha = int(G.has_edge(u, v))
                if G.degree(u) - G.degree(v) in (-alpha, 1 - alpha):
                    continue
                i = cid[(u, v)]
                if i in seen_cls:
                    continue
                seen_cls.add(i)
                A = members[i]
                chat = {cid[(y, x)] for (x, y) in A}
                if not tsize[ty[(u, v)]] - len(A) - sum(len(members[j]) for j in chat) < len(A):
                    continue
                c["classes with (i),(ii)"] += 1
                full = (u, v) in good
                c["classes with all hypotheses"] += full
                reps = [members[j][0] for j in chat]
                F = ty[(u, v)]
                cu = ctype(G, (u,))
                for H in by_ds[ds]:
                    nA = nrest = 0
                    for a in H:
                        ca = ctype(H, (a,))
                        for b in H:
                            if a == b or ctype(H, (a, b)) != F:
                                continue
                            if ca == cu and pointed_iso2(G, u, v, H, a, b):
                                nA += 1
                            elif any(ctype(G, (r[0],)) == ca and pointed_iso2(G, r[0], r[1], H, a, b)
                                     for r in reps):
                                pass
                            else:
                                nrest += 1
                    if nA > nrest:
                        iso = canon(H) == cG
                        if full:
                            c["H tested"] += 1
                            if not iso:
                                print("WITNESS", g6(G), (u, v), g6(H))
                                c["WITNESS"] += 1
                        elif not iso:
                            c["non-isomorphic H when (iii) fails"] += 1
        print("n =", n, dict(c), flush=True)


if __name__ == "__main__":
    main()
