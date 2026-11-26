"""Census form of Theorem C3 (and of its pair analogue C2), exhaustive for small n. Evidence only.

For every graph G on n vertices, every doubly pointed class A = class of (G-u; v, w) with the
window census  #R < #A  and the kill clause K at every member, and every graph H on n vertices
WITH THE DEGREE SEQUENCE OF G (no deck is presupposed, so the test is not vacuous):
     #R_H < #A_H   ==>   H isomorphic to G,
where A_H, C_H, R_H are computed in H against the reference types of G:
   A_H = triples of H of the type of (G-u; v, w)
   C_H = triples of H of the type of (G-y'; x', z') for some (x', y', z') in A_G
   R_H = triples (x, y, z) of H with (H-x-y; z) of the type of (G-u-v; w),
         deg_H x in {deg v - [u~v], deg v - [u~v] + 1}, not in C_H.
This is what the paper argument proves from: degree sequence + census inequality in H.
Also counts the non-isomorphic H that pass when the kill clause is dropped.

  python3 t2_check_census.py 7 [pair]
"""
import os
import sys
from collections import defaultdict, Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2_lib import *  # noqa
from small_graphs import all_graphs  # noqa: E402


def main():
    nmax = int(sys.argv[1])
    pair = len(sys.argv) > 2 and sys.argv[2] == "pair"
    for n in range(4, nmax + 1):
        graphs = [nx.convert_node_labels_to_integers(G) for G in all_graphs(n)]
        cens = [Census(G) for G in graphs]
        can = [canon(G) for G in graphs]
        by_ds = defaultdict(list)
        tab = []
        for i, G in enumerate(graphs):
            by_ds[tuple(sorted(d for _, d in G.degree()))].append(i)
            C = cens[i]
            cnt = Counter()
            port = defaultdict(Counter)
            if pair:
                for t, ty in C.c2.items():
                    cnt[ty] += 1
                    port[(C.ty[t], G.degree(t[0]))][ty] += 1
            else:
                for t, ty in C.c3.items():
                    cnt[ty] += 1
                    port[(C.p3[t], G.degree(t[0]))][ty] += 1
            tab.append((cnt, port))
        c = Counter()
        for i, G in enumerate(graphs):
            C = cens[i]
            ds = tuple(sorted(d for _, d in G.degree()))
            classes = pair_census_w(G, C) if pair else triple_census_w(G, C)
            for r, Acl in classes:
                c["census classes"] += 1
                if pair:
                    full = all(kill_all(G, C, x, y, "K") for (x, y) in Acl)
                    u, v = Acl[0]
                    ctypes = {C.c2[(y, x)] for (x, y) in Acl}
                    pt = C.ty[(u, v)]
                else:
                    full = all(kill_all(G, C, x, y, "K", fix=z) for (x, y, z) in Acl)
                    u, v, w = Acl[0]
                    ctypes = {C.c3[(y, x, z)] for (x, y, z) in Acl}
                    pt = C.p3[(u, v, w)]
                c["classes with kill K"] += full
                dv = G.degree(v) - int(G.has_edge(u, v))
                for j in by_ds[ds]:
                    cnt, port = tab[j]
                    nA = cnt[r]
                    nR = sum(k for d in (dv, dv + 1) for ty, k in port[(pt, d)].items() if ty not in ctypes)
                    if nR < nA:
                        iso = can[j] == can[i]
                        if full:
                            c["H tested (pass census)"] += 1
                            if not iso:
                                print("WITNESS", g6(G), Acl[0], g6(graphs[j]))
                                return
                        elif not iso:
                            c["non-isomorphic H passing without the kill clause"] += 1
        print("n =", n, "pair" if pair else "triple", dict(c), flush=True)
    print("NO WITNESS")


main()
