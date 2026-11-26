"""Slice ceiling PC, exhaustive for small n.  Evidence only.

slice_F(K) = multiset of pointed types (K-x, y) over the ordered pairs (x, y) with K-x-y of type F.
A graph K is an F-PHANTOM of G if K is not isomorphic to G, has the degree sequence of G and
slice_F(K) = slice_F(G).   G is in PC iff some two-deleted type F of G has no phantom.

Tests / statistics:
  T1  (inclusion W3 in PC, per type)  for every W3 witness class (u, v, w) of G (window census and
      kill K at every member, as computed by the round-12 library) the type F of G-u-v has no phantom.
  T2  same with the codegree kill (K-cd) in place of K          (class W3cd of the sketch).
  S1  number of graphs in PC, number of ambiguous slices (G, F), graphs outside PC.
  S2  dichotomy of a phantom K at F:  'twisted'  = some ordered pair (a, b) of K of type F is
      anchored: (K-a, b) ~ (G-x, y) and (K-b, a) ~ (G-y, x) for one pair (x, y) of G;
      're-paired' = none is.

  python3 t2s_slice.py 7
"""
import os
import sys
from collections import Counter, defaultdict

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa
from small_graphs import all_graphs  # noqa: E402


def main():
    nmax = int(sys.argv[1])
    nmin = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    for n in range(nmin, nmax + 1):
        graphs = [nx.convert_node_labels_to_integers(G) for G in all_graphs(n)]
        cens = [Census(G, triples=True) for G in graphs]
        can = [canon(G) for G in graphs]
        sl = [slices(G, C) for G, C in zip(graphs, cens)]
        by_ds = defaultdict(list)
        for i, G in enumerate(graphs):
            by_ds[degseq(G)].append(i)
        c = Counter()
        outside = []
        for i, G in enumerate(graphs):
            C = cens[i]
            c["graphs"] += 1
            regular = len(set(degseq(G))) == 1
            phantoms = {}
            for F, cnt in sl[i].items():
                c["slices"] += 1
                ph = [j for j in by_ds[degseq(G)] if j != i and can[j] != can[i] and sl[j].get(F) == cnt]
                phantoms[F] = ph
                if ph:
                    c["ambiguous slices"] += 1
                    # dichotomy
                    swapG = {(C.c2[(x, y)], C.c2[(y, x)]) for (x, y) in C.ty if C.ty[(x, y)] == F}
                    for j in ph:
                        CK = cens[j]
                        anchored = any((CK.c2[(a, b)], CK.c2[(b, a)]) in swapG for (a, b) in CK.ty if CK.ty[(a, b)] == F)
                        c["phantoms: twisted" if anchored else "phantoms: re-paired"] += 1
            inPC = any(not ph for ph in phantoms.values())
            c["in PC"] += inPC
            if not inPC:
                outside.append(g6(G))
            c["all slices unambiguous"] += all(not ph for ph in phantoms.values())
            # T1 / T2
            tw = triple_census_w(G, C)
            member = Counter()
            for r, Acl in tw:
                (u, v, w) = Acl[0]
                F = C.ty[(u, v)]
                flags = {
                    "K (round-12, 3 disjuncts)": all(kill_all(G, C, x, y, "K", fix=z) for (x, y, z) in Acl),
                    "K2 (Lean body of W3)": all(kill_all_cd(G, C, x, y, fix=z, mode="K2") for (x, y, z) in Acl),
                    "CD (W3cd)": all(kill_all_cd(G, C, x, y, fix=z, mode="CD") for (x, y, z) in Acl),
                    "CD3": all(kill_all_cd(G, C, x, y, fix=z, mode="CD3") for (x, y, z) in Acl),
                }
                if flags["K2 (Lean body of W3)"] and not flags["CD (W3cd)"]:
                    print("WITNESS K2 not in CD", g6(G), (u, v, w))
                    return
                for name, ok in flags.items():
                    if ok:
                        c["witness classes " + name] += 1
                        member[name] = 1
                        if phantoms[F]:
                            print("WITNESS", name, g6(G), (u, v, w), [g6(graphs[j]) for j in phantoms[F]])
                            return
                if not flags["CD3"] and not phantoms[F]:
                    c["census classes failing CD3 at an unambiguous slice"] += 1
            for name in member:
                c["graphs in class " + name] += 1
        print("n =", n, dict(c), "outside PC:", outside, flush=True)
    print("NO WITNESS")


main()
