"""What separates a phantom from G?  Exhaustive small n.  Evidence only.

For every graph G on n vertices, every two-deleted type F of G and every F-phantom K
(K not isomorphic to G, degree sequence of G, slice_F(K) = slice_F(G)):
  - is K a twist of G (anchored at a pair of type F) or re-paired?
  - does K have the multiset of (deg, w2) of G?            (W1 of round-11 t1: card-tied)
  - does K have the multiset of (deg, t, tbar) of G?        (K0 of debe_codegree: card-tied, n >= 4)
  - number of two-deleted types F' of G with slice_F'(K) = slice_F'(G)
  - is F a unique copy in G (one unordered pair)?
Prints per-n counters and the phantoms that survive both key filters.

  python3 t2s_phantoms.py 7
  python3 t2s_phantoms.py 8 8      (n = 8 by one-vertex extension of the atlas)
"""
import os
import sys
from collections import Counter, defaultdict

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa
from small_graphs import all_graphs  # noqa: E402


def keys_w2(G):
    return sorted((G.degree(x), sum(G.degree(y) for y in G[x])) for x in G)


def keys_tri(G):
    out = []
    for x in G:
        N = set(G[x])
        t = sum(1 for a in N for b in N if a < b and G.has_edge(a, b))
        M = set(G) - N - {x}
        tb = sum(1 for a in M for b in M if a < b and not G.has_edge(a, b))
        out.append((G.degree(x), t, tb))
    return sorted(out)


def main():
    nmax = int(sys.argv[1])
    nmin = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    for n in range(nmin, nmax + 1):
        graphs = graphs_n(n)
        print('graphs:', len(graphs), flush=True)
        cens = [Census(G, triples=False) for G in graphs]
        can = [canon(G) for G in graphs]
        sl = [slices(G, C) for G, C in zip(graphs, cens)]
        kw = [keys_w2(G) for G in graphs]
        kt = [keys_tri(G) for G in graphs]
        by_ds = defaultdict(list)
        for i, G in enumerate(graphs):
            by_ds[degseq(G)].append(i)
        c = Counter()
        shared = Counter()
        survivors = []
        for i, G in enumerate(graphs):
            C = cens[i]
            for F, cnt in sl[i].items():
                for j in by_ds[degseq(G)]:
                    if can[j] == can[i] or sl[j].get(F) != cnt:
                        continue
                    c["phantoms (G, F, K)"] += 1
                    swapG = {(C.c2[(x, y)], C.c2[(y, x)]) for (x, y) in C.ty if C.ty[(x, y)] == F}
                    CK = cens[j]
                    anchored = any((CK.c2[(a, b)], CK.c2[(b, a)]) in swapG for (a, b) in CK.ty if CK.ty[(a, b)] == F)
                    c["twisted (anchored at a pair of type F)" if anchored else "re-paired (no anchored pair)"] += 1
                    c["F unique copy"] += sum(cnt.values()) == 2
                    c["same (deg, w2) multiset"] += kw[j] == kw[i]
                    c["same (deg, t, tbar) multiset"] += kt[j] == kt[i]
                    both = kw[j] == kw[i] and kt[j] == kt[i]
                    c["same both"] += both
                    k = sum(1 for F2, cnt2 in sl[i].items() if sl[j].get(F2) == cnt2)
                    shared[k] += 1
                    if both:
                        survivors.append((g6(G), g6(graphs[j]), k, len(sl[i])))
        print("n =", n, dict(c), "| number of shared slices:", dict(sorted(shared.items())), flush=True)
        for s in survivors[:12]:
            print("   survivor (G, K, shared slices, slices of G):", s)


if __name__ == "__main__":
    main()
