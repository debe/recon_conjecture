"""Non-vacuous single-pair form of Zinchenko's Lemma 6.3(b) (arXiv:2611.13728v1). Evidence only.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/debe_zinchenko_module_check.py

Let B be a module of G with 2 <= |B| <= n - 1 and let K agree with G on every pair not
contained in B. Lemma 6.3(b) with "G ~ K" replaced by what its induction uses:
  if G and K have the same induced-subgraph census for every order j <= m (m < n),
  then G[B] and K[B] have the same induced-subgraph census for every order j <= m.
(For m = n - 1 the hypothesis is "same deck" and is satisfied only by K isomorphic to G for
n <= 13, so the informative cases are m < n - 1.)
Exhaustive over all graphs G on n = 4, 5, 6 vertices, all such modules B, all K.
"""
import itertools
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import all_graphs, canon  # noqa: E402

_C = {}


def ctype(adj, S):
    S = tuple(S)
    key = (len(S), tuple(adj[a][b] for a, b in itertools.combinations(S, 2)))
    c = _C.get(key)
    if c is None:
        H = nx.Graph()
        H.add_nodes_from(range(len(S)))
        H.add_edges_from((i, j) for (i, a), (j, b) in itertools.combinations(enumerate(S), 2)
                         if adj[a][b])
        c = _C[key] = canon(H)
    return c


def census(adj, verts, j):
    return Counter(ctype(adj, S) for S in itertools.combinations(verts, j))


def main():
    for n in (4, 5, 6):
        cases = informative = 0
        for G in all_graphs(n):
            V = list(range(n))
            adj = [[1 if G.has_edge(a, b) else 0 for b in V] for a in V]
            cenG = {j: census(adj, V, j) for j in range(1, n)}
            for size in range(2, n):
                for B in itertools.combinations(V, size):
                    Bs = set(B)
                    if any(len({adj[x][b] for b in B}) > 1 for x in V if x not in Bs):
                        continue
                    pairs = list(itertools.combinations(B, 2))
                    cenGB = {j: census(adj, B, j) for j in range(1, size + 1)}
                    for bits in itertools.product((0, 1), repeat=len(pairs)):
                        K = [row[:] for row in adj]
                        for (a, b), bt in zip(pairs, bits):
                            K[a][b] = K[b][a] = bt
                        if K == adj:
                            continue
                        cases += 1
                        for m in range(1, n):
                            if census(K, V, m) != cenG[m]:
                                break
                            if m <= size and census(K, B, m) != cenGB[m]:
                                print("WITNESS", n, G.edges(), B, bits, m)
                                return
                            if m >= 2 and m <= size:
                                informative += 1
        print(f"n={n}: {cases} triples (G, B, K), {informative} (triple, m >= 2) instances "
              f"with equal censuses up to order m: NO WITNESS")


if __name__ == "__main__":
    main()
