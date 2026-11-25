"""Sizes of the classes proposed in debe_zinchenko.md, exhaustive n = 3..7. Evidence only.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/debe_zinchenko_stats.py

  A   at most two card types
  B   normal form: degrees in {d, d+1}, both occurring, equal degree => isomorphic cards
  N   B and some card isomorphism G - u -> G - u' does not extend to an automorphism of G
      (equivalently: Aut(G) is not transitive on a degree class, or |Aut(G - u)| > |Aut(G)_u|)
  E   B and every card isomorphism extends
"""
import os
import sys
from collections import Counter

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import all_graphs, canon, g6  # noqa: E402


def classify(G):
    deg = dict(G.degree())
    types = {}
    for v in G:
        H = G.copy()
        H.remove_node(v)
        types[v] = canon(H)
    out = set()
    if len(set(types.values())) <= 2:
        out.add("A")
    ds = sorted(set(deg.values()))
    if len(ds) == 2 and ds[1] == ds[0] + 1 and all(
            types[x] == types[y] for x in G for y in G if deg[x] == deg[y]):
        out.add("B")
        auts = list(GraphMatcher(G, G).isomorphisms_iter())
        orbits = {frozenset(a[v] for a in auts) for v in G}
        ext = len(orbits) == 2
        if ext:
            for v in G:
                H = G.copy()
                H.remove_node(v)
                if sum(1 for _ in GraphMatcher(H, H).isomorphisms_iter()) != sum(
                        1 for a in auts if a[v] == v):
                    ext = False
                    break
        out.add("E" if ext else "N")
    return out


def main():
    for n in range(3, 8):
        c = Counter()
        ex = []
        for G in all_graphs(n):
            cl = classify(G)
            both = nx.is_connected(G) and nx.is_connected(nx.complement(G))
            for k in cl:
                c[k] += 1
                if both:
                    c[k + " (G and complement connected)"] += 1
            if "E" in cl and both:
                ex.append(g6(G))
            c["all"] += 1
        print(f"n={n}:", dict(sorted(c.items())))
        if ex:
            print("   E with G and complement connected:", ex[:12])


if __name__ == "__main__":
    main()
