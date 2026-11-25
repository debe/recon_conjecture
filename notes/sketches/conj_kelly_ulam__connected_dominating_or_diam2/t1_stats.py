"""Sizes of the sub-classes of sketch t1, exhaustively for n <= 8. Evidence only.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t1_stats.py [n_max]

n = 8 is built by adding one vertex to every 7-vertex graph and deduplicating with the
tool's canonical form (no geng needed); the count 12346 is checked against OEIS A000088.

Columns
  P     parent class (G, co-G connected; dominating edge or both diameters <= 2)
  D3    G and co-G both have a dominating edge            (= diam G = diam co-G = 3)
  D2    co-G connected, G has a dominating edge, diam G <= 2
  Q     both diameters <= 2
For each class: total / with (*) at some vertex / "one-card" (some card G - v plus the
degree sequence of G leaves only graphs isomorphic to G) / triangle-free G or co-G.
"""
import itertools
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import all_graphs, canon  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1_claims import dom_edges, diam_le, star_at  # noqa: E402


def graphs(n):
    if n <= 7:
        return list(all_graphs(n))
    seen = {}
    for G in graphs(n - 1):
        base = list(G.nodes())
        for k in range(n):
            for S in itertools.combinations(base, k):
                H = G.copy()
                H.add_node(n - 1)
                H.add_edges_from((n - 1, s) for s in S)
                key = canon(H)
                if key not in seen:
                    seen[key] = H
    return list(seen.values())


def one_card(G):
    """some v: every S with the level profile of N(v) gives a graph isomorphic to G"""
    cg = canon(G)
    for v in G.nodes():
        N = set(G[v])
        others = [w for w in G.nodes() if w != v]
        c = {w: G.degree(w) - (1 if w in N else 0) for w in others}
        prof = Counter(c[w] for w in N)
        base = G.copy()
        base.remove_node(v)
        ok = True
        for S in itertools.combinations(others, len(N)):
            Ss = set(S)
            if Ss == N or Counter(c[w] for w in Ss) != prof:
                continue
            H = base.copy()
            H.add_node(v)
            H.add_edges_from((v, s) for s in Ss)
            if canon(H) != cg:
                ok = False
                break
        if ok:
            return True
    return False


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    for n in range(4, n_max + 1):
        gs = graphs(n)
        tot = Counter()
        for G in gs:
            Gc = nx.complement(G)
            if not (nx.is_connected(G) and nx.is_connected(Gc)):
                continue
            de, dec = bool(dom_edges(G)), bool(dom_edges(Gc))
            if de and dec:
                cls = "D3"
            elif de and diam_le(G, 2):
                cls = "D2"
            elif diam_le(G, 2) and diam_le(Gc, 2):
                cls = "Q"
            else:
                tot["coD2 (not in P; complement is in D2)"] += 1
                continue
            star = any(star_at(G, v) for v in G.nodes())
            oc = star or one_card(G)
            tf = sum(nx.triangles(G).values()) == 0
            tfc = sum(nx.triangles(Gc).values()) == 0
            tot[cls] += 1
            tot[cls + " star"] += star
            tot[cls + " one-card"] += oc
            tot[cls + " G tri-free"] += tf
            tot[cls + " coG tri-free"] += tfc
            # the triangle-free theorem (CLMS 2022) covers D3 only
            known_tf = cls == "D3" and (tf or tfc)
            tot[cls + " residual(no star" + (", triangles in G and coG)" if cls == "D3" else ")")] += (
                not star and not known_tf)
            tot[cls + " residual(not one-card" + (", triangles in G and coG)" if cls == "D3" else ")")] += (
                not oc and not known_tf)
        print(f"n={n}: {len(gs)} graphs")
        for k in sorted(tot):
            print(f"   {k:60s} {tot[k]}")


if __name__ == "__main__":
    main()
