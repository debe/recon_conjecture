"""A non-vacuous single-graph test of lemmas S3 / S4 of sketch t3. Evidence only.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t3_pseudosimilar.py [n_max]

If G - x and G - y are isomorphic, the transposition (x y) is a hypomorphism G -> G, so S3 and S4
say that x and y have the same closed-walk counts (A^k)_xx and the same walk counts (A^k 1)_x
for every k. The test is not vacuous: from n = 8 on there are pseudo-similar vertices (cards
isomorphic, no automorphism mapping x to y).
"""
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon, card, g6  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import adj, matvec  # noqa: E402
from t1_stats import graphs  # noqa: E402


def profiles(G):
    nodes = sorted(G.nodes())
    n = len(nodes)
    A = adj(G, nodes)
    x = [1] * n
    P = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    out = {v: [] for v in nodes}
    for _ in range(n + 1):
        for i, v in enumerate(nodes):
            out[v].append((x[i], P[i][i]))
        x = matvec(A, x)
        P = [[sum(P[i][l] * A[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
    return {v: tuple(p) for v, p in out.items()}


def orbits_key(G, v):
    """a cheap automorphism-invariant of the rooted graph (G, v): canonical form with v marked
    by a pendant path of length n (long enough to be recognisable)"""
    H = G.copy()
    n = G.number_of_nodes()
    prev = v
    for i in range(n):
        H.add_edge(prev, ("m", i))
        prev = ("m", i)
    import networkx as nx
    return canon(nx.convert_node_labels_to_integers(H))


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    for n in range(3, n_max + 1):
        pairs = pseudo = bad = 0
        example = None
        for G in graphs(n):
            by_card = defaultdict(list)
            for v in G.nodes():
                by_card[canon(card(G, v))].append(v)
            if all(len(c) == 1 for c in by_card.values()):
                continue
            prof = profiles(G)
            for cls in by_card.values():
                if len(cls) < 2:
                    continue
                keys = {v: orbits_key(G, v) for v in cls}
                for i, a in enumerate(cls):
                    for b in cls[i + 1:]:
                        pairs += 1
                        if keys[a] != keys[b]:
                            pseudo += 1
                            example = example or (g6(G), a, b)
                        if prof[a] != prof[b]:
                            bad += 1
                            print("VIOLATION", g6(G), a, b)
        print(f"n={n}: vertex pairs with isomorphic cards: {pairs}, of which pseudo-similar: {pseudo}"
              f" (first: {example}), profile mismatches: {bad}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
