"""Hunt for members of the one-card residual of sketch t3 among structured (near-regular)
graphs with both diameters <= 2. Evidence only, never a result and never an argument.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t3_probe_structured.py [count] [n ...]

A graph is reported when, at EVERY vertex v, some S satisfies the level counts of N(v), keeps
both diameters <= 2, satisfies the one-card spectral constraints, and gives a graph that is
not isomorphic to G (so no single card decides G with the constraints of this sketch).
"""
import os
import random
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon, g6  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import feasible_sets, in_Q, star2_at, walk_rank  # noqa: E402


def decided_somewhere(G, use_spec=True):
    cg = canon(G)
    for v in G.nodes():
        good = True
        for S in feasible_sets(G, v, use_Q=True, use_spec=use_spec):
            H = G.copy()
            H.remove_node(v)
            H.add_node(v)
            H.add_edges_from((v, s) for s in S)
            if canon(H) != cg:
                good = False
                break
        if good:
            return True
    return False


def perturb(G, rng, k):
    H = G.copy()
    nodes = list(H.nodes())
    for _ in range(k):
        u, v = rng.sample(nodes, 2)
        if H.has_edge(u, v):
            H.remove_edge(u, v)
        else:
            H.add_edge(u, v)
    return H


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    ns = [int(a) for a in sys.argv[2:]] or [9, 10, 11]
    rng = random.Random(11)
    for n in ns:
        seen = set()
        tot = Counter()
        hits = []
        tries = 0
        while len(seen) < count and tries < 60 * count:
            tries += 1
            d = rng.choice([d for d in range(3, n - 3) if (n * d) % 2 == 0])
            try:
                R = nx.random_regular_graph(d, n, seed=rng.randrange(10 ** 9))
            except nx.NetworkXError:
                continue
            G = perturb(R, rng, rng.choice([1, 1, 2, 2, 3]))
            if not in_Q(G):
                continue
            key = canon(G)
            if key in seen:
                continue
            seen.add(key)
            tot["Q"] += 1
            s2 = any(star2_at(G, v) for v in G.nodes())
            tot["star2"] += s2
            cor = n - walk_rank(G)
            tot["cor<=1"] += cor <= 1
            dec = decided_somewhere(G, use_spec=True)
            tot["decided"] += dec
            if not dec:
                hits.append((g6(G), cor, sorted(dict(G.degree()).values())))
        print(f"n={n}: {dict(tot)}  undecided: {hits[:8]}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
