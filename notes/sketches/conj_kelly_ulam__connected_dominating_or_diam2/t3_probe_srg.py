"""Hunt for one-card-undecided graphs among perturbations of highly regular graphs with both
diameters <= 2. Evidence only, never a result and never an argument.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t3_probe_srg.py [per_base]

Bases: C5, Petersen, Paley(9), Paley(13), Clebsch, Shrikhande, 4x4 rook, C5[2K1], C5[K2],
complement of Petersen. Each is perturbed by toggling 1..3 random pairs. A graph is reported
when at EVERY vertex some S passes the level counts, keeps both diameters <= 2, passes the
one-card spectral constraints and gives a graph not isomorphic to G.
"""
import itertools
import os
import random
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon, g6  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import in_Q, star2_at, walk_rank  # noqa: E402
from t3_probe_structured import decided_somewhere, perturb  # noqa: E402


def paley(q):
    sq = {(x * x) % q for x in range(1, q)}
    G = nx.Graph()
    G.add_nodes_from(range(q))
    G.add_edges_from((a, b) for a, b in itertools.combinations(range(q), 2) if (a - b) % q in sq)
    return G


def paley9():
    # GF(9) = F3[i], squares = {+-1, +-i}
    pts = [(a, b) for a in range(3) for b in range(3)]
    sq = {(1, 0), (2, 0), (0, 1), (0, 2)}
    G = nx.Graph()
    G.add_nodes_from(range(9))
    for (i, p), (j, q) in itertools.combinations(enumerate(pts), 2):
        if ((p[0] - q[0]) % 3, (p[1] - q[1]) % 3) in sq:
            G.add_edge(i, j)
    return G


def clebsch():
    G = nx.Graph()
    G.add_nodes_from(range(16))
    for a, b in itertools.combinations(range(16), 2):
        if bin(a ^ b).count("1") in (1, 4):
            G.add_edge(a, b)
    return G


def shrikhande():
    G = nx.Graph()
    pts = [(a, b) for a in range(4) for b in range(4)]
    S = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
    for (i, p), (j, q) in itertools.combinations(enumerate(pts), 2):
        if ((p[0] - q[0]) % 4, (p[1] - q[1]) % 4) in S:
            G.add_edge(i, j)
    return G


def rook4():
    G = nx.Graph()
    pts = [(a, b) for a in range(4) for b in range(4)]
    for (i, p), (j, q) in itertools.combinations(enumerate(pts), 2):
        if p[0] == q[0] or p[1] == q[1]:
            G.add_edge(i, j)
    return G


def lex(G, H):
    return nx.convert_node_labels_to_integers(nx.lexicographic_product(G, H))


def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 25
    rng = random.Random(5)
    bases = {
        "C5": nx.cycle_graph(5), "Petersen": nx.petersen_graph(),
        "coPetersen": nx.complement(nx.petersen_graph()),
        "Paley9": paley9(), "Paley13": paley(13), "Clebsch": clebsch(),
        "Shrikhande": shrikhande(), "Rook4x4": rook4(),
        "C5[2K1]": lex(nx.cycle_graph(5), nx.empty_graph(2)),
        "C5[K2]": lex(nx.cycle_graph(5), nx.complete_graph(2)),
    }
    for name, B in bases.items():
        B = nx.convert_node_labels_to_integers(B)
        n = B.number_of_nodes()
        seen, tot, hits = set(), Counter(), []
        tries = 0
        while len(seen) < per and tries < 40 * per:
            tries += 1
            G = perturb(B, rng, rng.choice([1, 2, 2, 3]))
            if not in_Q(G):
                continue
            key = canon(G)
            if key in seen:
                continue
            seen.add(key)
            tot["Q"] += 1
            tot["star2"] += any(star2_at(G, v) for v in G.nodes())
            cor = n - walk_rank(G)
            tot["cor<=1"] += cor <= 1
            dec = decided_somewhere(G, use_spec=True)
            tot["decided"] += dec
            if not dec:
                hits.append((g6(G), cor))
        print(f"{name} (n={n}): {dict(tot)}  undecided: {hits[:6]}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
