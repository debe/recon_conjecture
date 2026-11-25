"""Hunt for D2 graphs outside the t4 classes among adversarial families (evidence only).

Families: G(n, 1/2); random d-regular graphs (d near n/2) with 1-3 edges toggled; d-regular
(random or circulant) with a matching toggled on half of the vertices (degrees d, d + 1). Reports, for the D2 graphs seen: star / pure / glue / T / none.

  python3 .../t4_probe_hunt.py [seed]
"""
import os
import random
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import in_D2, pair_table, pure_degrees, star_vertices  # noqa: E402
from t4_stats import glue  # noqa: E402
from t4_probe_transport import in_T  # noqa: E402
from small_graphs import canon, g6  # noqa: E402


def near_regular(n, rng):
    d = rng.choice([k for k in range(max(3, n // 2 - 2), min(n - 3, n // 2 + 2)) if (n * k) % 2 == 0])
    G = nx.random_regular_graph(d, n, seed=rng.randrange(1 << 30))
    for _ in range(rng.choice((1, 2, 3))):
        a, b = rng.sample(range(n), 2)
        if G.has_edge(a, b):
            G.remove_edge(a, b)
        else:
            G.add_edge(a, b)
    return G


def bidegree(n, rng):
    """d-regular (random or circulant) plus a matching on a random half: degrees d, d + 1."""
    d = rng.choice([k for k in range(max(3, n // 2 - 2), min(n - 3, n // 2 + 2)) if (n * k) % 2 == 0])
    if rng.random() < 0.5:
        G = nx.random_regular_graph(d, n, seed=rng.randrange(1 << 30))
    else:
        js = rng.sample(range(1, n // 2), min(d // 2, n // 2 - 1))
        G = nx.circulant_graph(n, js)
    half = rng.sample(range(n), 2 * (n // 4))
    for i in range(0, len(half), 2):
        a, b = half[i], half[i + 1]
        if G.has_edge(a, b):
            G.remove_edge(a, b)
        else:
            G.add_edge(a, b)
    return G


def run(label, graphs):
    c = Counter()
    left = []
    seen = set()
    for G in graphs:
        if not in_D2(G):
            continue
        k = canon(G)
        if k in seen:
            continue
        seen.add(k)
        pi, e = pair_table(G)
        s = bool(star_vertices(G))
        p = bool(pure_degrees(G, pi, e))
        gl = glue(G, pi, e)
        t = s or p or in_T(G)
        c["D2"] += 1
        c["star"] += s
        c["pure"] += p
        c["glue"] += gl
        c["T"] += t
        if not (s or p or gl or t):
            c["none"] += 1
            left.append(g6(G))
    print(label, dict(c), left[:12], flush=True)


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 4)
    for n, cnt in ((8, 3000), (9, 3000), (10, 2000), (11, 1200), (12, 800), (14, 300)):
        run(f"n={n} G(n,1/2)", (nx.gnp_random_graph(n, 0.5, seed=rng.randrange(1 << 30))
                                for _ in range(cnt)))
        run(f"n={n} near-regular", (near_regular(n, rng) for _ in range(cnt)))
        run(f"n={n} bi-degree", (bidegree(n, rng) for _ in range(cnt)))
