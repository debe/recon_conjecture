"""Larger hunt for a D2 graph outside one2: near-regular graphs (regular +- one or two edges)
with d about n/2, n = 9..12. Evidence only. Prints every hit as graph6."""
import os, sys, random
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'search'))
from small_graphs import canon, g6
from t2_stats_one2 import one2
from t2_lib import in_D2

rng = random.Random(23)
for n, d, reps in ((8, 3, 300), (8, 4, 300), (9, 4, 200), (10, 4, 150), (10, 5, 150), (11, 4, 80), (11, 6, 80), (12, 5, 60), (12, 6, 60)):
    seen = {}
    for _ in range(reps):
        R = nx.random_regular_graph(d, n, seed=rng.randrange(1 << 30))
        for flips in (1, 1, 2):
            A = nx.Graph(R)
            for _ in range(flips):
                if rng.random() < 0.5:
                    A.remove_edge(*rng.choice(list(A.edges())))
                else:
                    A.add_edge(*rng.choice(list(nx.non_edges(A))))
            if in_D2(A):
                seen.setdefault(canon(A), A)
    bad = [g6(A) for A in seen.values() if not one2(A)]
    print(f"n={n} d={d}: distinct D2 near-regular {len(seen)}, not one2: {len(bad)} {bad[:5]}", flush=True)
