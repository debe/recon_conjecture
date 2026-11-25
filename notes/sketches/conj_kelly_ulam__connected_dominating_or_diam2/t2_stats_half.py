"""Trend of the proposed children on G(n, 1/2) samples restricted to D2. Evidence only.
Columns as in t2_stats.py (one is not computed here)."""
import os, sys, random
from collections import Counter
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'search'))
from small_graphs import canon, g6
from t2_lib import in_D2, is_regular, sep_vertices
from t2_stats import in_W

rng = random.Random(11)
for n, cnt in ((8, 600), (9, 400), (10, 300), (11, 200), (12, 150), (14, 60)):
    seen = {}
    for _ in range(cnt):
        G = nx.gnp_random_graph(n, 0.5, seed=rng.randrange(1 << 30))
        if in_D2(G):
            seen.setdefault(canon(G), G)
    c = Counter(); ex = []
    for G in seen.values():
        sep = bool(sep_vertices(G)); w = in_W(G)
        c['D2'] += 1; c['sep'] += sep; c['W'] += w
        c['both'] += sep and w
        if not sep and not w:
            c['res'] += 1
            if len(ex) < 2: ex.append(g6(G))
    print(f"n={n} sampled={cnt}: " + ' '.join(f"{k}={c[k]}" for k in ('D2', 'sep', 'W', 'both', 'res')), ex, flush=True)
