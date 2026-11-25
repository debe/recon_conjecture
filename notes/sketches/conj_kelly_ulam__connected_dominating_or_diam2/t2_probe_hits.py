"""Classify near-regular graphs outside one2: D2? dominating edge? W'? Evidence only."""
import os, sys, random
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'search'))
from small_graphs import canon, g6
from t2_stats_one2 import one2
from t2_stats_wprime import in_Wp
from t2_lib import in_D2, dominating_edge, degseq, sep_vertices

rng = random.Random(17)
seen = {}
for n, d, reps in ((8, 3, 150), (8, 4, 150), (9, 4, 100), (10, 3, 40), (10, 4, 60), (10, 5, 60), (10, 6, 40)):
    for _ in range(reps):
        R = nx.random_regular_graph(d, n, seed=rng.randrange(1 << 30))
        e = rng.choice(list(R.edges())); ne = rng.choice(list(nx.non_edges(R)))
        A = nx.Graph(R); A.remove_edge(*e)
        B = nx.Graph(R); B.add_edge(*ne)
        for G in (A, B):
            seen.setdefault(canon(G), G)
rows = []
for G in seen.values():
    if not in_D2(G):
        continue
    o = one2(G)
    if not o:
        rows.append((G.number_of_nodes(), g6(G), degseq(G), 'W\'' if in_Wp(G) else 'notW\''))
print('distinct near-regular graphs', len(seen), 'in D2', sum(in_D2(G) for G in seen.values()))
print('D2 and not one2:', len(rows))
for r in rows[:12]:
    print(r)
