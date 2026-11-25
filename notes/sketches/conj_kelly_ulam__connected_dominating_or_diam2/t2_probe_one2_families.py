"""Hunt for graphs outside `one2` (no card determines the graph together with the neighbour-degree
data) in families away from G(n,1/2): trees, sparse/dense random graphs, near-regular graphs.
A hit would show the residual of the proposed reduction is non-empty in general (it need not lie
in D2). Evidence only."""
import os, sys, random, itertools
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'search'))
from small_graphs import canon, g6
from t2_stats_one2 import one2
from t2_lib import in_D2

hits = []
for n in range(8, 12):
    cnt = 0
    for T in nx.nonisomorphic_trees(n):
        cnt += 1
        if not one2(T):
            hits.append(('tree', n, g6(T)))
    print('trees', n, cnt, 'hits so far', len(hits), flush=True)

rng = random.Random(3)
for n, per in ((8, 250), (9, 120)):
    for p in (0.15, 0.3, 0.7, 0.85):
        seen = {}
        for _ in range(per):
            G = nx.gnp_random_graph(n, p, seed=rng.randrange(1 << 30))
            seen.setdefault(canon(G), G)
        bad = [g6(G) for G in seen.values() if not one2(G)]
        hits += [('gnp', n, b) for b in bad]
        print('gnp', n, p, len(seen), 'bad', bad[:3], flush=True)

# near-regular: random d-regular graph with one edge removed / one edge added / one vertex cloned
for n, d in ((8, 3), (8, 4), (9, 4), (10, 3), (10, 4), (10, 5)):
    bad = 0; tot = 0; d2 = 0
    for _ in range(40):
        R = nx.random_regular_graph(d, n, seed=rng.randrange(1 << 30))
        e = rng.choice(list(R.edges()))
        ne = rng.choice(list(nx.non_edges(R)))
        for G in (nx.restricted_view(R, [], [e]), nx.Graph(list(R.edges()) + [ne])):
            G = nx.Graph(G); G.add_nodes_from(range(n)); tot += 1
            d2 += in_D2(G)
            if not one2(G):
                bad += 1; hits.append(('nearreg', n, g6(G)))
    print('near-regular', n, d, 'tested', tot, 'in D2', d2, 'bad', bad, flush=True)
print('HITS', hits[:10], len(hits))
