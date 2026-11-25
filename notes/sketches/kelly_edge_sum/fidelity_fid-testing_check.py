import sys, itertools
sys.path.insert(0, '/home/db/repositories/recon_conjecture/tools/search')
import networkx as nx
from small_graphs import all_graphs, card

def natsub(a, b): return max(a - b, 0)

def lean_reading(n, G):
    # (Recon.card G v) = G.induce {v}ᶜ : edges are unordered pairs {a,b} of subtype elements, a != b, G.Adj a b.
    # edgeSet.ncard counts them. Computed from the raw adjacency relation, not via networkx subgraph.
    lhs = 0
    for v in range(n):
        rest = [u for u in range(n) if u != v]
        lhs += sum(1 for a, b in itertools.combinations(rest, 2) if G.has_edge(a, b))
    E = sum(1 for a, b in itertools.combinations(range(n), 2) if G.has_edge(a, b))
    return lhs == natsub(n, 2) * E

def english_reading(n, G):
    # sum over vertices of |E(G - v)| equals (n-2)|E| (integer arithmetic; English says nat-sub, both 0 for n<2)
    lhs = sum(card(G, v).number_of_edges() for v in G.nodes)
    return lhs == (n - 2) * G.number_of_edges()

def english_natsub(n, G):
    lhs = sum(card(G, v).number_of_edges() for v in G.nodes)
    return lhs == natsub(n, 2) * G.number_of_edges()

stats = {}
# unlabelled classes n = 0..7
for n in range(0, 8):
    cnt = diff = holds = 0
    if n == 0:
        gs = [nx.empty_graph(0)]
    else:
        gs = list(all_graphs(n))
    for G in gs:
        assert sorted(G.nodes) == list(range(n))
        l, e, e2 = lean_reading(n, G), english_reading(n, G), english_natsub(n, G)
        cnt += 1; holds += l
        if not (l == e == e2):
            diff += 1; print('DIFF', n, list(G.edges), l, e, e2)
    stats[('unlab', n)] = (cnt, holds, diff)
# all labelled graphs n = 0..6
for n in range(0, 7):
    pairs = list(itertools.combinations(range(n), 2))
    cnt = diff = holds = 0
    for mask in range(1 << len(pairs)):
        G = nx.empty_graph(n)
        G.add_edges_from(p for i, p in enumerate(pairs) if mask >> i & 1)
        l, e, e2 = lean_reading(n, G), english_reading(n, G), english_natsub(n, G)
        cnt += 1; holds += l
        if not (l == e == e2):
            diff += 1; print('DIFF', n, list(G.edges), l, e, e2)
    stats[('lab', n)] = (cnt, holds, diff)
for k, v in stats.items(): print(k, 'graphs=%d lean_true=%d diffs=%d' % v)
