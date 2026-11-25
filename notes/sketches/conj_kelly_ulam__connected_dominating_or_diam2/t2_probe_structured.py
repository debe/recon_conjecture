"""Hunt for D2 graphs outside one2 among perturbations of symmetric D2 graphs. Evidence only."""
import os, sys, random, itertools
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'search'))
from small_graphs import canon, g6
from t2_stats_one2 import one2
from t2_lib import in_D2, degseq

def paley(q):
    sq = {(x * x) % q for x in range(1, q)}
    G = nx.Graph(); G.add_nodes_from(range(q))
    G.add_edges_from((a, b) for a in range(q) for b in range(a + 1, q) if (b - a) % q in sq)
    return G

def paley9():
    # GF(9) = Z3[i]; squares: nonzero elements a+bi with norm... use explicit set
    els = [(a, b) for a in range(3) for b in range(3)]
    def mul(x, y): return ((x[0]*y[0] - x[1]*y[1]) % 3, (x[0]*y[1] + x[1]*y[0]) % 3)
    sq = {mul(x, x) for x in els if x != (0, 0)}
    G = nx.Graph(); G.add_nodes_from(range(9))
    for i, x in enumerate(els):
        for j, y in enumerate(els):
            if i < j and ((x[0]-y[0]) % 3, (x[1]-y[1]) % 3) in sq:
                G.add_edge(i, j)
    return G

bases = {
    'C5': nx.cycle_graph(5),
    'Petersen': nx.petersen_graph(),
    'Paley9': paley9(),
    'Paley13': paley(13),
    'C5[2K1]': nx.lexicographic_product(nx.cycle_graph(5), nx.empty_graph(2)),
    'C5[K2]': nx.lexicographic_product(nx.cycle_graph(5), nx.complete_graph(2)),
    'circ9(1,3)': nx.circulant_graph(9, [1, 3]),
    'circ11(1,3)': nx.circulant_graph(11, [1, 3]),
    'circ8(1,3)c': nx.circulant_graph(8, [1, 2]),
    'circ12(1,3,4)': nx.circulant_graph(12, [1, 3, 4]),
}
rng = random.Random(1)
tot = 0; d2 = 0; bad = []
for name, R in bases.items():
    R = nx.convert_node_labels_to_integers(R)
    seen = {}
    cands = []
    for e in R.edges():
        A = nx.Graph(R); A.remove_edge(*e); cands.append(A)
    for e in nx.non_edges(R):
        A = nx.Graph(R); A.add_edge(*e); cands.append(A)
    for x in R.nodes():
        A = nx.Graph(R); A.remove_node(x); cands.append(nx.convert_node_labels_to_integers(A))
    for _ in range(25):  # two random flips
        A = nx.Graph(R)
        for (a, b) in rng.sample(list(itertools.combinations(R.nodes(), 2)), 2):
            if A.has_edge(a, b): A.remove_edge(a, b)
            else: A.add_edge(a, b)
        cands.append(A)
    for A in cands:
        seen.setdefault(canon(A), A)
    k = 0; kb = 0
    for A in seen.values():
        tot += 1
        if in_D2(A):
            d2 += 1; k += 1
            if not one2(A):
                kb += 1; bad.append((name, g6(A), degseq(A)))
    print(name, 'base in D2:', in_D2(R), 'perturbations', len(seen), 'in D2', k, 'not one2', kb, flush=True)
print('total', tot, 'D2', d2, 'D2 not one2', len(bad), bad[:8])
