import sys, itertools
sys.path.insert(0, "/home/db/repositories/recon_conjecture/tools/search")
import networkx as nx
from small_graphs import all_graphs, card

def lean_pred(G, v):
    # Lean reading, literal: vertices of the card are the subtype {v}ᶜ (no relabelling);
    # card adjacency = G.Adj restricted (G.induce); edgeSet = set of Sym2 pairs s(a,b) with Adj a b
    # (loopless, so a != b); ncard on a finite type = cardinality.
    # neighborSet v = {w | G.Adj v w}; ncard = its size.
    sub = [x for x in G.nodes() if x != v]
    card_edges = {frozenset((a, b)) for a in sub for b in sub if a != b and G.has_edge(a, b)}
    nbrs = {w for w in G.nodes() if w != v and G.has_edge(v, w)}
    all_edges = {frozenset((a, b)) for a in G.nodes() for b in G.nodes() if a != b and G.has_edge(a, b)}
    return len(card_edges) + len(nbrs) == len(all_edges)

def en_pred(G, v):
    # English: |E(G - v)| + deg_G(v) = |E(G)|, using the repo's card (vertex-deleted, relabelled)
    return card(G, v).number_of_edges() + G.degree(v) == G.number_of_edges()

stats = {}
diffs = []
for n in range(0, 7):
    cnt = holds_l = holds_e = 0
    for G in all_graphs(n):
        for v in G.nodes():
            cnt += 1
            l, e = lean_pred(G, v), en_pred(G, v)
            holds_l += l; holds_e += e
            if l != e: diffs.append((n, nx.to_graph6_bytes(G, header=False), v))
    stats[n] = (len(all_graphs(n)), cnt, holds_l, holds_e)
# all labelled graphs for n <= 5 (no iso reduction)
lab = 0
for n in range(0, 6):
    pairs = list(itertools.combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        G = nx.Graph(); G.add_nodes_from(range(n))
        G.add_edges_from(p for i, p in enumerate(pairs) if mask >> i & 1)
        for v in range(n):
            lab += 1
            if lean_pred(G, v) != en_pred(G, v) or not lean_pred(G, v):
                diffs.append(("lab", n, mask, v))
for n, s in stats.items(): print(n, "classes=%d (G,v)=%d lean_true=%d en_true=%d" % s)
print("labelled (G,v) pairs checked n<=5:", lab)
print("diffs:", diffs[:10], len(diffs))
