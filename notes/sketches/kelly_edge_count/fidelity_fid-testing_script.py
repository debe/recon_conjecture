import sys, random, itertools
sys.path.insert(0, '/home/db/repositories/recon_conjecture/tools/search')
import networkx as nx
from networkx.algorithms import bipartite
from small_graphs import all_graphs, card, deck_key

def card_lean(G, x):
    # G.induce {x}ᶜ : vertices of G other than x, induced adjacency
    return G.subgraph([v for v in G.nodes if v != x]).copy()

def hyp_lean(G, H):
    # ∃ σ : V ≃ W, ∀ x, Nonempty (card G x ≃g card H (σ x)); computed as a perfect
    # matching in the bipartite "cards isomorphic" graph (independent of small_graphs.canon)
    if G.number_of_nodes() != H.number_of_nodes():
        return False  # no bijection Fin n ≃ Fin m when n ≠ m (not reachable here: same n)
    B = nx.Graph()
    L = [('g', x) for x in G.nodes]; R = [('h', y) for y in H.nodes]
    B.add_nodes_from(L); B.add_nodes_from(R)
    for x in G.nodes:
        cx = card_lean(G, x)
        for y in H.nodes:
            if nx.is_isomorphic(cx, card_lean(H, y)):
                B.add_edge(('g', x), ('h', y))
    if not L:
        return True
    M = bipartite.hopcroft_karp_matching(B, top_nodes=L)
    return all(l in M for l in L)

def hyp_en(G, H):
    # English: same deck = same multiset of cards up to isomorphism
    return deck_key(G) == deck_key(H)

def lean_pred(n, G, H):   # 3 ≤ n → Hypomorphic G H → |E G| = |E H|
    return (not (3 <= n)) or (not hyp_lean(G, H)) or G.number_of_edges() == H.number_of_edges()

def en_pred(n, G, H):     # n ≥ 3, same deck ⇒ same number of edges
    return (not (n >= 3)) or (not hyp_en(G, H)) or G.number_of_edges() == H.number_of_edges()

def relabel(G, rng):
    p = list(G.nodes); rng.shuffle(p)
    return nx.relabel_nodes(G, dict(zip(G.nodes, p)))

rng = random.Random(1)
stats = {}
diffs = []
for n in range(0, 7):
    gs = list(all_graphs(n)) if n > 0 else [nx.empty_graph(0)]
    pairs = hyp_pairs = hyp_distinct = hyp_mismatch = 0
    lean_false = en_false = 0
    for G in gs:
        for H in gs:
            Hr = relabel(H, rng)   # labelled, not just atlas representatives
            pairs += 1
            hl, he = hyp_lean(G, Hr), hyp_en(G, Hr)
            if hl != he: hyp_mismatch += 1; diffs.append(('hyp', n, G.edges, Hr.edges))
            if hl:
                hyp_pairs += 1
                if not nx.is_isomorphic(G, Hr): hyp_distinct += 1
            lp, ep = lean_pred(n, G, Hr), en_pred(n, G, Hr)
            if lp != ep: diffs.append(('pred', n, list(G.edges), list(Hr.edges)))
            lean_false += (not lp); en_false += (not ep)
    stats[n] = dict(graphs=len(gs), pairs=pairs, hyp_pairs=hyp_pairs, hyp_noniso=hyp_distinct,
                    hyp_mismatch=hyp_mismatch, lean_pred_false=lean_false, en_pred_false=en_false)
    print(n, stats[n])

# n=2 without the 3 ≤ n guard: does the conclusion fail? (shows the hypothesis is needed)
K2, E2 = nx.complete_graph(2), nx.empty_graph(2)
print('n=2 K2 vs 2K1: hyp_lean', hyp_lean(K2, E2), 'edges', K2.number_of_edges(), E2.number_of_edges())
print('diffs:', len(diffs), diffs[:5])
