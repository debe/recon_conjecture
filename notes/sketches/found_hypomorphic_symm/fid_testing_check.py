import sys, itertools
sys.path.insert(0, '/home/db/repositories/recon_conjecture/tools/search')
import networkx as nx
from networkx.algorithms import bipartite
from small_graphs import all_graphs, card, deck_key, hypomorphic

def lean_hyp(G, H):
    """Lean Recon.Hypomorphic: exists bijection s : V -> W with card G x ~= card H (s x) for all x.
    Encoded independently: perfect matching in bipartite graph of iso card pairs (nx.is_isomorphic)."""
    VG, VH = sorted(G.nodes), sorted(H.nodes)
    if len(VG) != len(VH):
        return False   # no Equiv between Fin n and Fin m with n != m
    if not VG:
        return True    # empty Equiv, vacuous forall
    B = nx.Graph()
    L = [('g', x) for x in VG]; R = [('h', y) for y in VH]
    B.add_nodes_from(L); B.add_nodes_from(R)
    for x in VG:
        cx = G.subgraph([v for v in VG if v != x])
        for y in VH:
            if nx.is_isomorphic(cx, H.subgraph([v for v in VH if v != y])):
                B.add_edge(('g', x), ('h', y))
    M = bipartite.hopcroft_karp_matching(B, top_nodes=L)
    return sum(1 for k in M if k[0] == 'g') == len(VG)

def lean_hyp_brute(G, H):
    VG, VH = sorted(G.nodes), sorted(H.nodes)
    if len(VG) != len(VH): return False
    for p in itertools.permutations(VH):
        s = dict(zip(VG, p))
        if all(nx.is_isomorphic(G.subgraph([v for v in VG if v != x]),
                                H.subgraph([v for v in VH if v != s[x]])) for x in VG):
            return True
    return False

def en_hyp(G, H):
    """English: same deck = equal multisets of cards up to isomorphism."""
    return G.number_of_nodes() == H.number_of_nodes() and deck_key(G) == deck_key(H)

def lean_stmt(G, H): return (not lean_hyp(G, H)) or lean_hyp(H, G)
def en_stmt(G, H):   return (not en_hyp(G, H)) or en_hyp(H, G)

diff = []; hyp_true = 0; hyp_true_ne = 0; pairs = 0; defdiff = []
for n in range(0, 7):
    gs = list(all_graphs(n)) if n > 0 else [nx.Graph()]
    for G in gs:
        for H in gs:
            pairs += 1
            lh, eh = lean_hyp(G, H), en_hyp(G, H)
            if lh != eh: defdiff.append((n, G.edges, H.edges))
            if lh:
                hyp_true += 1
                if not nx.is_isomorphic(G, H): hyp_true_ne += 1
            if lean_stmt(G, H) != en_stmt(G, H) or not lean_stmt(G, H):
                diff.append((n, list(G.edges), list(H.edges)))
    print('n', n, 'graphs', len(gs))
print('unlabeled pairs', pairs, 'hyp true', hyp_true, 'hyp true & non-iso', hyp_true_ne)
print('stmt diffs/failures', diff[:5], len(diff))
print('Lean-def vs deck-multiset diffs', len(defdiff))

# labeled exhaustive with brute-force permutation search, n <= 4
lab = 0; ld = 0; lhcount = 0
for n in range(0, 5):
    E = list(itertools.combinations(range(n), 2))
    gs = []
    for mask in range(1 << len(E)):
        G = nx.Graph(); G.add_nodes_from(range(n))
        G.add_edges_from(e for i, e in enumerate(E) if mask >> i & 1)
        gs.append(G)
    for G in gs:
        for H in gs:
            lab += 1
            a, b = lean_hyp_brute(G, H), lean_hyp_brute(H, G)
            lhcount += a
            if a != en_hyp(G, H) or (a and not b): ld += 1
print('labeled pairs n<=4', lab, 'hyp true', lhcount, 'diffs', ld)
# cross check with library
print('lib agrees on n=2 anchor:', hypomorphic(nx.complete_graph(2), nx.empty_graph(2)), lean_hyp(nx.complete_graph(2), nx.empty_graph(2)))
