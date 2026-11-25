import sys, itertools
sys.path.insert(0, "/home/db/repositories/recon_conjecture/tools/search")
import networkx as nx
from networkx.algorithms import bipartite
from small_graphs import all_graphs, deck_key, hypomorphic

def card_lean(G, x):
    # G.induce {x}^c : keep original labels (subtype), no relabelling
    return G.subgraph([v for v in G.nodes() if v != x]).copy()

def lean_hyp_perm(G, H):
    """Literal Lean: exists bijection sigma: V(G) ~= V(H), forall x, card G x ~=g card H (sigma x)."""
    VG, VH = sorted(G.nodes()), sorted(H.nodes())
    if len(VG) != len(VH): return False
    for p in itertools.permutations(VH):
        s = dict(zip(VG, p))
        if all(nx.is_isomorphic(card_lean(G, x), card_lean(H, s[x])) for x in VG):
            return True
    return False

def lean_hyp_match(G, H):
    """Same predicate via perfect matching in the card-iso bipartite relation (equivalent to exists sigma)."""
    VG, VH = list(G.nodes()), list(H.nodes())
    if len(VG) != len(VH): return False
    if not VG: return True
    B = nx.Graph()
    L = [("g", x) for x in VG]; R = [("h", y) for y in VH]
    B.add_nodes_from(L); B.add_nodes_from(R)
    for x in VG:
        for y in VH:
            if nx.is_isomorphic(card_lean(G, x), card_lean(H, y)):
                B.add_edge(("g", x), ("h", y))
    M = bipartite.maximum_matching(B, top_nodes=L)
    return len(M) // 2 == len(VG)

def en_hyp(G, H):
    """English: same deck = equal multisets of iso classes of vertex-deleted cards."""
    return hypomorphic(G, H)

def check_trans(gs, rel, label):
    N = len(gs); bad = 0; hyp_pairs = 0; chains = 0
    R = [[rel[i][j] for j in range(N)] for i in range(N)]
    for i in range(N):
        for j in range(N):
            if not R[i][j]: continue
            hyp_pairs += 1
            for k in range(N):
                if R[j][k]:
                    chains += 1
                    if not R[i][k]: bad += 1
    return hyp_pairs, chains, bad

total_diff = 0
print("== unlabelled representatives, n = 0..6 ==")
for n in range(0, 7):
    gs = list(all_graphs(n))
    N = len(gs)
    L = [[lean_hyp_match(gs[i], gs[j]) for j in range(N)] for i in range(N)]
    E = [[en_hyp(gs[i], gs[j]) for j in range(N)] for i in range(N)]
    diff = sum(L[i][j] != E[i][j] for i in range(N) for j in range(N))
    total_diff += diff
    # Statement-level: Lean statement truth vs English statement truth on all triples
    lp, lc, lb = check_trans(gs, L, "lean")
    ep, ec, eb = check_trans(gs, E, "en")
    nontriv = sum(L[i][j] and i != j for i in range(N) for j in range(N))
    print(f"n={n} graphs={N} pair-diffs={diff} lean:hyp_pairs={lp} chains={lc} trans_fail={lb} "
          f"en:hyp_pairs={ep} chains={ec} trans_fail={eb} nonisomorphic_hyp_pairs={nontriv}")

print("== all labelled graphs on Fin n, n = 0..4, literal permutation search ==")
for n in range(0, 5):
    pairs = list(itertools.combinations(range(n), 2))
    gs = []
    for mask in range(1 << len(pairs)):
        G = nx.Graph(); G.add_nodes_from(range(n))
        G.add_edges_from(p for b, p in enumerate(pairs) if mask >> b & 1)
        gs.append(G)
    N = len(gs)
    L = [[lean_hyp_perm(gs[i], gs[j]) for j in range(N)] for i in range(N)]
    E = [[en_hyp(gs[i], gs[j]) for j in range(N)] for i in range(N)]
    diff = sum(L[i][j] != E[i][j] for i in range(N) for j in range(N))
    total_diff += diff
    lp, lc, lb = check_trans(gs, L, "lean")
    ep, ec, eb = check_trans(gs, E, "en")
    print(f"n={n} labelled graphs={N} pair-diffs={diff} lean:hyp_pairs={lp} chains={lc} trans_fail={lb} "
          f"en:chains={ec} trans_fail={eb}")
print("TOTAL pair diffs:", total_diff)
