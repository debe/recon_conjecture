import sys, itertools, collections
sys.path.insert(0, "/home/db/repositories/recon_conjecture/tools/search")
import networkx as nx
from small_graphs import all_graphs, card, deck_key, hypomorphic, canon

# Lean reading, literal: Hypomorphic G H := ∃ σ : Fin n ≃ Fin n, ∀ x, card G x ≅ card H (σ x)
def lean_hyp(G, H):
    n = G.number_of_nodes()
    cg = [canon(card(G, x)) for x in range(n)]
    ch = [canon(card(H, x)) for x in range(n)]
    return any(all(cg[x] == ch[s[x]] for x in range(n)) for s in itertools.permutations(range(n)))

# Lean conclusion, literal: ∃ σ perm, ∀ v, |N_G(v)| = |N_H(σ v)|
def lean_concl(G, H):
    n = G.number_of_nodes()
    dg = [G.degree(v) for v in range(n)]; dh = [H.degree(v) for v in range(n)]
    return any(all(dg[v] == dh[s[v]] for v in range(n)) for s in itertools.permutations(range(n)))

def lean_pred(n, G, H):  # the body of S for this n,G,H
    return (not (3 <= n)) or (not lean_hyp(G, H)) or lean_concl(G, H)

# English reading: n>=3, same deck (multiset of card iso classes) => same degree sequence (sorted)
def en_pred(n, G, H):
    if n < 3: return True
    if deck_key(G) != deck_key(H): return True
    return sorted(d for _, d in G.degree()) == sorted(d for _, d in H.degree())

stats = collections.Counter()
diffs = []
for n in range(0, 7):
    gs = list(all_graphs(n)) if n > 0 else [nx.empty_graph(0)]
    # cheap prefilter on lean_hyp: necessary condition is same deck multiset
    for G in gs:
        for H in gs:
            same_deck = deck_key(G) == deck_key(H)
            lh = lean_hyp(G, H) if same_deck else False
            assert lh == same_deck, (n, G.edges, H.edges)  # literal Hypomorphic = deck equality
            if lh: stats[("hyp_holds", n)] += 1
            lp = (not (3 <= n)) or (not lh) or lean_concl(G, H)
            ep = en_pred(n, G, H)
            if lp != ep: diffs.append((n, list(G.edges), list(H.edges)))
            if not lp: stats[("lean_false", n)] += 1
# also check non-same-deck pairs never satisfy lean_hyp for n<=5 (no prefilter)
for n in range(1, 6):
    gs = list(all_graphs(n))
    for G in gs:
        for H in gs:
            assert lean_hyp(G, H) == (deck_key(G) == deck_key(H))
print("diffs:", diffs)
print(sorted(stats.items()))

# labeled check n=3,4: all labeled graphs on Fin n
for n in (3, 4):
    pairs = list(itertools.combinations(range(n), 2))
    lab = []
    for mask in range(1 << len(pairs)):
        G = nx.empty_graph(n); G.add_edges_from(p for i, p in enumerate(pairs) if mask >> i & 1); lab.append(G)
    bad = 0; hyp = 0; nontriv = 0
    for G in lab:
        for H in lab:
            if lean_hyp(G, H):
                hyp += 1
                if set(G.edges) != set(H.edges): nontriv += 1
                if not lean_concl(G, H) or not en_pred(n, G, H): bad += 1
    print("labeled n=%d graphs=%d hyp_pairs=%d distinct_labeled_hyp_pairs=%d bad=%d" % (n, len(lab), hyp, nontriv, bad))

# n=2 sanity: without 3<=n the claim fails (K2 vs 2K1)
K2 = nx.complete_graph(2); E2 = nx.empty_graph(2)
print("n=2 K2~2K1 hyp:", lean_hyp(K2, E2), "degree conclusion:", lean_concl(K2, E2))
