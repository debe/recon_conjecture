import sys, itertools, random, time
sys.path.insert(0, "/home/db/repositories/recon_conjecture/tools/search")
import networkx as nx
import small_graphs as sg

def lean_card(G, x):
    # Recon.card G x = G.induce {x}ᶜ : keep original labels (subtype), induced subgraph
    return G.subgraph([v for v in G.nodes() if v != x])

def lean_hypomorphic(G, H):
    # ∃ σ : V ≃ W, ∀ x, Nonempty (card G x ≃g card H (σ x)); literal backtracking over σ
    V, W = list(G.nodes()), list(H.nodes())
    if len(V) != len(W):
        return False  # no equiv V ≃ W
    cg = {x: lean_card(G, x) for x in V}
    ch = {y: lean_card(H, y) for y in W}
    memo = {}
    def ok(x, y):
        if (x, y) not in memo:
            memo[(x, y)] = nx.is_isomorphic(cg[x], ch[y])
        return memo[(x, y)]
    used = set()
    def bt(i):
        if i == len(V):
            return True
        for y in W:
            if y not in used and ok(V[i], y):
                used.add(y)
                if bt(i + 1):
                    return True
                used.discard(y)
        return False
    return bt(0)

def english_same_deck(G, H):
    # deck = multiset of cards up to isomorphism (independent of canon: greedy class matching)
    if G.number_of_nodes() != H.number_of_nodes():
        return False
    a = [sg.card(G, v) for v in G.nodes()]
    b = [sg.card(H, v) for v in H.nodes()]
    for c in a:
        for j, d in enumerate(b):
            if nx.is_isomorphic(c, d):
                del b[j]; break
        else:
            return False
    return not b

def lean_stmt(G, H):     # Nonempty (G ≃g H) → Recon.Hypomorphic G H
    return (not nx.is_isomorphic(G, H)) or lean_hypomorphic(G, H)

def english_stmt(G, H):  # G ≅ H → same deck
    return (not nx.is_isomorphic(G, H)) or english_same_deck(G, H)

def relabel(G, p):
    return nx.relabel_nodes(G, dict(enumerate(p)))

rng = random.Random(1)
stats = dict(labeled_pairs=0, hyp_true=0, stmt_diff=0, def_pairs=0, def_diff=0,
             def_hyp=0, hyp_not_iso=0, deckkey_diff=0)
diffs = []
t = time.time()
for n in range(0, 7):
    gs = list(sg.all_graphs(n))
    perms = list(itertools.permutations(range(n)))
    for G in gs:
        ps = perms if n <= 5 else rng.sample(perms, 40) + [tuple(range(n))]
        for p in ps:
            H = relabel(G, p)
            stats["labeled_pairs"] += 1
            hyp = nx.is_isomorphic(G, H)  # hypothesis
            stats["hyp_true"] += hyp
            l, e = lean_stmt(G, H), english_stmt(G, H)
            if l != e or not l:
                stats["stmt_diff"] += 1; diffs.append(("stmt", n, sg.g6(G), p, l, e))
    # definition check: Lean Hypomorphic vs English same-deck, all unlabeled pairs (+ random relabel of H)
    for G in gs:
        for H0 in gs:
            H = relabel(H0, rng.choice(perms)) if n else H0
            stats["def_pairs"] += 1
            l, e = lean_hypomorphic(G, H), english_same_deck(G, H)
            k = sg.hypomorphic(G, H)
            stats["def_hyp"] += l
            if l and not nx.is_isomorphic(G, H):
                stats["hyp_not_iso"] += 1
            if k != e: stats["deckkey_diff"] += 1
            if l != e:
                stats["def_diff"] += 1; diffs.append(("def", n, sg.g6(G), sg.g6(H0), l, e))
    print(n, len(gs), dict(stats), round(time.time() - t, 1), flush=True)
print("DIFFS", diffs[:20])
