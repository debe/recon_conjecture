import sys, itertools, time
sys.path.insert(0, "/home/db/repositories/recon_conjecture/tools/search")
import networkx as nx
import small_graphs as sg

# ---- Lean reading (independent of sg.canon): Basic.lean Hypomorphic / Reconstructible ----
def lean_card(G, x):
    # G.induce ({x}ᶜ), vertex type is the subtype; keep labels (no relabel)
    return G.subgraph([v for v in G.nodes() if v != x]).copy()

class CardClasses:
    def __init__(self): self.reps = []
    def cid(self, C):
        for i, R in enumerate(self.reps):
            if R.number_of_nodes() == C.number_of_nodes() and nx.is_isomorphic(R, C):
                return i
        self.reps.append(C); return len(self.reps) - 1

CC = CardClasses()
def card_ids(G):
    return [CC.cid(lean_card(G, x)) for x in sorted(G.nodes())]

def lean_hypomorphic(G, H, gi=None, hi=None):
    # ∃ σ : V ≃ W, ∀ x, Nonempty (card G x ≃g card H (σ x)); brute force over all bijections
    if G.number_of_nodes() != H.number_of_nodes(): return False  # no bijection V ≃ W
    gi = gi if gi is not None else card_ids(G)
    hi = hi if hi is not None else card_ids(H)
    n = len(gi)
    for p in itertools.permutations(range(n)):
        if all(gi[x] == hi[p[x]] for x in range(n)):
            return True
    return False

def lean_iso(G, H): return nx.is_isomorphic(G, H)

# ---- English reading: deck = multiset of cards up to iso; reconstructible ----
def en_hypomorphic(G, H): return sg.hypomorphic(G, H)

def run():
    mism = []
    stats = {}
    for n in range(0, 7):
        gs = list(sg.all_graphs(n))
        ids = [card_ids(G) for G in gs]
        hyp_pairs = nonid_hyp = 0
        lean_recon_all = en_recon_all = True
        for i, G in enumerate(gs):
            lean_rec = True; en_rec = True
            for j, H in enumerate(gs):
                lh = lean_hypomorphic(G, H, ids[i], ids[j])
                eh = en_hypomorphic(G, H)
                if lh != eh: mism.append(("hyp", n, sg.g6(G), sg.g6(H), lh, eh))
                iso = lean_iso(G, H)
                if lh: hyp_pairs += 1
                if lh and not iso: lean_rec = False; nonid_hyp += 1
                if eh and not iso: en_rec = False
            if lean_rec != en_rec: mism.append(("recon", n, sg.g6(G), lean_rec, en_rec))
            lean_recon_all &= lean_rec; en_recon_all &= en_rec
        # statement level: Lean: 3 <= n -> all reconstructible ; English: "at least 3 vertices"
        lean_stmt_n = (not (3 <= n)) or lean_recon_all
        en_stmt_n = (not (n >= 3)) or en_recon_all
        if lean_stmt_n != en_stmt_n: mism.append(("stmt", n))
        stats[n] = dict(graphs=len(gs), hyp_pairs=hyp_pairs, hyp_nonISO_pairs=nonid_hyp,
                        all_recon_lean=lean_recon_all, all_recon_en=en_recon_all,
                        stmt_lean=lean_stmt_n, stmt_en=en_stmt_n)
        print(n, stats[n], flush=True)
    return mism

def labelled_check(n):
    # Lean quantifies over ALL labelled H on Fin n, not iso classes: check invariance at n<=4
    pairs = list(itertools.combinations(range(n), 2))
    gs = []
    for mask in range(1 << len(pairs)):
        G = nx.Graph(); G.add_nodes_from(range(n))
        G.add_edges_from(p for k, p in enumerate(pairs) if mask >> k & 1)
        gs.append(G)
    ids = [card_ids(G) for G in gs]
    bad = 0; hyp = 0
    for i, G in enumerate(gs):
        for j, H in enumerate(gs):
            lh = lean_hypomorphic(G, H, ids[i], ids[j])
            hyp += lh
            if lh != en_hypomorphic(G, H): bad += 1
            if lh and not lean_iso(G, H) and n >= 3: bad += 1
    print("labelled n=%d graphs=%d hyp_pairs=%d bad=%d" % (n, len(gs), hyp, bad))
    return bad

t = time.time()
m = run()
b = sum(labelled_check(n) for n in range(0, 5))
print("mismatches:", m[:20], "count", len(m), "labelled bad", b, "time %.1fs" % (time.time() - t))
