"""Red team (round 13) independent recount of t2 section 7 phantoms (evidence only).
Weak F-phantom: K not iso G, same degree multiset, same slice over F (counter of pointed types
(K-a, b) over ordered pairs with K-a-b ~ F; equal counters include equal totals).
Keyed: also same multiset of (deg, w2).  Own pointed canonical form, independent of t2s_lib.
usage: python3 redteam_t2_phantoms.py NMIN NMAX"""
import sys, itertools
from collections import Counter, defaultdict
sys.path.insert(0, '/home/db/repositories/recon_conjecture/tools/search')
import networkx as nx
from small_graphs import all_graphs, canon, _leaves

def pcanon(adj, n, marks):
    # adj: dict v->set over vertex list verts; marks: list of distinguished vertices (ordered)
    verts = sorted(adj)
    idx = {v: i for i, v in enumerate(verts)}
    A = [frozenset(idx[u] for u in adj[v]) for v in verts]
    m = [idx[s] for s in marks]
    rest = [i for i in range(len(verts)) if i not in m]
    cells = [[i] for i in m] + ([rest] if rest else [])
    best = None
    for order in _leaves(A, cells):
        pos = {v: i for i, v in enumerate(order)}
        b = tuple(sorted((min(pos[a], pos[c]), max(pos[a], pos[c])) for a in range(len(verts)) for c in A[a] if a < c))
        if best is None or b < best:
            best = b
    return (len(verts), best)

def delete(adj, S):
    return {v: adj[v] - S for v in adj if v not in S}

def slices(adj):
    sl = defaultdict(Counter)
    for x in adj:
        for y in adj:
            if x == y: continue
            F = pcanon(delete(adj, {x, y}), 0, [])
            sl[F][pcanon(delete(adj, {x}), 0, [y])] += 1
    return sl

def keys(adj):
    return Counter((len(adj[x]), sum(len(adj[y]) for y in adj[x])) for x in adj)

def graphs8():
    seen = set()
    for H in all_graphs(7):
        for r in range(128):
            G = H.copy(); G.add_node(7)
            for i in range(7):
                if r >> i & 1: G.add_edge(i, 7)
            c = canon(G)
            if c in seen: continue
            seen.add(c); yield G

def pairtypes(adj, F):
    P = [(x, y) for x in adj for y in adj if x != y and pcanon(delete(adj, {x, y}), 0, []) == F]
    return [(pcanon(delete(adj, {x}), 0, [y]), pcanon(delete(adj, {y}), 0, [x])) for x, y in P]

def main(nmin, nmax):
    for n in range(nmin, nmax + 1):
        rp = 0
        weak = keyed = outPC = pairs_outPCp = 0
        rep = 0
        graphs = 0
        for G in (graphs8() if n == 8 else all_graphs(n)):
            graphs += 1
            adj = {v: set(G[v]) for v in G}
            cG = pcanon(adj, 0, [])
            dG = Counter(len(adj[v]) for v in adj); kG = keys(adj)
            slG = None
            Ks = {}
            for x in adj:
                others = [v for v in adj if v != x]
                for A in itertools.combinations(others, len(adj[x])):
                    K = {v: set(adj[v]) - {x} for v in adj if v != x}
                    K[x] = set(A)
                    for a in A: K[a].add(x)
                    if Counter(len(K[v]) for v in K) != dG: continue
                    c = pcanon(K, 0, [])
                    if c == cG or c in Ks: continue
                    Ks[c] = K
            if not Ks: continue
            slG = slices(adj)
            weakF = set(); keyF = set()
            for c, K in Ks.items():
                slK = slices(K)
                kk = keys(K) == kG
                for F, cnt in slG.items():
                    if slK.get(F) == cnt:
                        weak += 1; weakF.add(F)
                        if not set(pairtypes(K, F)) & set(pairtypes(adj, F)):
                            rp += 1; print('RE-PAIRED weak phantom', n, F)
                        if kk:
                            keyed += 1; keyF.add(F)
                            print('KEYED phantom', n, nx.to_graph6_bytes(G, header=False).decode().strip(), F)
            if weakF == set(slG): outPC += 1; print('outside PC', n)
            if keyF == set(slG): print('OUTSIDE PC+', n)
        print('n=%d graphs=%d weak phantoms (G,F,K)=%d keyed=%d graphs outside PC=%d re-paired=%d' % (n, graphs, weak, keyed, outPC, rp), flush=True)

main(int(sys.argv[1]), int(sys.argv[2]))
