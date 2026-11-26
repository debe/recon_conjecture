"""Red team on t2.md (Theorem W3). Independent brute-force transcription of the W3 Lean body
of t2.md section 10 (no shared code with t2_lib.py). Evidence only.

Graphs are adjacency sets on range(n). Marked types: canonical form of (K - deleted; marks)
by brute force over permutations of the unmarked vertices.

census-form test (what the paper argument uses of H): for G with a W3 witness (u, v, w)
[(W) and (K) as in the Lean body], every H on n vertices with the degree multiset of G and
|R_H| < |A_H| (computed in H, against the reference types of G, H's own degrees in the
window) must be isomorphic to G.
"""
import itertools, random, sys
from collections import defaultdict

def adj_of(G):
    n = G.number_of_nodes()
    A = [set() for _ in range(n)]
    for a, b in G.edges():
        A[a].add(b); A[b].add(a)
    return A

def mtype(A, deleted, marks):
    """canonical form of A minus `deleted` with ordered marks."""
    rest = [x for x in range(len(A)) if x not in deleted and x not in marks]
    best = None
    for perm in itertools.permutations(rest):
        order = list(marks) + list(perm)
        bits = tuple(1 if order[j] in A[order[i]] else 0
                     for i in range(len(order)) for j in range(i + 1, len(order)))
        if best is None or bits < best:
            best = bits
    return (len(marks), best)

def auts_fixing(A, deleted, z):
    """automorphisms of A - deleted fixing z, as dicts."""
    S = [x for x in range(len(A)) if x not in deleted]
    rest = [x for x in S if x != z]
    out = []
    for perm in itertools.permutations(rest):
        g = dict(zip(rest, perm)); g[z] = z
        if all((g[b] in A[g[a]]) == (b in A[a]) for a, b in itertools.combinations(S, 2)):
            out.append(g)
    return out

class Tab:
    def __init__(self, A):
        n = len(A); self.A = A; self.n = n
        self.deg = [len(A[x]) for x in range(n)]
        self.c3 = {}; self.p3 = {}
        for x, y, z in itertools.permutations(range(n), 3):
            self.c3[(x, y, z)] = mtype(A, {x}, (y, z))
            self.p3[(x, y, z)] = mtype(A, {x, y}, (z,))

def sets_against(TH, TG, u, v, w):
    """A_H, R_H of H (table TH) against the references of G (table TG)."""
    ref = TG.c3[(u, v, w)]
    AG = [t for t, ty in TG.c3.items() if ty == ref]
    ctypes = {TG.c3[(y, x, z)] for (x, y, z) in AG}
    port = TG.p3[(u, v, w)]
    dv = TG.deg[v]
    if v in TG.A[u]:
        win = {dv - 1, dv}
    else:
        win = {dv, dv + 1}
    AH = [t for t, ty in TH.c3.items() if ty == ref]
    RH = [t for t in TH.c3 if TH.p3[t] == port and TH.deg[t[0]] in win and TH.c3[t] not in ctypes]
    return AG, AH, RH

def killK(TG, AG):
    A = TG.A
    for (x, y, z) in AG:
        S = [t for t in range(TG.n) if t not in (x, y)]
        for g in auts_fixing(A, {x, y}, z):
            triv = all((g[t] in A[x]) == (t in A[x]) for t in S)
            dp = all(TG.deg[g[t]] == TG.deg[t] for t in S)
            if not (triv or dp):
                return False
    return True

def w3_witnesses(TG):
    out = []
    for (u, v, w) in itertools.permutations(range(TG.n), 3):
        AG, _, RG = sets_against(TG, TG, u, v, w)
        if len(RG) < len(AG) and killK(TG, AG):
            out.append((u, v, w))
    return out

def canon(A):
    return mtype(A, set(), ())

if __name__ == "__main__":
    import networkx as nx
    sys.path.insert(0, "/home/db/repositories/recon_conjecture/tools/search")
    from small_graphs import all_graphs
    nmax = int(sys.argv[1])
    for n in range(3, nmax + 1):
        gs = [adj_of(nx.convert_node_labels_to_integers(G)) for G in all_graphs(n)]
        tabs = [Tab(A) for A in gs]
        cans = [canon(A) for A in gs]
        byds = defaultdict(list)
        for i, A in enumerate(gs):
            byds[tuple(sorted(len(a) for a in A))].append(i)
        inW3 = 0; tested = 0; nokill_pass = 0
        for i, A in enumerate(gs):
            TG = tabs[i]
            wit = []
            # every class with (W), with and without (K)
            seen = set()
            for (u, v, w) in itertools.permutations(range(n), 3):
                if TG.c3[(u, v, w)] in seen: continue
                seen.add(TG.c3[(u, v, w)])
                AG, _, RG = sets_against(TG, TG, u, v, w)
                if not len(RG) < len(AG): continue
                k = killK(TG, AG)
                if k: wit.append((u, v, w))
                for j in byds[tuple(sorted(TG.deg))]:
                    _, AH, RH = sets_against(tabs[j], TG, u, v, w)
                    if len(RH) < len(AH):
                        iso = cans[j] == cans[i]
                        if k:
                            tested += 1
                            if not iso:
                                print("WITNESS", n, i, (u, v, w), j); sys.exit(1)
                        elif not iso:
                            nokill_pass += 1
            inW3 += bool(wit)
        print(f"n={n}: graphs={len(gs)} inW3={inW3} H-tested={tested} nonisoH-pass-without-K={nokill_pass}")
