"""Red team on t2.md: targeted fuzz of Theorem W3 (census form) on random G, n = 8, 9.
H ranges over all twists of G (vertex x rewired through g in Aut(G - x - y), both values of the
bit xy) and G with one degree-preserving 2-switch; H kept if it has the degree multiset of G.
For every W3 witness class of G: |R_H| < |A_H| must imply H isomorphic to G. Evidence only."""
import itertools, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from redteam_t2w3 import Tab, sets_against, killK, canon, auts_fixing

def rand_graph(n, p, rng):
    A = [set() for _ in range(n)]
    for a, b in itertools.combinations(range(n), 2):
        if rng.random() < p:
            A[a].add(b); A[b].add(a)
    return A

def twists(A):
    n = len(A)
    out = []
    for x, y in itertools.permutations(range(n), 2):
        S = [t for t in range(n) if t not in (x, y)]
        for g in auts_fixing(A, {x, y}, S[0]) if False else all_auts(A, {x, y}):
            for bit in (0, 1):
                B = [set(a) for a in A]
                for t in range(n):
                    B[t].discard(x)
                B[x] = set()
                for t in S:
                    if g[t] in A[x]:
                        B[x].add(t); B[t].add(x)
                if bit:
                    B[x].add(y); B[y].add(x)
                out.append(B)
    return out

def all_auts(A, deleted):
    S = [x for x in range(len(A)) if x not in deleted]
    res = []
    for perm in itertools.permutations(S):
        g = dict(zip(S, perm))
        if all((g[b] in A[g[a]]) == (b in A[a]) for a, b in itertools.combinations(S, 2)):
            res.append(g)
    return res

def switches(A, rng, k):
    n = len(A); out = []
    E = [(a, b) for a in range(n) for b in A[a] if a < b]
    for _ in range(k):
        if len(E) < 2: break
        (a, b), (c, d) = rng.sample(E, 2)
        if len({a, b, c, d}) < 4 or d in A[a] or c in A[b]: continue
        B = [set(s) for s in A]
        B[a].discard(b); B[b].discard(a); B[c].discard(d); B[d].discard(c)
        B[a].add(d); B[d].add(a); B[b].add(c); B[c].add(b)
        out.append(B)
    return out

if __name__ == "__main__":
    n = int(sys.argv[1]); N = int(sys.argv[2]); seed = int(sys.argv[3])
    rng = random.Random(seed)
    stats = dict(G=0, inW3=0, Htested=0, Hpass=0)
    for it in range(N):
        A = rand_graph(n, rng.choice([0.3, 0.45, 0.6]), rng)
        TG = Tab(A); stats["G"] += 1
        cG = canon(A)
        ds = sorted(TG.deg)
        cls = []; seen = set()
        for (u, v, w) in itertools.permutations(range(n), 3):
            if TG.c3[(u, v, w)] in seen: continue
            seen.add(TG.c3[(u, v, w)])
            AG, _, RG = sets_against(TG, TG, u, v, w)
            if len(RG) < len(AG) and killK(TG, AG):
                cls.append((u, v, w))
        if not cls: print("NOT IN W3", A); continue
        stats["inW3"] += 1
        Hs = [B for B in twists(A) + switches(A, rng, 40) if sorted(len(b) for b in B) == ds]
        hc = {}
        for B in Hs:
            k = canon(B)
            if k != cG: hc[k] = B
        for B in hc.values():
            TH = Tab(B); stats["Htested"] += 1
            for (u, v, w) in cls:
                _, AH, RH = sets_against(TH, TG, u, v, w)
                if len(RH) < len(AH):
                    print("WITNESS", A, (u, v, w), B); sys.exit(1)
        print(it, stats, flush=True)
    print("DONE", stats)
