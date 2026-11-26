"""Red team (round 11) on sketch t2, abstract statement CORE (section 7), relaxed form.
Evidence only.

claim(G): if G has degrees d, d+1 (both present) and is equitable with parameters (d,q,b,e),
let P be the connected component of G in the parameter class under "agree off one vertex"
(BFS over all re-attachments of one vertex; capped).  F* = greatest subfamily of P in which
every member has, at every vertex, a different member agreeing with it off that vertex.
CORE says: G not in F*, or some low vertex of G has at most one further member of F* at it.
Returns False (= witness) if CORE fails.  Graphs whose component exceeds CAP are skipped (True).

Faithfulness: CORE quantifies over all families F with the common parameters; the hypothesis
is monotone in F and the conclusion antitone, and the component of G contains every member of
any admissible F reachable from G, so testing F* of the component is exact (up to the cap).
"""
import itertools
from collections import defaultdict

CAP = 60000


def params(adj, n):
    deg = [bin(m).count("1") for m in adj]
    lo, hi = min(deg), max(deg)
    if hi != lo + 1:
        return None
    high = 0
    for x in range(n):
        if deg[x] == hi:
            high |= 1 << x
    h = [bin(adj[x] & high).count("1") for x in range(n)]
    bs = {h[x] for x in range(n) if deg[x] == lo}
    es = {h[x] for x in range(n) if deg[x] == hi}
    if len(bs) != 1 or len(es) != 1:
        return None
    return (lo, bin(high).count("1"), bs.pop(), es.pop())


def reattach(adj, n, u, S):
    a = list(adj)
    full = (1 << n) - 1
    for x in range(n):
        if x == u:
            continue
        if S >> x & 1:
            a[x] |= 1 << u
        else:
            a[x] &= full ^ (1 << u)
    a[u] = S
    return tuple(a)


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    nodes = sorted(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [0] * n
    for a, b in G.edges():
        adj[idx[a]] |= 1 << idx[b]
        adj[idx[b]] |= 1 << idx[a]
    adj = tuple(adj)
    key = params(adj, n)
    if key is None:
        return True
    d = key[0]
    seen = {adj}
    stack = [adj]
    nbrs = defaultdict(lambda: [set() for _ in range(n)])
    while stack:
        K = stack.pop()
        for u in range(n):
            rest = ((1 << n) - 1) ^ (1 << u)
            for S in range(1 << n):
                if S >> u & 1:
                    continue
                if S == K[u]:
                    continue
                K2 = reattach(K, n, u, S)
                if params(K2, n) != key:
                    continue
                nbrs[K][u].add(K2)
                if K2 not in seen:
                    seen.add(K2)
                    if len(seen) > CAP:
                        return True
                    stack.append(K2)
    alive = set(seen)
    while True:
        dead = [K for K in alive if any(not (nbrs[K][u] & alive) for u in range(n))]
        if not dead:
            break
        alive.difference_update(dead)
    if adj not in alive:
        return True
    deg = [bin(m).count("1") for m in adj]
    low = [v for v in range(n) if deg[v] == d]
    if all(len(nbrs[adj][v] & alive) >= 2 for v in low):
        print("CORE WITNESS", key, len(alive))
        return False
    return True
