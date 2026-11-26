"""Red team (round 13): independent test of Theorem Sw of t1.md, encoded from the Lean body of
the proposed child `aligned_switch_kelly4` (not from t1s_lib.py).

claim(G): for EVERY permutation pi of V that preserves the isomorphism type of every card
(G - x ~ G - pi x), the aligned hypomorph H' = pi(G) (sigma = id is then a hypomorphism G -> H')
has difference set D = E(G) xor E(H') with
  (1) every pair {w,y} of D, in BOTH orders, satisfying the Lean switchable clause
      (exists y1 w1 outside {w,y}, the four degree lines split by adjacency, and
       G - {w,y1} ~ G - {y,w1});
  (2) the Lean degree-balance clause at every v and k;
  (3) the induced counts of every graph on <= 4 vertices (k < n) equal in G xor D and G.
Since every hypomorph of a graph on n <= 13 vertices is isomorphic to it, H' = pi(G) over all
card-type-preserving pi covers every aligned pair (sigma = id) for these n: the test is
exhaustive in H for each G whenever the permutation group is enumerated fully (cap 5000;
over the cap a random sample of 300 is used and the claim still must hold).
Fidelity: (1)-(3) are transcribed line by line from the Lean body in t1.md section 9.
"""
import itertools
import math
import random
from collections import defaultdict

import networkx as nx


def wl_key(G):
    return nx.weisfeiler_lehman_graph_hash(G)


def iso(A, B):
    if A.number_of_nodes() != B.number_of_nodes() or A.number_of_edges() != B.number_of_edges():
        return False
    if sorted(d for _, d in A.degree()) != sorted(d for _, d in B.degree()):
        return False
    return nx.is_isomorphic(A, B)


def minus(G, S):
    H = G.copy()
    H.remove_nodes_from(S)
    return H


def switchable(G, w, y, deg):
    V = list(G.nodes())
    adj = G.has_edge(w, y)
    for y1 in V:
        if y1 in (w, y):
            continue
        a1 = G.has_edge(w, y1)
        if adj:
            ok1 = (deg[y1] == deg[y] + 1) if a1 else (deg[y1] == deg[y])
        else:
            ok1 = (deg[y1] == deg[y]) if a1 else (deg[y1] + 1 == deg[y])
        if not ok1:
            continue
        for w1 in V:
            if w1 in (w, y):
                continue
            b1 = G.has_edge(y, w1)
            if adj:
                ok2 = (deg[w1] == deg[w] + 1) if b1 else (deg[w1] == deg[w])
            else:
                ok2 = (deg[w1] == deg[w]) if b1 else (deg[w1] + 1 == deg[w])
            if not ok2:
                continue
            if iso(minus(G, [w, y1]), minus(G, [y, w1])):
                return True
    return False


def small_counts(G, kmax):
    n = G.number_of_nodes()
    out = defaultdict(int)
    for k in range(0, min(kmax, n - 1) + 1):
        for S in itertools.combinations(sorted(G.nodes()), k):
            sub = G.subgraph(S)
            # canonical form for <= 4 vertices: sorted degree seq + edges suffices up to iso
            key = (k, sub.number_of_edges(), tuple(sorted(d for _, d in sub.degree())))
            out[key] += 1
    return out


def claim(G):
    V = sorted(G.nodes())
    n = len(V)
    if n < 3:
        return True
    deg = dict(G.degree())
    cards = {v: minus(G, [v]) for v in V}
    cls = []
    for v in V:
        for c in cls:
            if iso(cards[c[0]], cards[v]):
                c.append(v)
                break
        else:
            cls.append([v])
    total = math.prod(math.factorial(len(c)) for c in cls)
    if total <= 5000:
        perms = itertools.product(*[itertools.permutations(c) for c in cls])
    else:
        rng = random.Random(n * 7919 + G.number_of_edges())
        def gen():
            for _ in range(300):
                yield tuple(tuple(rng.sample(c, len(c))) for c in cls)
        perms = gen()
    E = {frozenset(e) for e in G.edges()}
    c0 = None
    swcache = {}
    for img in perms:
        p = {}
        for c, d in zip(cls, img):
            p.update(dict(zip(c, d)))
        EH = {frozenset((p[a], p[b])) for a, b in G.edges()}
        Dset = E ^ EH
        if not Dset:
            continue
        for e in Dset:
            a, b = tuple(e)
            for (w, y) in ((a, b), (b, a)):
                if (w, y) not in swcache:
                    swcache[(w, y)] = switchable(G, w, y, deg)
                if not swcache[(w, y)]:
                    print('Sw fails', nx.to_graph6_bytes(G, header=False), (w, y), p)
                    return False
        bal = defaultdict(int)
        for e in Dset:
            a, b = tuple(e)
            s = 1 if G.has_edge(a, b) else -1
            bal[(a, deg[b])] += s
            bal[(b, deg[a])] += s
        if any(bal.values()):
            print('balance fails', nx.to_graph6_bytes(G, header=False), p)
            return False
        if c0 is None:
            c0 = small_counts(G, 4)
        X = nx.Graph()
        X.add_nodes_from(V)
        X.add_edges_from(tuple(e) for e in EH)
        if small_counts(X, 4) != c0:
            print('kelly fails', nx.to_graph6_bytes(G, header=False), p)
            return False
    return True
