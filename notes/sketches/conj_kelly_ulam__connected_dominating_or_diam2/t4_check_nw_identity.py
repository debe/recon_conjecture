"""Section 7 of sketch t4: the counting identity behind the 'vertex Nash-Williams' attempt.

For graphs G, H on [n] and a bijection p, let D_p be the disagreement graph: xy is an edge of
D_p iff (xy in E(G)) != (p(x)p(y) in E(H)). Identity (every pair G, H, every k):
  sum over p of #{independent k-sets of D_p}
      = (n - k)! * sum over types F on k vertices of ind(F, G) * ind(F, H) * |Aut F|,
where ind counts k-subsets inducing F. For hypomorphic G, H the right side for k < n does not
change when H is replaced by G (Kelly), which gives
  sum_p I(D_p(G,H); -1) - sum_p I(D_p(G,G); -1) = (-1)^n (|Iso(G,H)| - |Aut G|).
Checked here for random pairs on n = 4, 5, 6. Evidence only.
"""
import itertools
import math
import os
import random
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import ctype  # noqa: E402
from networkx.algorithms.isomorphism import GraphMatcher  # noqa: E402


def lhs(G, H, k):
    n = len(G)
    tot = 0
    for p in itertools.permutations(range(n)):
        for A in itertools.combinations(range(n), k):
            if all(G.has_edge(x, y) == H.has_edge(p[x], p[y])
                   for x, y in itertools.combinations(A, 2)):
                tot += 1
    return tot


def rhs(G, H, k):
    n = len(G)

    def counts(X):
        c = Counter()
        rep = {}
        for A in itertools.combinations(range(n), k):
            t = ctype(X, set(range(n)) - set(A))
            c[t] += 1
            rep[t] = X.subgraph(A)
        return c, rep

    cg, rep = counts(G)
    ch, _ = counts(H)
    tot = 0
    for t in cg:
        if t in ch:
            aut = sum(1 for _ in GraphMatcher(rep[t], rep[t]).isomorphisms_iter())
            tot += cg[t] * ch[t] * aut
    return math.factorial(n - k) * tot


if __name__ == "__main__":
    rng = random.Random(1)
    bad = 0
    checks = 0
    for n, reps in ((4, 30), (5, 20), (6, 4)):
        for _ in range(reps):
            G = nx.gnp_random_graph(n, 0.5, seed=rng.randrange(1 << 30))
            H = nx.gnp_random_graph(n, 0.5, seed=rng.randrange(1 << 30))
            for k in range(0, n + 1):
                checks += 1
                if lhs(G, H, k) != rhs(G, H, k):
                    bad += 1
    print("checks", checks, "mismatches", bad)
