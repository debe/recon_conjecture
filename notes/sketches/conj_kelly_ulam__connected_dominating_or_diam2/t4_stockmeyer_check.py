"""Section 8 of sketch t4: do Lemma G and Lemma P have tournament analogues? Evidence only.

Uses Stockmeyer's tournaments B_k, C_k as built (and checked hypomorphic, non-isomorphic) in
t1_stockmeyer_check.py. For a tournament the analogue of the table of Lemma G is
  E(T) = multiset of (score of x, type of T - x - y) over the arcs x -> y.
Graph case: the table over adjacent pairs is a deck invariant (Lemma G). Printed here: whether
B_k and C_k have the same table, the same score sequence, and whether the pure-class
hypothesis of Lemma P (all two-deleted types pure for some score class) holds for them.
"""
import io
import itertools
import os
import sys
from collections import Counter
from contextlib import redirect_stdout

import networkx as nx
from networkx.algorithms.isomorphism import DiGraphMatcher

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
with redirect_stdout(io.StringIO()):
    from t1_stockmeyer_check import stockmeyer, hypomorphic, iso  # noqa: E402


def type_index(T, drop, reps):
    S = T.subgraph([w for w in T if w not in drop])
    for i, R in enumerate(reps):
        if DiGraphMatcher(S, R).is_isomorphic():
            return i
    reps.append(nx.DiGraph(S))
    return len(reps) - 1


def table(T, reps):
    out = Counter()
    for x, y in T.edges():
        out[(T.out_degree(x), type_index(T, (x, y), reps))] += 1
    return out


for k in (2, 3):
    B, C = stockmeyer(k, "B"), stockmeyer(k, "C")
    reps = []
    tb, tc = table(B, reps), table(C, reps)
    two_b = Counter(type_index(B, p, reps) for p in itertools.combinations(B, 2))
    two_c = Counter(type_index(C, p, reps) for p in itertools.combinations(C, 2))
    print(f"k={k} n={2**k+1}: hypomorphic {hypomorphic(B, C)}, isomorphic {iso(B, C)}, "
          f"same score sequence {sorted(d for _, d in B.out_degree()) == sorted(d for _, d in C.out_degree())}, "
          f"same two-deleted deck {two_b == two_c}, "
          f"same (score of tail, type) table over arcs {tb == tc}, "
          f"two-deleted types all distinct: B {max(two_b.values()) == 1}, C {max(two_c.values()) == 1}")
