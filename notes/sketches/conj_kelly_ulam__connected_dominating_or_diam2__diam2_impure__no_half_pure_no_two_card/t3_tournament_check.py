"""What breaks in Theorem T for Stockmeyer's tournaments B_k, C_k (n = 2^k + 1)? Evidence only.

Tournament analogue of the hypotheses, for an ordered pair (u, v) of T:
  (a+)  (T - u, v) ~ (T - v, u) as pointed tournaments;
  (b+)  the pointed class of (u, v) holds more than half of the ordered pairs (x, y) with
        T - x - y ~ T - u - v.
Steps 1, 2, 4, 6 of the argument (pointed census, symmetric pair, twist, factorization) do not
use that the structure is a graph, so for such a pair the other tournament must be a twist
T_g by an automorphism g of T - u - v. Printed: the pairs with (a+), (b+); for each twist that
is isomorphic to the other tournament, whether g preserves scores on S, whether the scores
of the anchored pair agree (step 3: fails for tournaments, the card does not show the score),
and whether the score multiset on S agrees (step 5).
"""
import io
import itertools
import os
import sys
from collections import Counter, defaultdict
from contextlib import redirect_stdout

import networkx as nx
from networkx.algorithms.isomorphism import DiGraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2"))
with redirect_stdout(io.StringIO()):
    from t1_stockmeyer_check import stockmeyer, hypomorphic, iso  # noqa: E402


def sub(T, drop):
    return T.subgraph([w for w in T if w not in drop])


def pointed_iso(T, x, y, R, u, v):
    A = nx.DiGraph(sub(T, (x,)))
    B = nx.DiGraph(sub(R, (u,)))
    for w in A:
        A.nodes[w]["m"] = int(w == y)
    for w in B:
        B.nodes[w]["m"] = int(w == v)
    return DiGraphMatcher(A, B, node_match=lambda p, q: p["m"] == q["m"]).is_isomorphic()


def analyse(T, other, name):
    V = sorted(T)
    reps = []
    ty = {}
    for x, y in itertools.combinations(V, 2):
        S = nx.DiGraph(sub(T, (x, y)))
        for i, R in enumerate(reps):
            if DiGraphMatcher(S, R).is_isomorphic():
                break
        else:
            reps.append(S)
            i = len(reps) - 1
        ty[(x, y)] = ty[(y, x)] = i
    tsize = Counter(ty.values())
    found = 0
    for u, v in itertools.combinations(V, 2):
        if not pointed_iso(T, u, v, T, v, u):
            continue
        cls = [(x, y) for (x, y) in ty if ty[(x, y)] == ty[(u, v)] and pointed_iso(T, x, y, T, u, v)]
        if not len(cls) > tsize[ty[(u, v)]] - len(cls):
            continue
        found += 1
        S = [w for w in V if w not in (u, v)]
        F = nx.DiGraph(sub(T, (u, v)))
        A = list(DiGraphMatcher(F, F).isomorphisms_iter())
        Nu = {x for x in S if T.has_edge(x, u)}          # in-neighbours of u inside S
        for g in A:
            newNu = {x for x in S if g[x] in Nu}
            H = nx.DiGraph(T)
            for x in S:
                if (x in Nu) != (x in newNu):
                    if H.has_edge(x, u):
                        H.remove_edge(x, u); H.add_edge(u, x)
                    else:
                        H.remove_edge(u, x); H.add_edge(x, u)
            if newNu != Nu and iso(H, other):
                pres = all(T.out_degree(g[x]) == T.out_degree(x) for x in S)
                same_u = H.out_degree(u) == T.out_degree(u)
                same_S = sorted(H.out_degree(x) for x in S) == sorted(T.out_degree(x) for x in S)
                print(f"   {name} pair {(u, v)}: twist by g gives the OTHER tournament; "
                      f"g preserves scores on S: {pres}; score of u unchanged: {same_u}; "
                      f"score multiset on S unchanged: {same_S}; |Aut F| = {len(A)}")
    print(f"{name}: n = {len(V)}, pairs with (a+), (b+): {found}")


for k in (2, 3):
    B, C = stockmeyer(k, "B"), stockmeyer(k, "C")
    print(f"k = {k}: hypomorphic {hypomorphic(B, C)}, isomorphic {iso(B, C)}")
    analyse(B, C, f"B_{k}")
    analyse(C, B, f"C_{k}")
