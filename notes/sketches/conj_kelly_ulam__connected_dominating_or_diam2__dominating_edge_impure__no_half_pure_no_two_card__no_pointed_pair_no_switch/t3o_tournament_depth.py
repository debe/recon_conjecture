"""Anchoring depth of Stockmeyer's pair (B_k, C_k), n = 2^k + 1. Evidence only.

k-anchored: tuples p in B, q in C and isomorphisms e_i : B - p_i -> C - q_i with e_i(p_j) = q_j.
The triple twist lemma of the sketch is generic (it never uses that the structure is a graph),
so for a 3-anchored pair the coset triangle in Aut(B - p) must fail the Helly condition.
Printed: the number of j-anchorings (as partial bijections) for j = 1, 2, 3, ..., and for the
3-anchorings whether Helly holds on the B side.
Construction of B_k, C_k as in t1_stockmeyer_check.py (UNVERIFIED against Stockmeyer 1977; the
script there checks hypomorphic + non-isomorphic directly).
"""
import io
import itertools
import os
import sys
from contextlib import redirect_stdout

import networkx as nx
from networkx.algorithms.isomorphism import DiGraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2"))
with redirect_stdout(io.StringIO()):
    from t1_stockmeyer_check import stockmeyer, hypomorphic, iso  # noqa: E402


def pointed_ok(T, x, pts, R, a, qts):
    A = nx.DiGraph(T.subgraph([w for w in T if w != x]))
    B = nx.DiGraph(R.subgraph([w for w in R if w != a]))
    for w in A:
        A.nodes[w]["m"] = 0
    for w in B:
        B.nodes[w]["m"] = 0
    for i, w in enumerate(pts, 1):
        A.nodes[w]["m"] = i
    for i, w in enumerate(qts, 1):
        B.nodes[w]["m"] = i
    return DiGraphMatcher(A, B, node_match=lambda s, t: s["m"] == t["m"]).is_isomorphic()


def anchored(T, R, bij):
    """bij: tuple of (p_i, q_i)."""
    for i, (x, a) in enumerate(bij):
        rest = [pq for j, pq in enumerate(bij) if j != i]
        if not pointed_ok(T, x, [p for p, _ in rest], R, a, [q for _, q in rest]):
            return False
    return True


def auts(T, S):
    H = nx.DiGraph(T.subgraph(S))
    return list(DiGraphMatcher(H, H).isomorphisms_iter())


def helly(T, u, v, w):
    """Helly condition for the triple (u, v, w) of the tournament T, arcs to and from S."""
    S = [x for x in sorted(T) if x not in (u, v, w)]
    A = auts(T, S)

    def nb(z):
        return frozenset(x for x in S if T.has_edge(z, x))

    def im(g, X):
        return frozenset(g[x] for x in X)

    Nu, Nv, Nw = nb(u), nb(v), nb(w)
    via_w = {im(g, Nu) for g in A if im(g, Nw) == Nw}
    via_v = {im(g, Nu) for g in A if im(g, Nv) == Nv}
    triv = {im(g, Nu) for g in A if im(g, Nw) == Nw and im(g, Nv) == Nv}
    return (via_w & via_v) <= triv, len(A), len(via_w & via_v), len(triv)


for k in (2, 3):
    B, C = stockmeyer(k, "B"), stockmeyer(k, "C")
    n = 2 ** k + 1
    print(f"k={k} n={n}: hypomorphic {hypomorphic(B, C)}, isomorphic {iso(B, C)}")
    level = {((x, a),) for x in B for a in C if anchored(B, C, ((x, a),))}
    j = 1
    while level:
        print(f"   {j}-anchorings (partial bijections): {len(level)}")
        if j == 3:
            res = [helly(B, *[p for p, _ in bij]) for bij in sorted(level)]
            print("      Helly holds at", sum(1 for r in res if r[0]), "of", len(res),
                  "; (|Aut F3|, triangles, trivial) sample:", sorted(set(r[1:] for r in res))[:6])
        nxt = set()
        for bij in level:
            usedp = {p for p, _ in bij}
            usedq = {q for _, q in bij}
            for x in B:
                if x in usedp:
                    continue
                for a in C:
                    if a in usedq:
                        continue
                    cand = tuple(sorted(bij + ((x, a),)))
                    if cand in nxt:
                        continue
                    if anchored(B, C, cand):
                        nxt.add(cand)
        level = nxt
        j += 1
    print(f"   anchoring depth: {j - 1}")

# Falsification test of the generic anchoring lemma: a triple with (a) a unique copy of the
# three-deleted tournament and (b) pairwise non-isomorphic two-deleted tournaments would force a
# 3-anchoring; the pairs above have none, so no such triple may exist.
from t3o_digraph_redteam import ab_triples  # noqa: E402
import itertools as _it  # noqa: E402
from collections import Counter as _C  # noqa: E402

for k in (2, 3):
    for name in ("B", "C"):
        T = stockmeyer(k, name)
        V = sorted(T)
        trip = list(_it.combinations(V, 3))
        reps = []
        cnt = _C()
        for t in trip:
            F = nx.DiGraph(T.subgraph([x for x in V if x not in t]))
            for i, R in enumerate(reps):
                if DiGraphMatcher(F, R).is_isomorphic():
                    cnt[i] += 1
                    break
            else:
                reps.append(F)
                cnt[len(reps) - 1] += 1
        print(f"{name}_{k}: triples {len(trip)}, three-deleted types {len(reps)}, "
              f"unique-copy triples {sum(1 for c in cnt.values() if c == 1)}, "
              f"triples with (a), (b): {len(ab_triples(T))}")
