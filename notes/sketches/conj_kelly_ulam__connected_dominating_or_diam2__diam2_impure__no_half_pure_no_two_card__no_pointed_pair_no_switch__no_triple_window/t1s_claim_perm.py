"""Claim file for tools/search/small_graphs.py counterexample (evidence only).

Theorem Sw of t1.md, tested on aligned pairs that exist for every n: H = pi(G) for a permutation
pi that preserves the isomorphism type of the card of every vertex (then H - v ~ G - v for all v).
For each such H the difference set D = E(G) xor E(H) must be contained in Sw(G) and in the
three-card form Sw3(G), and must be degree-balanced.  pi ranges over all transpositions inside
card classes and over 6 random products of them.
Also Proposition TW: G in NS implies that vertices with isomorphic cards are twins.
"""
import itertools
import os
import random
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import t1s_lib as L  # noqa: E402


def claim(G):
    V = sorted(G.nodes())
    deg = dict(G.degree())
    cc = {v: L.canon(L.card(G, v)) for v in V}
    cls = defaultdict(list)
    for v in V:
        cls[cc[v]].append(v)
    perms = []
    for c in cls.values():
        for a, b in itertools.combinations(c, 2):
            p = {v: v for v in V}
            p[a], p[b] = b, a
            perms.append(p)
    rng = random.Random(len(V) * 1000 + G.number_of_edges())
    for _ in range(6):
        p = {}
        for c in cls.values():
            d = c[:]
            rng.shuffle(d)
            p.update(dict(zip(c, d)))
        perms.append(p)
    Sw = L.sw_pairs(G)
    Sw3 = L.sw3_pairs(G)
    E = {frozenset(e) for e in G.edges()}
    nontrivial = False
    for p in perms:
        EH = {frozenset((p[a], p[b])) for a, b in G.edges()}
        D = {tuple(sorted(e)) for e in E ^ EH}
        if not D:
            continue
        nontrivial = True
        if not (D <= Sw and D <= Sw3):
            return False
        bal = defaultdict(int)
        for a, b in D:
            s = 1 if G.has_edge(a, b) else -1
            bal[(a, deg[b])] += s
            bal[(b, deg[a])] += s
        if any(bal.values()):
            return False
    if nontrivial and not L.has_balanced(G, Sw3):
        return False          # Proposition TW would fail
    return True
