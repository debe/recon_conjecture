"""Claim file for tools/search/small_graphs.py counterexample.

Proposition M of sketch t3 (pointed refinement never breaks a tie), single-graph form.
CLAIM: if an ordered triple (u; v, w) satisfies clause (a1) of the apex census
  (every (x; y, z) with (G-x-y; z) ~ (G-u-v; w) has the 2-pointed type of (u; v, w) or (v; u, w)),
then every ordered pair (x, y) with G-x-y ~ G-u-v has the pointed type of (u, v) or of (v, u).
So the zero-remainder pair census of T+ (resp. T) holds at (u, v) whenever the apex triple
census holds at (u; v, w) for some w.  Evidence only.
"""
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3o_lib import ctype, pointed2del_key, pointed_classes


def claim(G):
    if G.number_of_nodes() < 4:
        return True
    cid2 = pointed_classes(G, 2)
    cid3 = pointed_classes(G, 3)
    ty2 = {p: ctype(G, p) for p in cid2}
    p2 = {t: pointed2del_key(G, *t) for t in cid3}
    by_p2 = defaultdict(set)
    for t, key in p2.items():
        by_p2[key].add(cid3[t])
    by_f = defaultdict(set)
    for p, F in ty2.items():
        by_f[F].add(cid2[p])
    for (u, v, w) in cid3:
        if by_p2[p2[(u, v, w)]] <= {cid3[(u, v, w)], cid3[(v, u, w)]}:
            if not by_f[ty2[(u, v)]] <= {cid2[(u, v)], cid2[(v, u)]}:
                return False
    return True
