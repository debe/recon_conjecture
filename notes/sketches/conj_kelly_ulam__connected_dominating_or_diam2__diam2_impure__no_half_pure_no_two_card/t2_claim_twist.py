"""Claim (twist obstruction, sketch t2 section 2): a level-wise half-pure vertex u (the vertex
of Theorem D) is untwisted, i.e. every card isomorphism alpha : G - u' -> G - u maps N(u') onto
N(u). Evidence only.

  python3 tools/search/small_graphs.py counterexample --claim notes/sketches/<step>/t2_claim_twist.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2_lib import half_pure_vertices, triv  # noqa: E402

STATS = {"graphs": 0, "half_pure_vertices": 0, "twisted_vertices": 0}


def claim(G):
    if G.number_of_nodes() < 3:
        return True
    STATS["graphs"] += 1
    hp = set(half_pure_vertices(G))
    for u in G.nodes():
        t = len(triv(G, u))
        if t >= 2:
            STATS["twisted_vertices"] += 1
        if u in hp:
            STATS["half_pure_vertices"] += 1
            if t != 1:
                return False
    return True


import atexit  # noqa: E402

atexit.register(lambda: print("t2_claim_twist stats:", STATS))
