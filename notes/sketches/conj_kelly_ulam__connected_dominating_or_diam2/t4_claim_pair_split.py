"""Lemma G of sketch t4 (single-graph identity; non-vacuous).

For a graph G with m edges, a graph F on n - 2 vertices and a degree a, let
  pi_a(F) = number of ordered pairs (x, y), x != y, with G - x - y isomorphic to F, deg x = a
  e_a(F)  = number of those pairs with x adjacent to y
  s       = m - |E(F)|.
Claim:  e_a(F) = sum over j >= a of (pi_j(F) - pi_{s-j}(F)).

pi is read off the deck (each card G - x shows deg x and the multiset of its own cards), so
the identity makes e_a(F) a deck invariant.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import pair_table  # noqa: E402


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    m = G.number_of_edges()
    pi, e = pair_table(G)
    types = {F for (F, _) in pi}
    for F in types:
        s = m - len(F[1])
        for a in range(0, n + 1):
            rhs = sum(pi.get((F, j), 0) - pi.get((F, s - j), 0) for j in range(a, n + 2))
            if rhs != e.get((F, a), 0):
                return False
    return True
