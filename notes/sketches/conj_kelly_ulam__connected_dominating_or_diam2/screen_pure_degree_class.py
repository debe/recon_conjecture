"""Falsity screen for child conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class.

Lean: Recon.ClassReconstructible (fun n G => P n G); encoded as
  claim(G) := n < 3 or not P(G) or Reconstructible(G),
with P = has_pure_class(G) (clauses from screen_lib.py, each a clause-by-clause transcription of the Lean
body) and Reconstructible exact for n <= 7 (deck class over all graphs on n vertices is a
single isomorphism class). Atexit prints how many graphs per n lie in the class
(non-vacuity evidence).
"""
import atexit
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from screen_lib import *  # noqa: E402,F401,F403
import screen_lib  # noqa: E402

atexit.register(screen_lib.report)


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    if not has_pure_class(G):
        return True
    screen_lib.STATS[n] += 1
    return reconstructible(G)
