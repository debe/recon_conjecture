"""Where do the known residual members sit, and does the strong single-card form of Theorem U
hold on them?  Evidence only.     python3 .../t1us_probe_named.py

For each named graph: branch, old classes, frozen-remainder membership, (a, b), number of US
vertices, and claim() of t1us_claims.py (every two-walk-(a,b)-linear re-attachment at every
vertex: relation REL, at most one alternative when nonsingular, alternative isomorphic to G
when a card isomorphism does not extend).
"""
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1us_lib import named, classify, two_walk_linear, minus, shrikhande  # noqa: E402
from t1us_stats import us_vertices, n_alternatives  # noqa: E402
from t1us_claims import claim  # noqa: E402

graphs = named() + [("coShrikhande-v", minus(nx.complement(shrikhande())))]
for name, G in graphs:
    c = classify(G)
    ab = two_walk_linear(G)
    if ab is None:
        print(name, "n=%d" % G.number_of_nodes(), c, "not two-walk-linear", flush=True)
        continue
    us = us_vertices(G)
    alts = sorted({n_alternatives(G, u, ab) for u in G})
    print(name, "n=%d" % G.number_of_nodes(), c, "(a,b)=(%s,%s)" % ab, "US vertices=%d" % len(us),
          "alternatives per vertex=%s" % alts, "claim=%s" % claim(G), flush=True)
