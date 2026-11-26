"""Exhaustive n = 8 run for sketch t1 (no geng needed: graphs built by one-vertex extension).
Evidence only.   python3 .../t1us_n8.py

Runs claim() of t1us_claims.py on every graph on 8 vertices and prints the size of class US
and its intersection with the earlier classes.
"""
import importlib.util
import os
import sys
from collections import Counter

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from t1us_lib import two_walk_linear, classify, g6  # noqa: E402
from t1us_claims import claim  # noqa: E402
from t1us_stats import us_vertices  # noqa: E402

spec = importlib.util.spec_from_file_location(
    "parent_t1_stats", os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2",
                                    "t1_stats.py"))
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

c = Counter()
for G in mod.graphs(8):
    c["all"] += 1
    if two_walk_linear(G) is None:
        continue
    c["2wl non-regular"] += 1
    if not claim(G):
        print("WITNESS against claim:", g6(G), flush=True)
        c["witness"] += 1
    us = us_vertices(G)
    if us:
        c["US"] += 1
        cl = classify(G)
        if cl["branch"]:
            c["US in branch " + cl["branch"]] += 1
            if not cl["pure"]:
                c["US, branch, not pure"] += 1
                if not cl["D"]:
                    c["US, branch, not pure, not D"] += 1
                    print("  US member outside pure and D:", g6(G), cl, flush=True)
print(dict(sorted(c.items())))
