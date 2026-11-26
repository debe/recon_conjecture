"""Exhaustive n = 8 (graphs built by one-vertex extension, no geng needed): the residual of this
step in both branches and its meeting with C3.  Evidence only.   python3 t1tri_n8.py
Only graphs with G and its complement connected are classified (the residual lies there)."""
import importlib.util
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import t1tri_lib as L  # noqa: E402
import t1tri_stats as ST  # noqa: E402
from small_graphs import g6  # noqa: E402

spec = importlib.util.spec_from_file_location(
    "parent_t1_stats", os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2", "t1_stats.py"))
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

c = Counter()
for G in mod.graphs(8):
    c["all"] += 1
    fl = ST.residual_flags(G)
    if not fl["rem_parent"]:
        continue
    c["parent remainder " + fl["branch"]] += 1
    m = bool(L.c3_triples(G, "M"))
    o = bool(L.c3_triples(G, "OI"))
    c["parent remainder %s in C3(M)" % fl["branch"]] += m
    if fl["res"]:
        c["residual " + fl["branch"]] += 1
        c["residual %s in C3(M)" % fl["branch"]] += m
        c["residual %s in C3(OI)" % fl["branch"]] += o
    print("  parent remainder:", g6(G), fl, "C3(M)", m, "C3(OI)", o, flush=True)
print(8, dict(c))
