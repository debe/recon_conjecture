"""Class sizes for n <= N (exhaustive, evidence only):
T3u = unique copy of F3 + pairwise non-isomorphic two-deleted subgraphs + Helly;
T3  = apex census clauses + Helly;  T, T+ from the round-11 sketch (t3_lib of the twin dir)."""
import os
import sys
import time
import importlib.util
from collections import Counter

from t3o_lib import *
from small_graphs import all_graphs

HERE = os.path.dirname(os.path.abspath(__file__))
p = os.path.join(HERE, "..",
                 "conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card")
sys.path.insert(0, p)
spec = importlib.util.spec_from_file_location("r11", os.path.join(p, "t3_lib.py"))
r11 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r11)

N = int(sys.argv[1])
for n in range(4, N + 1):
    t0 = time.time()
    c = Counter()
    outside = []
    for G in all_graphs(n):
        G = nx.convert_node_labels_to_integers(G)
        ty = r11.pair_types(G)
        cid = r11.pointed_classes(G, ty)
        inT = bool(r11.T_pairs(G, ty, cid, "rigid"))
        inTp = bool(r11.Tplus_pairs(G, ty, cid))
        cid3 = pointed_classes(G, 3)
        t3u = bool(T3_triples(G))
        t3c = bool(T3_apex(G, cid3, "none"))
        t3 = bool(T3_apex(G, cid3, "helly"))
        c["all"] += 1
        c["T"] += inT
        c["T+"] += inTp
        c["T3u"] += t3u
        c["T3 census"] += t3c
        c["T3"] += t3
        c["T or T+"] += inT or inTp
        c["T3 or T3u"] += t3 or t3u
        if (t3 or t3u) and not (inT or inTp):
            c["(T3 or T3u) outside T, T+"] += 1
            outside.append(g6(G))
    print("n =", n, dict(c), "time %.0fs" % (time.time() - t0), flush=True)
    print("   new graphs (first 30):", outside[:30], flush=True)
