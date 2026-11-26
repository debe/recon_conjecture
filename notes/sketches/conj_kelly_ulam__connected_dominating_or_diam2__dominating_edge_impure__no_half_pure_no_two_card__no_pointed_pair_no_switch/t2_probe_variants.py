"""Which variants contain the given graphs?  (single-graph facts, evidence only)
old = census of T / T+ (clause (i) or symmetric), w = degree-window census."""
import sys
from t2_lib import *

MODES = ["TRIV", "K", "DP", "DPF", "DC", "SQ", "SQF", "LVF", "SEQ", "ISO"]
for s in sys.argv[1:]:
    G = from_g6(s)
    C = Census(G)
    pc, tc = pair_census(G, C), triple_census(G, C)
    pw, tw = pair_census_w(G, C), triple_census_w(G, C)
    print("==", s, "census classes: pair", len(pc), "triple", len(tc), "| window: pair", len(pw), "triple", len(tw))
    print("  pair    :", {m: in_pair_class(G, C, m) for m in MODES})
    print("  triple  :", {m: in_triple_class(G, C, m) for m in MODES})
    print("  pair  w :", {m: in_pair_class_w(G, C, m, pw) for m in MODES})
    print("  triple w:", {m: in_triple_class_w(G, C, m, tw) for m in MODES})
