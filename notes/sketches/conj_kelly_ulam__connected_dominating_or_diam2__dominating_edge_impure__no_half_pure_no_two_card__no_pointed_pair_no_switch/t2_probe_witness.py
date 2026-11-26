"""Details of a C3 witness triple. Single-graph facts, evidence only.
  python3 t2_probe_witness.py <g6> u v w
"""
import sys
from collections import defaultdict
from t2_lib import *

s, u, v, w = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
G = from_g6(s)
C = Census(G)
A = [t for t, ty in C.c3.items() if ty == C.c3[(u, v, w)]]
ctypes = {C.c3[(y, x, z)] for (x, y, z) in A}
dv = G.degree(v) - int(G.has_edge(u, v))
P = [t for t, p in C.p3.items() if p == C.p3[(u, v, w)]]
Cc = [t for t in P if C.c3[t] in ctypes]
R = [t for t in P if C.c3[t] not in ctypes and G.degree(t[0]) - dv in (0, 1)]
print(s, "deg", [G.degree(x) for x in sorted(G)], "(u,v,w) =", (u, v, w), "adj uv", G.has_edge(u, v), "window", (dv, dv + 1))
print(" A =", A)
print(" triples with the pointed port:", len(P), " of them in C:", Cc)
print(" R =", R)
for (x, y, z) in A:
    S, Au, Nx, Ny, Ku, Kv = C.pd(x, y)
    st = [g for g in Au if g[z] == z]
    print(f"  member {(x, y, z)}: |Aut(G-x-y)| = {len(Au)}, pointed stabiliser {len(st)},",
          "trivial at x:", [k_trivial(G, x, y, S, Nx, g) for g in st],
          "deg-preserving:", [k_DP(G, S, g) for g in st],
          "| whole group: trivial at x", sum(k_trivial(G, x, y, S, Nx, g) for g in Au), "deg-pres", sum(k_DP(G, S, g) for g in Au))
