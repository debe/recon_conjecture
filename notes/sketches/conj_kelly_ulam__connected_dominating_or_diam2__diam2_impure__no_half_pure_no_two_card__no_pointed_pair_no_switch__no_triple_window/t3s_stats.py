"""Which structure statements survive on small non-regular graphs (sketch t3, section 7). Evidence only.
  python3 t3s_stats.py 7
For every non-regular graph on n vertices:
  ANCH   some class with clause (i) and the window census (W)
  W3     the checked class
  TRIV   some class with (W) at which every pinned twist fixes N(x)   (first disjunct of (K) only)
  RIGID  some class with (W) at which every pinned stabiliser is trivial
  UC     some class with (W) and (K) at a pair with clause (i) whose two-deleted subgraph has a unique copy
"""
import sys
from collections import Counter, defaultdict

import networkx as nx
from networkx.generators.atlas import graph_atlas_g

from t3s_lib import *

n = int(sys.argv[1])
c = Counter()
out = defaultdict(list)
for G in graph_atlas_g():
    if G.number_of_nodes() != n:
        continue
    if len(set(d for _, d in G.degree())) == 1:
        c["regular"] += 1
        continue
    c["nonregular"] += 1
    C = Census(G)
    cls = classes(G, C)
    cnt = Counter(F for (x, y), F in C.ty.items() if x < y)
    f = Counter()
    for k in cls:
        if not k["W"]:
            continue
        f["W"] = 1
        if k["i"]:
            f["ANCH"] = 1
        if k["K"]:
            f["W3"] = 1
            u, v, w = k["rep"]
            if k["i"] and cnt[C.ty[(u, v)]] == 1:
                f["UC"] = 1
        st = [kill_exact(G, C, x, y, z) for (x, y, z) in k["A"]]
        if all(s[1] == 1 for s in st):
            f["RIGID"] = 1
        S_ok = True
        for (x, y, z) in k["A"]:
            S, A, Nu, Nv, Ku, Kv = C.pd(x, y)
            if not all(k_trivial(G, x, y, S, Nu, g) for g in A if g[z] == z):
                S_ok = False
                break
        if S_ok:
            f["TRIV"] = 1
    for key in ("W", "ANCH", "W3", "TRIV", "RIGID", "UC"):
        c[key] += f[key]
        if not f[key]:
            out[key].append(g6(G))
print("n =", n, dict(c))
for key, L in out.items():
    print("  not", key, len(L), L[:12])
