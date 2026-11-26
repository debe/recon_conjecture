"""Why are the three known members outside T, T+ ?  Per pair diagnostics."""
import sys
from collections import Counter, defaultdict
from t2_lib import *

for s in sys.argv[1:]:
    G = from_g6(s)
    n = G.number_of_nodes()
    A = auts(G)
    orbits = sorted({tuple(sorted({a[v] for a in A})) for v in G})
    print("==", s, "n", n, "m", G.number_of_edges(), "deg", [G.degree(v) for v in sorted(G)], "|Aut|", len(A), "orbits", orbits)
    ty = pair_types(G)
    cid = pointed_classes(G, ty)
    csize = Counter(cid.values())
    tsize = Counter(ty.values())
    print(" T pairs", T_pairs(G, ty, cid, 'rigid'), " T+ pairs", Tplus_pairs(G, ty, cid))
    members = defaultdict(list)
    for p, i in cid.items():
        members[i].append(p)
    for (u, v) in sorted(ty):
        S, Au, Nu, Nv = pair_data(G, u, v)
        alpha = int(G.has_edge(u, v))
        i = cid[(u, v)]
        a = csize[i]
        t = tsize[ty[(u, v)]]
        sym = cid[(v, u)] == i
        chat = {cid[(y, x)] for (x, y) in members[i]}
        sc = sum(len(members[j]) for j in chat if j != i)
        cond_i = G.degree(u) - G.degree(v) not in (-alpha, 1 - alpha)
        dp = all(deg_preserving(G, S, g) for g in Au)
        fo = all(factor_ok(Au, Nu, Nv, g) for g in Au)
        print(f"  ({u},{v}) adj={alpha} deg=({G.degree(u)},{G.degree(v)}) |A|={a} type={t} sym={int(sym)} |C\\A|={sc} R={t-a-(sc if not sym else 0)} (i)={int(cond_i)} |AutF|={len(Au)} degpres={int(dp)} factor={int(fo)}")
