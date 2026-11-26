"""Triple statistics of the residual members: copies of F3, clause (b), Helly."""
import sys
from collections import Counter
from t3o_lib import *

for s in sys.argv[1:]:
    G = from_g6(s)
    ty3 = triple_types(G)
    ty2 = pair_types_u(G)
    cnt = Counter(ty3.values())
    cnt2 = Counter(ty2.values())
    print("==", s, "triples", len(ty3), "copies histogram", sorted(Counter(cnt.values()).items()),
          "| pairs", len(ty2), "copies histogram", sorted(Counter(cnt2.values()).items()))
    uniq = [t for t, F in ty3.items() if cnt[F] == 1]
    nb = 0
    rows = []
    for t in uniq:
        u, v, w = t
        b = len({ty2[(u, v)], ty2[(u, w)], ty2[(v, w)]}) == 3
        S, A, Nu, Nv, Nw = triple_data(G, u, v, w)
        hel = [helly(G, *o) for o in ((u, v, w), (v, u, w), (w, u, v))]
        tri = triangles(A, Nu, Nv, Nw)
        triv = trivial_images(A, Nu, Nv, Nw)
        rows.append((t, len(A), b, hel, len(tri), len(triv)))
    print("   unique-copy triples:", len(uniq), " with (b):", sum(r[2] for r in rows),
          " with (b) and Helly:", sum(1 for r in rows if r[2] and r[3][0]))
    print("   Helly symmetric in the choice of u:", all(len(set(r[3])) == 1 for r in rows))
    print("   |Aut F3| histogram over unique triples:", sorted(Counter(r[1] for r in rows).items()))
    good = [r[0] for r in rows if r[2] and r[3][0]]
    print("   T3 triples (first 12):", good[:12])
    bad = [r for r in rows if r[2] and not r[3][0]]
    print("   (b) but not Helly (first 5):", bad[:5])
