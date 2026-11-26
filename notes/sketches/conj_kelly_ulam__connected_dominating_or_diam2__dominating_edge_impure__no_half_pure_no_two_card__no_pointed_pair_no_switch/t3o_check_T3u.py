"""Theorem T3u in three-card form, exhaustive for n <= N. Evidence only (no deck is assumed,
so the test is not vacuous for n <= 13).

For every graph G, every triple K = {u, v, w} with
  (a) G - K has a unique copy among the 3-subsets,
  (b) G - u - v, G - u - w, G - v - w pairwise non-isomorphic,
  (c) Helly (mode 'helly') -- or nothing (mode 'nohelly', to see that (c) does work),
and every graph H on n vertices such that
  (1) H has exactly one 3-subset K_H with H - K_H isomorphic to G - K,
  (2) there is a bijection s : K -> K_H with H - s(x) isomorphic to G - x for x in K,
CLAIM: H is isomorphic to G.
"""
import itertools
import sys
from collections import Counter, defaultdict

from t3o_lib import *
from small_graphs import all_graphs

N = int(sys.argv[1])
mode = sys.argv[2] if len(sys.argv) > 2 else "helly"
for n in range(4, N + 1):
    graphs = [nx.convert_node_labels_to_integers(G) for G in all_graphs(n)]
    info = []
    by_m = defaultdict(list)
    for i, H in enumerate(graphs):
        cards = {v: ctype(H, (v,)) for v in H}
        trip = {t: ctype(H, t) for t in itertools.combinations(sorted(H), 3)}
        info.append((canon(H), cards, trip, Counter(trip.values())))
        by_m[H.number_of_edges()].append(i)
    checks = bad = 0
    for i, G in enumerate(graphs):
        cG, cardsG, tripG, cntG = info[i]
        ty2 = pair_types_u(G)
        for t, F in tripG.items():
            if cntG[F] != 1:
                continue
            u, v, w = t
            if len({ty2[(u, v)], ty2[(u, w)], ty2[(v, w)]}) != 3:
                continue
            if mode == "helly" and not helly(G, u, v, w):
                continue
            need = sorted(cardsG[x] for x in t)
            for j in by_m[G.number_of_edges()]:
                cH, cardsH, tripH, cntH = info[j]
                if cntH.get(F, 0) != 1:
                    continue
                KH = next(s for s, FF in tripH.items() if FF == F)
                if sorted(cardsH[x] for x in KH) != need:
                    continue
                checks += 1
                if cH != cG:
                    bad += 1
                    if bad <= 3:
                        print("   WITNESS", g6(G), t, g6(graphs[j]), KH)
    print("n =", n, "mode", mode, "checks", checks, "non-isomorphic H passing:", bad, flush=True)
