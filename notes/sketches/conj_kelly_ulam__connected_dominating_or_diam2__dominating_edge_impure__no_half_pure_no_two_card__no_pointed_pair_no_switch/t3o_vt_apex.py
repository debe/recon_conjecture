"""Apex triple census (clauses (a1), (a2), (b) of class T3) and pair census on vertex-transitive
graphs minus a vertex. Evidence only. Expected from the sketch: the apex census is tied (the
pointed two-deleted class of (u, v; w) holds three 2-pointed types), the pair census is not."""
import sys
import time
from collections import Counter, defaultdict

from t3o_lib import *
from t3o_tied import pair_census  # noqa: F401  (runs nothing at import: guarded below)

for s in sys.argv[1:]:
    t0 = time.time()
    G = from_g6(s)
    cid2 = pointed_classes(G, 2)
    t_ok, tp_ok = pair_census(G, cid2)
    cid3 = pointed_classes(G, 3)
    p2 = {t: pointed2del_key(G, *t) for t in cid3}
    by_p2 = defaultdict(set)
    for t, key in p2.items():
        by_p2[key].add(cid3[t])
    hist = Counter(len(v) for v in by_p2.values())
    apex = T3_apex(G, cid3, "none")
    print(s, "n", G.number_of_nodes(), "pair census T:", t_ok, "T+:", tp_ok,
          "| 2-pointed types per pointed two-deleted class:", sorted(hist.items()),
          "| apex-census triples:", len(apex), "| %.0fs" % (time.time() - t0), flush=True)
