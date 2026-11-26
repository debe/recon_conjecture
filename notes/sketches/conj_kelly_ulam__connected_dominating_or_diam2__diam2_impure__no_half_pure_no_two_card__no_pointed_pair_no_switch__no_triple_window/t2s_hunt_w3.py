"""Are nearly regular graphs in W3?  Evidence only.
For random d-regular graphs on n vertices minus a vertex / minus an edge / plus an edge: membership
in W3 with the round-12 clause (mode K, three disjuncts), with the kill of the frozen body (K2) and
with the codegree kill (CD); for graphs outside W3(K2) also the phantom count of t2s_hunt.
  python3 t2s_hunt_w3.py <n> <d> <count> [seed]
"""
import os
import random
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa
from t2s_hunt import analyse  # noqa


def classes(G):
    C = Census(G)
    tw = triple_census_w(G, C)
    out = {"census classes": len(tw)}
    for name, test in (("K", lambda Acl: all(kill_all(G, C, x, y, "K", fix=z) for (x, y, z) in Acl)),
                       ("K2", lambda Acl: all(kill_all_cd(G, C, x, y, fix=z, mode="K2") for (x, y, z) in Acl)),
                       ("CD", lambda Acl: all(kill_all_cd(G, C, x, y, fix=z, mode="CD") for (x, y, z) in Acl))):
        out[name] = next((Acl[0] for r, Acl in tw if test(Acl)), None)
    return out


def main():
    n, d, count = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    tot = Counter()
    for i in range(count):
        R = nx.random_regular_graph(d, n, seed=rng.randrange(10 ** 9))
        variants = {}
        v = rng.choice(sorted(R))
        variants["-v"] = R.subgraph([x for x in R if x != v]).copy()
        e = rng.choice(sorted(R.edges()))
        X = R.copy(); X.remove_edge(*e); variants["-e"] = X
        ne = rng.choice([(a, b) for a in R for b in R if a < b and not R.has_edge(a, b)])
        X = R.copy(); X.add_edge(*ne); variants["+e"] = X
        for tag, G in variants.items():
            G = nx.convert_node_labels_to_integers(G)
            r = classes(G)
            tot["graphs"] += 1
            for k in ("K", "K2", "CD"):
                tot["in W3 with kill " + k] += r[k] is not None
            tot["no census class"] += r["census classes"] == 0
            name = "reg(%d,%d)#%d%s %s" % (n, d, i, tag, g6(G))
            if r["K2"] is None or r["K"] is None:
                print("OUTSIDE W3:", name, r, flush=True)
                analyse("   phantoms of " + name, G)
    print("TOTAL", dict(tot))


if __name__ == "__main__":
    main()
