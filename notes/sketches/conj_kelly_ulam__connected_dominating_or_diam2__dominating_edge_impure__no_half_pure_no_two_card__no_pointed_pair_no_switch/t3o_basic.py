"""Basic data of the known residual members (evidence only)."""
import sys
from collections import Counter
from t3o_lib import *

for s in sys.argv[1:]:
    G = from_g6(s)
    n = G.number_of_nodes()
    orb, na = vertex_orbits(G)
    print("==", s, "n", n, "m", G.number_of_edges(), "degs", sorted(d for _, d in G.degree()),
          "|Aut|", na, "orbits", orb)
    print("   adjacency:", {v: sorted(G[v]) for v in G})
    ct = {v: ctype(G, (v,)) for v in G}
    ids = {}
    print("   card types:", [ids.setdefault(ct[v], len(ids)) for v in sorted(G)],
          "|Aut(card)|:", [len(auts(G, [w for w in G if w != v])) for v in sorted(G)])
    X = regular_completion(G)
    print("   regular completion:", None if X is None else (g6(X), "VT" if is_vt(X) else "not VT"))
    for k in (2, 3):
        cid = pointed_classes(G, k)
        sizes = Counter(cid.values())
        print("   k =", k, "tuples", len(cid), "types", len(sizes), "size histogram",
              sorted(Counter(sizes.values()).items()))
