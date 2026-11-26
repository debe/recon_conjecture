"""Class T3 on given graphs: number of apex triples with census clauses only / with Helly /
with 'every triangle twist isomorphic to G'."""
import sys
from t3o_lib import *

for s in sys.argv[1:]:
    G = from_g6(s)
    cid3 = pointed_classes(G, 3)
    c = T3_apex(G, cid3, "none")
    h = T3_apex(G, cid3, "helly")
    i = T3_apex(G, cid3, "iso")
    print(s, "census-anchored apex triples:", len(c), " + Helly:", len(h), " + iso:", len(i),
          " examples:", h[:6])
