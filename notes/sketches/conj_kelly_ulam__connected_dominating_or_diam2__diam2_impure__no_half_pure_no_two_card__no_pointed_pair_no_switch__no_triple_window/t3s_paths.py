"""Check of the path remark of sketch t3, section 4.5: the path p1 ... pm is in W3 at (p2, p1, w)
exactly for the pins w among p3 ... pm other than the midpoint of that sub-path.
Evidence only.   python3 t3s_paths.py
"""
import networkx as nx

from t3s_lib import *

for m in range(5, 12):
    G = nx.path_graph(m)   # p1 .. pm = 0 .. m-1
    got = w3_set(G)
    S = list(range(2, m))
    mid = [S[len(S) // 2]] if len(S) % 2 == 1 else []
    good = [w for w in S if (1, 0, w) in got]
    print(m, "pins with W3 at (p2, p1, w):", good, "prediction ok:", good == [w for w in S if w not in mid])
