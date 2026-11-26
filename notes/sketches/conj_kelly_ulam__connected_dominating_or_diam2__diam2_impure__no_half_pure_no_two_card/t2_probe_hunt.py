"""Hunt for members of the remainder (the frozen step's class) and of N+ among random
self-complementary graphs and near-regular families (evidence only).

  python3 notes/sketches/<step>/t2_probe_hunt.py [seed]
"""
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2_lib import (in_D2, pair_table, pure_degrees, half_pure_vertices, in_N, in_Nplus,  # noqa: E402
                    has_glue, canon, g6, equitable_two_degrees)
from t4_probe_selfcompl import random_sc  # noqa: E402
from t4_probe_hunt import near_regular, bidegree  # noqa: E402


def classify(G):
    if not in_D2(G):
        return None
    pi, e = pair_table(G)
    if pure_degrees(G, pi, e):
        return "pure"
    if half_pure_vertices(G):
        return "D"
    if in_N(G):
        return "N"
    if has_glue(G):
        return "glue"
    return "REM"


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 11)
    plans = [("sc", 8, (8,)), ("sc", 8, (4, 4)), ("sc", 9, (8,)), ("sc", 9, (4, 4)),
             ("sc", 12, (12,)), ("sc", 12, (8, 4)), ("sc", 12, (4, 4, 4)), ("sc", 13, (12,)),
             ("sc", 13, (4, 4, 4)), ("sc", 13, (8, 4)),
             ("nr", 9, None), ("nr", 10, None), ("nr", 11, None), ("nr", 12, None),
             ("bi", 10, None), ("bi", 12, None)]
    for kind, n, shape in plans:
        c = Counter()
        seen = set()
        hits = []
        for _ in range(500):
            if kind == "sc":
                G = random_sc(n, shape, rng)
            elif kind == "nr":
                G = near_regular(n, rng)
            else:
                G = bidegree(n, rng)
            if G is None:
                continue
            k = canon(G)
            if k in seen:
                continue
            seen.add(k)
            cl = classify(G)
            if cl is None:
                continue
            c["D2"] += 1
            c[cl] += 1
            if equitable_two_degrees(G):
                c["equitable"] += 1
            if cl == "REM":
                np_ = in_Nplus(G)
                if np_:
                    c["REM&N+"] += 1
                hits.append((g6(G), np_ or "-"))
        print(kind, n, shape, dict(c), hits[:6], flush=True)


if __name__ == "__main__":
    main()
