"""Hunt: Cayley graphs of dihedral groups D_k and of A_4 minus a vertex. Evidence only.

Non-abelian groups: inversion is not a group automorphism, so the pointed symmetry (a+) of
Theorem T is not automatic. Looks for remainder members outside the class of Theorem T.

  python3 .../t3_hunt_cayley.py D 5 7        # dihedral groups D_5 .. D_7 (orders 10 .. 14)
  python3 .../t3_hunt_cayley.py A4
"""
import itertools
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import *  # noqa


def dihedral(k):
    els = [(i, f) for f in (0, 1) for i in range(k)]
    mul = lambda a, b: ((a[0] + (b[0] if a[1] == 0 else -b[0])) % k, (a[1] + b[1]) % 2)
    return els, mul, (0, 0)


def a4():
    perms = [p for p in itertools.permutations(range(4))
             if sum(1 for i in range(4) for j in range(i) if p[j] > p[i]) % 2 == 0]
    mul = lambda a, b: tuple(a[b[i]] for i in range(4))
    return perms, mul, (0, 1, 2, 3)


def cayley_graphs(els, mul, e):
    inv = {a: next(b for b in els if mul(a, b) == e) for a in els}
    classes = []
    seen = set()
    for a in els:
        if a == e or a in seen:
            continue
        classes.append({a, inv[a]})
        seen |= {a, inv[a]}
    idx = {a: i for i, a in enumerate(els)}
    done = set()
    for r in range(1, len(classes)):
        for sub in itertools.combinations(classes, r):
            C = set().union(*sub)
            X = nx.empty_graph(len(els))
            for a in els:
                for c in C:
                    X.add_edge(idx[a], idx[mul(a, c)])
            k = canon(X)
            if k in done:
                continue
            done.add(k)
            yield sorted(C), X, idx[e]


def run(name, els, mul, e):
    c = Counter()
    seen = set()
    for C, X, r in cayley_graphs(els, mul, e):
        G = X.copy()
        G.remove_node(r)
        G = nx.convert_node_labels_to_integers(G)
        k = canon(G)
        if k in seen:
            continue
        seen.add(k)
        c["G"] += 1
        if not in_D2(G):
            continue
        c["D2"] += 1
        fl, ty = remainder_flags(G)
        if not fl["REM"]:
            continue
        c["remainder"] += 1
        cid = pointed_classes(G, ty)
        t = bool(T_pairs(G, ty, cid, "rigid"))
        tp = bool(Tplus_pairs(G, ty, cid))
        c["remainder in T"] += t
        c["remainder in T+"] += tp
        c["remainder in T or T+"] += (t or tp)
        if not t:
            print("   remainder member outside T:", name, g6(G), "|Aut G| =", len(auts(G)),
                  "|Aut X| =", len(auts(X)), "in T+:", tp, flush=True)
    print(name, "order", len(els), dict(c), flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "A4":
        run("A4", *a4())
    else:
        for k in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
            run("D_%d" % k, *dihedral(k))
