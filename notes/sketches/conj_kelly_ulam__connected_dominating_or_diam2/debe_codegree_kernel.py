"""Is the adjacency split by refined key forced by the linear data? (sketch debe_codegree, section 5)

Evidence about the METHOD only (never about reconstructibility).  For a graph G and a type F
the data that every hypomorphic H shares are: the refined table pi_k(F), k = (deg, t, tbar),
and the constants s = e(G) - e(F), c = t(G) - t(F), cbar = tbar(G) - tbar(F).  The pair laws
restrict the key pairs (k, k') of a type-F pair:
   adjacent:      a + a' = s + 1, tbar + tbar' = cbar, t + t' >= c
   non-adjacent:  a + a' = s,     t + t' = c,          tbar + tbar' >= cbar
An abstract table is a pair of symmetric non-negative arrays J1, J0 on admissible key pairs
with the row sums pi_k(F) and the caps J(k, k') <= m_k m_k', J(k, k) <= C(m_k, 2), where m_k
is the number of vertices with key k.  This script asks, by linear programming over the reals, whether
eps_k(F) (adjacent pairs with first key k) takes the same value in every abstract table.

  python3 .../debe_codegree_kernel.py [n_max]
  python3 .../debe_codegree_kernel.py g6 <graph6> ...   (also the integer range, by MILP)
prints, per n: number of (G, F, k) triples; how many have eps_k not forced; how many of those
are refined-pure in G (eps in {0, pi}); and the first few witnesses.
"""
import itertools
import os
import sys
from collections import Counter, defaultdict

import networkx as nx
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import all_graphs  # noqa: E402
from debe_codegree_lib import keys, pair_types, ref_table, tri, cotri, cond_R  # noqa: E402


def tot(G, f):
    return sum(f(G, x) for x in G.nodes()) // 3


def analyse(G, integer=False):
    key = keys(G)
    ty = pair_types(G)
    pi, e = ref_table(G, key, ty)
    eG, tG, tbG = G.number_of_edges(), tot(G, tri), tot(G, cotri)
    reps = {}
    for (x, y), F in ty.items():
        reps.setdefault(F, (x, y))
    out = []
    for F, (x, y) in reps.items():
        Fg = G.subgraph([w for w in G.nodes() if w not in (x, y)])
        s, c, cb = eG - Fg.number_of_edges(), tG - tot(Fg, tri), tbG - tot(Fg, cotri)
        occ = sorted(k for (F2, k) in pi if F2 == F)
        var = []
        for i, k in enumerate(occ):
            for k2 in occ[i:]:
                if k[0] + k2[0] == s + 1 and k[2] + k2[2] == cb and k[1] + k2[1] >= c:
                    var.append((1, k, k2))
                if k[0] + k2[0] == s and k[1] + k2[1] == c and k[2] + k2[2] >= cb:
                    var.append((0, k, k2))
        mult = Counter(key.values())
        caps = [(0, mult[k] * mult[k2] if k != k2 else mult[k] * (mult[k] - 1) // 2)
                for (_, k, k2) in var]
        A = np.zeros((len(occ), len(var)))
        for j, (b, k, k2) in enumerate(var):
            A[occ.index(k), j] += 1
            A[occ.index(k2), j] += 1
        rhs = np.array([pi[(F, k)] for k in occ], dtype=float)
        for k in occ:
            obj = np.zeros(len(var))
            for j, (b, k1, k2) in enumerate(var):
                if b == 1:
                    obj[j] = (k1 == k) + (k2 == k)
            lo = linprog(obj, A_eq=A, b_eq=rhs, bounds=caps, method="highs")
            hi = linprog(-obj, A_eq=A, b_eq=rhs, bounds=caps, method="highs")
            if lo.status != 0 or hi.status != 0:
                out.append((F, k, None, None, e[(F, k)], pi[(F, k)]))
                continue
            l, h = round(lo.fun, 6), round(-hi.fun, 6)
            if integer and h - l > 1e-6:
                con = LinearConstraint(A, rhs, rhs)
                bd = Bounds([0] * len(var), [c2 for (_, c2) in caps])
                ones = np.ones(len(var))
                li = milp(obj, constraints=con, integrality=ones, bounds=bd)
                hi_ = milp(-obj, constraints=con, integrality=ones, bounds=bd)
                l, h = round(li.fun), round(-hi_.fun)
            out.append((F, k, l, h, e[(F, k)], pi[(F, k)]))
    return out, cond_R(key)


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "g6":
        for g6 in sys.argv[2:]:
            G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
            res, R = analyse(G, integer=True)
            bad = [(k, lo, hi, ev, pv) for (F, k, lo, hi, ev, pv) in res if lo is not None and hi > lo]
            print(g6, "(R):", R, "classes (F, k):", len(res),
                  "not forced over the integers (key, min, max, eps, pi):", bad, flush=True)
        return
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    for n in range(4, n_max + 1):
        cnt = Counter()
        wit = []
        for G in all_graphs(n):
            res, R = analyse(G)
            for (F, k, lo, hi, ev, pv) in res:
                cnt["triples"] += 1
                if lo is None:
                    cnt["infeasible(BUG)"] += 1
                    continue
                if not (lo - 1e-6 <= ev <= hi + 1e-6):
                    cnt["truth outside range(BUG)"] += 1
                if hi - lo > 1e-6:
                    cnt["not forced"] += 1
                    if R:
                        cnt["not forced although (R)"] += 1
                    if ev in (0, pv):
                        cnt["not forced, pure"] += 1
                        if len(wit) < 3:
                            wit.append((nx.to_graph6_bytes(G, header=False).decode().strip(), k, lo, hi, ev, pv))
        print(n, dict(cnt), flush=True)
        for w in wit:
            print("   witness (g6, key, lp-min, lp-max, eps, pi):", w, flush=True)


if __name__ == "__main__":
    main()
