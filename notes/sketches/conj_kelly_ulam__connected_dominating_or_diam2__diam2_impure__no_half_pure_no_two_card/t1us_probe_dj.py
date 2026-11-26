"""Two-deleted spectral description of the switch (Proposition DJ of sketch t1). Evidence only.

  python3 .../t1us_probe_dj.py

For every named two-walk-linear graph G and vertex u with A_G - lam_u nonsingular
(lam_u = a - deg u): r = (A_G - lam_u)^{-1} e_u.  Checks
  (i)   the unique candidate switch z (if any) is r / max|r|, and it exists iff r(u) = 0 and r
        is a multiple of an admissible sign vector;
  (ii)  phi(G - u; lam_u) = 0 whenever a switch exists;
  (iii) support(z) = {x : phi(G - u - x; lam_u) != 0}, and on the support
        phi(G - u - x; lam_u) = - phi(G; lam_u) / k^2   (k = number of lost neighbours).
"""
import os
import sys

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1us_lib import named, two_walk_linear, switch_vectors  # noqa: E402


def charval(G, drop, lam):
    keep = [x for x in sorted(G.nodes()) if x not in drop]
    M = sp.Matrix(len(keep), len(keep), lambda i, j: 1 if G.has_edge(keep[i], keep[j]) else 0)
    return (lam * sp.eye(len(keep)) - M).det()


def main():
    for name, G in named():
        ab = two_walk_linear(G)
        if ab is None:
            continue
        a = sp.Rational(ab[0].numerator, ab[0].denominator)
        nodes = sorted(G.nodes())
        n = len(nodes)
        A = sp.Matrix(n, n, lambda i, j: 1 if G.has_edge(nodes[i], nodes[j]) else 0)
        ok = True
        ks = set()
        for u in nodes[:4] + nodes[-2:]:
            lam = a - G.degree(u)
            M = A - lam * sp.eye(n)
            if M.det() == 0:
                print(name, "u=%d singular" % u)
                continue
            e = sp.zeros(n, 1)
            e[u] = 1
            r = M.LUsolve(e)
            zs = switch_vectors(G, u, ab[0])
            if len(zs) > 1:
                ok = False
            phiG = charval(G, (), lam)
            if zs:
                z = zs[0]
                k = sum(1 for x in z if z[x] == 1)
                ks.add(k)
                if any(r[x] * k != z[x] for x in z) or r[u] != 0:
                    ok = False
                if charval(G, (u,), lam) != 0:
                    ok = False
                for x in z:
                    val = charval(G, (u, x), lam)
                    if (val != 0) != (z[x] != 0):
                        ok = False
                    if z[x] != 0 and val * k * k != -phiG:
                        ok = False
            else:
                mx = max(abs(t) for t in r)
                cand = [t / mx for t in r]
                if r[u] == 0 and all(t in (-1, 0, 1) for t in cand) and sum(cand) == 0:
                    N = set(G[u])
                    if all((t != 1 or x in N) and (t != -1 or x not in N) for x, t in zip(nodes, cand)):
                        ok = False  # an admissible r that switch_vectors missed
        print(name, "n=%d" % n, "DJ description holds at sampled vertices:", ok, "k values:", sorted(ks), flush=True)


if __name__ == "__main__":
    main()
