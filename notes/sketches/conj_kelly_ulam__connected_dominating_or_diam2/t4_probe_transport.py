"""Class T of sketch t4 (remark, not a proposed child): the transportation system.

For a degree a, unknowns x[u][F] for u of degree a and F a type on n - 2 vertices:
  0 <= x[u][F] <= c[u][F] = number of y != u with G - u - y of type F,
  for every card-degree level c:  sum over F at level c of x[u][F] = r[u][c]   (Lemma B, per vertex)
  for every F:                    sum over u of x[u][F]          = e_a(F)      (Lemma G, per class)
G is in T if for some u every solution has x[u][F] in {0, c[u][F]} equal to the true value for
every F (then the neighbourhood of u is forced). T contains (star) and the pure classes.

  python3 .../t4_probe_transport.py <graph6> [<graph6> ...]
Evidence only.
"""
import itertools
import os
import sys
from collections import defaultdict

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_lib import ctype  # noqa: E402


def solutions(rows, cols, cap, limit=20000):
    """All non-negative integer matrices with the given row sums, column sums and caps."""
    R, C = len(rows), len(cols)
    out = []
    x = [[0] * C for _ in range(R)]

    def rec(i, j, rowleft, colleft):
        if len(out) >= limit:
            return
        if i == R:
            if all(v == 0 for v in colleft):
                out.append([r[:] for r in x])
            return
        if j == C:
            if rowleft == 0:
                rec(i + 1, 0, rows[i + 1] if i + 1 < R else 0, colleft)
            return
        hi = min(cap[i][j], rowleft, colleft[j])
        for v in range(hi, -1, -1):
            x[i][j] = v
            colleft[j] -= v
            rec(i, j + 1, rowleft - v, colleft)
            colleft[j] += v
        x[i][j] = 0

    if R:
        rec(0, 0, rows[0], list(cols))
    return out


def in_T(G):
    m = G.number_of_edges()
    deg = dict(G.degree())
    for a in sorted(set(deg.values())):
        D = [u for u in sorted(G.nodes()) if deg[u] == a]
        cap = {u: defaultdict(int) for u in D}
        true = {u: defaultdict(int) for u in D}
        for u in D:
            for y in G.nodes():
                if y == u:
                    continue
                F = ctype(G, (u, y))
                cap[u][F] += 1
                true[u][F] += 1 if G.has_edge(u, y) else 0
        types = sorted({F for u in D for F in cap[u]})
        levels = defaultdict(list)
        for F in types:
            levels[m - a - len(F[1])].append(F)
        forced = {u: True for u in D}
        for c, Fs in levels.items():
            rows = [sum(true[u][F] for F in Fs) for u in D]
            cols = [sum(true[u][F] for u in D) for F in Fs]
            capm = [[cap[u][F] for F in Fs] for u in D]
            sols = solutions(rows, cols, capm)
            for i, u in enumerate(D):
                for j, F in enumerate(Fs):
                    t = true[u][F]
                    if t not in (0, cap[u][F]) or any(s[i][j] != t for s in sols):
                        forced[u] = False
        if any(forced.values()):
            return True
    return False


if __name__ == "__main__":
    for s in sys.argv[1:]:
        G = nx.from_graph6_bytes(s.encode())
        print(s, "in T:", in_T(G))
