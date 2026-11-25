"""t5: exhaustive check of the cut identity behind Lemma G (single-graph statement; evidence only).

For a graph G, a type F (iso class of G - x - y) and a degree a, over ordered pairs (x, y), x != y,
of type F:
  P   = all type-F pairs
  E_a = adjacent pairs with deg x = a
  X   = pairs with deg x >= a
  Y   = pairs with deg y + a + e(F) >= e(G) + 1
Claims: X ∩ Y = E_a and X ∪ Y = P (so |E_a| = |X| + |Y| - |P|), and |Y| = |Y'| where
Y' = pairs with deg x + a + e(F) >= e(G) + 1 (swap).
Usage: python3 t5_check.py [max_n]   (networkx atlas, exhaustive for n <= 7)
"""
import sys
import networkx as nx
from networkx.generators.atlas import graph_atlas_g


def types(G):
    """Map each ordered pair (x, y) to a type id (iso class of G - x - y)."""
    reps, out = [], {}
    nodes = list(G.nodes)
    for x in nodes:
        for y in nodes:
            if x == y:
                continue
            F = G.subgraph([z for z in nodes if z not in (x, y)])
            key = (F.number_of_edges(), tuple(sorted(d for _, d in F.degree())))
            tid = None
            for i, (k, R) in enumerate(reps):
                if k == key and nx.is_isomorphic(F, R):
                    tid = i
                    break
            if tid is None:
                reps.append((key, F.copy()))
                tid = len(reps) - 1
            out[(x, y)] = tid
    return out, [R for _, R in reps]


def check(G):
    ty, reps = types(G)
    deg = dict(G.degree())
    eG = G.number_of_edges()
    n = G.number_of_nodes()
    checks = 0
    for t, F in enumerate(reps):
        eF = F.number_of_edges()
        P = {p for p, s in ty.items() if s == t}
        for a in range(0, n + 1):
            E = {(x, y) for (x, y) in P if deg[x] == a and G.has_edge(x, y)}
            X = {(x, y) for (x, y) in P if deg[x] >= a}
            Y = {(x, y) for (x, y) in P if deg[y] + a + eF >= eG + 1}
            Yp = {(x, y) for (x, y) in P if deg[x] + a + eF >= eG + 1}
            assert X & Y == E, (nx.to_graph6_bytes(G), t, a)
            assert X | Y == P, (nx.to_graph6_bytes(G), t, a)
            assert len(Y) == len(Yp), (nx.to_graph6_bytes(G), t, a)
            checks += 1
    return checks


def main():
    max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    total = {}
    for G in graph_atlas_g():
        n = G.number_of_nodes()
        if 3 <= n <= max_n:
            total[n] = total.get(n, [0, 0])
            total[n][0] += 1
            total[n][1] += check(G)
    for n in sorted(total):
        print(f"n={n}: {total[n][0]} graphs, {total[n][1]} (type, a) checks, NO WITNESS")


if __name__ == "__main__":
    main()
