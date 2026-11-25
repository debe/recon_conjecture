"""Algebraic identities of Zinchenko's Sections 4-5 (arXiv:2611.13728v1) on real graphs.
Evidence only.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/debe_zinchenko_model_check.py

The identities (*), Lemma 4.1, Lemma 5.1(a)(b), Lemma 5.2 and Proposition 5.3 use the
hypothetical counterexample only through
    (A_G - lambda_u I) z_u = k_u eps_u,   lambda_u = theta - [u high],
for one extension vector z_u per vertex (Lemma 3.1(c)). That relation holds for every
dbe-extension of a dbe-graph (see debe_zinchenko_claims.py), so the identities can be tested
on dbe-graphs that have a dbe-extension at every vertex. Three such graphs are the residual
members with two card types of notes/literature/options_logic_topology.md item D1: each has
exactly one dbe-extension K != G at every vertex (K is isomorphic to G; it comes from an
automorphism of the card that does not extend to G).

Checked per graph, for every choice of one extension per vertex (all choices if few):
  L4.1(a)  <z_v, z_w> = k_w z_v(w) - k_v z_w(v)               (v low, w high)
  L4.1(b)  k_v' z_v(v') = k_v z_v'(v)                           (same class)
  L5.2     v in S1(w) => k_w >= k_v + theta;  w in S0(v) => k_w <= k_v + theta
  P5.3     R0 D3 + D0 E1 = k0 (D2 + D3),  E0 D1 + D2 R1 = k1 (D2 + D3)
           (only when k is constant on L and on U and k1 - k0 = theta)
"""
import itertools
import os
import random
import sys

import networkx as nx
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
import debe_zinchenko_claims as Z  # noqa: E402
from small_graphs import all_graphs, from_g6  # noqa: E402

MEMBERS = ["GhEJ]o", "K[N_ZpBVe`q{", "OpyHvCM]IFJpsMdwu`pJp"]
COUNT = {"graphs": 0, "families": 0, "L41a": 0, "L41b": 0, "L52": 0, "P53": 0}


def check(G, max_families=64, rng=random.Random(0)):
    par = Z.dbe(G)
    if par is None:
        return True
    d, b, e, L, U = par
    theta = e - b
    nodes = sorted(G)
    ext = {u: Z.extensions(G, u, par) for u in nodes}
    if not all(ext.values()):
        return True
    COUNT["graphs"] += 1
    A = nx.to_numpy_array(G, nodelist=nodes, dtype=int)
    idx = {x: i for i, x in enumerate(nodes)}
    total = 1
    for u in nodes:
        total *= len(ext[u])
    if total <= max_families:
        fams = itertools.product(*(ext[u] for u in nodes))
    else:
        fams = (tuple(rng.choice(ext[u]) for u in nodes) for _ in range(max_families))
    Ls, Us = sorted(L), sorted(U)
    for fam in fams:
        COUNT["families"] += 1
        z = {u: np.array([fam[idx[u]][0][x] for x in nodes]) for u in nodes}
        k = {u: fam[idx[u]][1] for u in nodes}
        for v in Ls:
            for w in Us:
                COUNT["L41a"] += 1
                if z[v].dot(z[w]) != k[w] * z[v][idx[w]] - k[v] * z[w][idx[v]]:
                    return False
                if z[w][idx[v]] == -1:
                    COUNT["L52"] += 1
                    if not k[w] >= k[v] + theta:
                        return False
                if z[v][idx[w]] == 1:
                    COUNT["L52"] += 1
                    if not k[w] <= k[v] + theta:
                        return False
        for cls in (Ls, Us):
            for v, v2 in itertools.combinations(cls, 2):
                COUNT["L41b"] += 1
                if k[v2] * z[v][idx[v2]] != k[v] * z[v2][idx[v]]:
                    return False
        k0s, k1s = {k[v] for v in Ls}, {k[w] for w in Us}
        if len(k0s) == 1 and len(k1s) == 1:
            k0, k1 = k0s.pop(), k1s.pop()
            if k1 - k0 != theta:
                return False        # contradicts L5.2 since S0, S1 are non-empty
            adj = lambda x, y: int(A[idx[x]][idx[y]])   # noqa: E731
            R0 = np.array([[int(z[v][idx[c]] == -1) for c in Ls] for v in Ls])
            R1 = np.array([[int(z[w][idx[c]] == 1) for c in Us] for w in Us])
            D0 = np.array([[int(z[v][idx[w]] == 1) for w in Us] for v in Ls])
            D1 = np.array([[int(z[w][idx[v]] == -1) for w in Us] for v in Ls])
            D2 = np.array([[int(adj(v, w) and z[v][idx[w]] != 1) for w in Us] for v in Ls])
            D3 = np.array([[int(not adj(v, w) and z[w][idx[v]] != -1) for w in Us] for v in Ls])
            E0 = np.array([[int(c != v and not adj(v, c) and z[v][idx[c]] != -1) for c in Ls]
                           for v in Ls])
            E1 = np.array([[int(adj(w, c) and z[w][idx[c]] != 1) for c in Us] for w in Us])
            if not (R0 == R0.T).all() or not (R1 == R1.T).all():
                return False
            if not (D0 + D1 + D2 + D3 == 1).all():
                return False
            if not (R0.dot(D1) + D0.dot(R1) == k1 * D0 + k0 * D1).all():
                return False
            COUNT["P53"] += 1
            if not (R0.dot(D3) + D0.dot(E1) == k0 * (D2 + D3)).all():
                return False
            if not (E0.dot(D1) + D2.dot(R1) == k1 * (D2 + D3)).all():
                return False
    return True


def main():
    for s in MEMBERS:
        print(f"member {s}: {'ok' if check(from_g6(s)) else 'WITNESS'}")
    # G = F - r for vertex-transitive regular F: re-attaching v to L \\ {v} gives a graph
    # isomorphic to F - v, hence to G; this is the shape of the paper's endgame (Theorem 9.3).
    vt = {"C7": nx.cycle_graph(7), "prism": nx.circular_ladder_graph(3), "cube": nx.hypercube_graph(3),
          "K33": nx.complete_bipartite_graph(3, 3), "Petersen": nx.petersen_graph(),
          "Paley5=C5": nx.paley_graph(5).to_undirected(),
          "K2x4 (4K2 complement)": nx.complement(nx.from_edgelist([(0, 1), (2, 3), (4, 5), (6, 7)])),
          "Moebius8": nx.circulant_graph(8, [1, 4]), "C10(1,2)": nx.circulant_graph(10, [1, 2]),
          "Paley13": nx.paley_graph(13).to_undirected()}
    for name, F in vt.items():
        F = nx.convert_node_labels_to_integers(F)
        F.remove_node(0)
        G = nx.convert_node_labels_to_integers(F)
        before = COUNT["graphs"]
        ok = check(G)
        print(f"{name} minus a vertex: {'ok' if ok else 'WITNESS'}"
              f"{'' if COUNT['graphs'] > before else ' (no full extension family: skipped)'}")
    for n in range(3, 8):
        for G in all_graphs(n):
            if not check(G):
                print("WITNESS", n, sorted(G.edges()))
                return
    print("exhaustive n = 3..7: NO WITNESS;", COUNT)


if __name__ == "__main__":
    main()
