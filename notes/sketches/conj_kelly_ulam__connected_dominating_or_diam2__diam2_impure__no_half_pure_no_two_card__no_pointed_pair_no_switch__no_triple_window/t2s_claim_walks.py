"""Total walk counts of a twist (single-graph identities), for
  python3 tools/search/small_graphs.py counterexample --claim <this file> --n-min 3 --n-max 6 --random 30 --random-n 7 8
Evidence only.

Notation of t2s_claim_transfer.py.  W_k(X) = number of walks of length k in X (= 1^T A_X^k 1).
  WK1  W_3(G_g) - W_3(G) = 2 Delta_1 + 2 (deg u + deg v) Delta_0
  WK2  triangular law: if Delta_i = 0 for all i < j, then W_k(G_g) = W_k(G) for all k < j + 2 and
       W_{j+2}(G_g) - W_{j+2}(G) = 2 Delta_j
  WK3  hence: W_k(G_g) = W_k(G) for all k <= 2n   <=>   Delta_j = 0 for all j
       (<=> same characteristic polynomial, by TR3)
"""
import os
import sys

import networkx as nx
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa
from t2s_claim_transfer import deltas  # noqa


def walks(G, kmax):
    V = sorted(G)
    M = np.array([[1 if G.has_edge(a, b) else 0 for b in V] for a in V], dtype=object)
    vec = np.array([1] * len(V), dtype=object)
    out = []
    for _ in range(kmax + 1):
        out.append(int(sum(vec)))
        vec = M.dot(vec)
    return out


def claim(G):
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    if n < 4:
        return True
    C = Census(G, triples=False)
    kmax = 2 * n
    wG = walks(G, kmax)
    for (u, v) in C.ty:
        S, A, Nu, Nv, Ku, Kv = C.pd(u, v)
        seen = set()
        for g in A:
            Np = frozenset(x for x in S if g[x] in Nu)
            if Np in seen:
                continue
            seen.add(Np)
            D = deltas(G, S, Nu, Nv, g)
            H = twist_graph(G, u, v, S, Nu, g)
            wH = walks(H, kmax)
            if wH[3] - wG[3] != 2 * D[1] + 2 * (G.degree(u) + G.degree(v)) * D[0]:
                return False
            j = next((i for i, d in enumerate(D) if d != 0), None)
            if j is None:
                if wH != wG:
                    return False
            else:
                if wH[:j + 2] != wG[:j + 2] or wH[j + 2] - wG[j + 2] != 2 * D[j]:
                    return False
    return True
