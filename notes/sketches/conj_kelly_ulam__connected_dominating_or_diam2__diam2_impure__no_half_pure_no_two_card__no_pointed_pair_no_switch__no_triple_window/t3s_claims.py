"""Single-graph forms of two paper claims of sketch t3 (structure), for
  python3 tools/search/small_graphs.py counterexample --claim <this file> --n-min 4 --n-max 7 --random 40 --random-n 8 9
Evidence only. Neither claim presupposes a deck.

N  (normal form at a unique-copy pair with clause (i)).  Let (u, v) satisfy (i) and let G-u-v have no
   copy G-x-y with {x, y} != {u, v}.  A = Aut(G-u-v), Kv = stabiliser of N(u) minus v, Ku = stabiliser of
   N(v) minus u.  Then for every w:
     class of (u,v,w) = {(u,v,z) : z in Ku w},   #R = #(A w) - #(Kv Ku w),
     (W) <=> #(A w) - #(Kv Ku w) < #(Ku w),
     (K) <=> for every k in Ku every element of A fixing k w lies in Kv or preserves G-degrees.
X  (extension).  If phi : G-x-y -> G-u-v is an isomorphism with phi(N(x) minus y) = N(v) minus u, then
   (x, y, phi^-1 w) is in the set C of the class of (u, v, w) for every w  (so it is never in R).
"""
import os
import sys
from collections import defaultdict

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3s_lib import *  # noqa


def claim(G):
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    if n < 4:
        return True
    C = Census(G)
    cls = classes(G, C)
    by = {t: c for c in cls for t in c["A"]}
    cnt = defaultdict(int)
    for (x, y), F in C.ty.items():
        if x < y:
            cnt[F] += 1
    V = sorted(G)
    for (u, v) in C.ty:
        S, A, Nu, Nv, Ku, Kv = C.pd(u, v)   # Ku fixes Nv, Kv fixes Nu
        if cond_i(G, u, v) and cnt[C.ty[(u, v)]] == 1:
            for w in S:
                c = by[(u, v, w)]
                oK = {k[w] for k in Ku}
                if set(c["A"]) != {(u, v, z) for z in oK}:
                    return False
                oA = {g[w] for g in A}
                oKK = {kv[ku[w]] for ku in Ku for kv in Kv}
                if c["nR"] != len(oA) - len(oKK):
                    return False
                if c["W"] != (len(oA) - len(oKK) < len(oK)):
                    return False
                if c["W"]:
                    pred = all((g in Kv) or k_DP(G, S, g) for z in oK for g in A if g[z] == z)
                    if pred != c["K"]:
                        return False
        # X
        Fuv = G.subgraph(S)
        for (x, y) in C.ty:
            if C.ty[(x, y)] != C.ty[(u, v)]:
                continue
            Sx = [t for t in V if t not in (x, y)]
            Nx = set(G[x]) - {y}
            for phi in GraphMatcher(G.subgraph(Sx), Fuv).isomorphisms_iter():
                if {phi[t] for t in Nx} != set(Nv):
                    continue
                inv = {b: a for a, b in phi.items()}
                for w in S:
                    c = by[(u, v, w)]
                    chat = {C.c3[(b, a, z)] for (a, b, z) in c["A"]}
                    if C.c3[(x, y, inv[w])] not in chat:
                        return False
                break
    return True
