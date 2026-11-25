"""Red team on sketch t1 (independent re-encoding, evidence only).

R1 (K1 core, steps 1-4): for every vertex v and every S in V-v such that the graph
   (G - v) + new vertex joined to S has the same degree multiset as G with the new vertex
   having degree deg v, |N(v) & L_k| = |S & L_k| for every card-degree level L_k; and if
   (*) holds at v then S = N(v).
R2 (F1/F2/F3/F6 partition): with D = G,co-G connected and Dom(G):
   Dom(G) <=> co-G has a pair at distance >= 3 (G, co-G connected);
   Dom(G) and Dom(co-G) <=> diam G = diam co-G = 3;
   parent class P is the disjoint union of D3, D2, Q;
   triangle-free G in D => in D3 and bipartite.
R3 (S1): # dominating edges = alternating sum of M_j for connected G, n>=3.
Faithfulness: (*) encoded exactly as the Lean STAR body (x adj v, y != v, y not adj v,
deg x != deg y + 1). Dom encoded as the Lean DOM body. edist <= 2 for all pairs encoded as
connected with diameter <= 2 (u = v gives 0).
"""
import itertools
from collections import Counter
import networkx as nx


def dom(G):
    V = set(G)
    return any(V <= ({u, v} | set(G[u]) | set(G[v])) for u, v in G.edges())


def diam_le2(G):
    if not nx.is_connected(G):
        return False
    return nx.diameter(G) <= 2 if len(G) > 1 else True


def star_at(G, v):
    N = set(G[v])
    return all(G.degree(x) != G.degree(y) + 1 for x in N for y in G if y != v and y not in N)


def claim(G):
    n = len(G)
    if n < 3:
        return True
    deg = dict(G.degree())
    # R1
    for v in G:
        others = [w for w in G if w != v]
        N = set(G[v])
        c = {w: deg[w] - (1 if w in N else 0) for w in others}
        target = Counter(deg[w] for w in others)
        for S in itertools.combinations(others, deg[v]):
            S = set(S)
            if Counter(c[w] + (1 if w in S else 0) for w in others) != target:
                continue
            for k in set(c.values()):
                if sum(1 for w in N if c[w] == k) != sum(1 for w in S if c[w] == k):
                    print("R1 level fail", v, S); return False
            if star_at(G, v) and S != N:
                print("R1 star fail", v, S); return False
    # R2
    C = nx.complement(G)
    if nx.is_connected(G) and nx.is_connected(C):
        dG, dC = dom(G), dom(C)
        far_C = nx.diameter(C) >= 3
        if dG != far_C:
            print("F1 fail"); return False
        if (dG and dC) != (nx.diameter(G) == 3 and nx.diameter(C) == 3):
            print("F2 fail"); return False
        q = diam_le2(G) and diam_le2(C)
        d3 = dG and dC
        d2 = dG and diam_le2(G)
        if int(d3) + int(d2) + int(q) != (1 if (dG or q) else 0):
            print("F3 fail"); return False
        if dG and not any(True for t in nx.enumerate_all_cliques(G) if len(t) == 3):
            if not (dC and nx.is_bipartite(G)):
                print("F6 fail"); return False
    # R3
    if nx.is_connected(G):
        def miss(u, v):
            return n - len({u, v} | set(G[u]) | set(G[v]))
        from math import comb
        nd = sum(1 for u, v in G.edges() if miss(u, v) == 0)
        alt = sum((-1) ** j * sum(comb(miss(u, v), j) for u, v in G.edges()) for j in range(0, n - 2))
        if nd != alt:
            print("S1 fail"); return False
    return True
