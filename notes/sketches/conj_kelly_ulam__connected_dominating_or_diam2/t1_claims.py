"""Intermediate claims of sketch t1 (dominating-edge branch). Evidence only.

Run:
  python3 tools/search/small_graphs.py counterexample \
      --claim notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t1_claims.py \
      --n-min 3 --n-max 7 --random 1500 --random-n 8 9 10

Every claim here is a statement about ONE graph (structure or degree combinatorics).
Reconstructibility itself is not tested: it holds for n <= 13 (McKay), so such a test
would say nothing.

T1  class D (G, co-G connected, G has a dominating edge)  ==  G, co-G connected and some
    pair is at distance >= 3 in co-G.
T2  G and co-G both have a dominating edge  <=>  G, co-G connected, diam G = diam co-G = 3.
T3  parent class P splits disjointly into
      D3 = both have a dominating edge,
      D2 = co-G connected, G has a dominating edge, diam G <= 2,
      Q  = both diameters <= 2.
T4  level-count lemma: for every vertex v and every S in V - v with |S| = deg v such that
    (G - v) + (new vertex joined to S) has the degree multiset of G, S meets every
    card-degree level in as many vertices as N(v) does.  Under (*) at v, S = N(v).
T5  G in D and triangle-free  =>  G bipartite with sides N(u), N(v), and co-G has a
    dominating edge.
T6  in D3, a dominating edge uv of G and a dominating edge xy of co-G form an induced
    path x-u-v-y or y-u-v-x of G.
T7  one-card analysis of the triangle-free case: with X = N(v), Y = N(u), Y0 = degree-1
    vertices of Y, every independent S of G - u with the level profile of Y is Y or
    (X - u) + Y0, the latter only if |Y - Y0| = |X| - 1.
T8  a cut vertex of a graph with dominating edge uv is u or v.
T9  for connected G: (number of dominating edges) = sum_{j=0}^{n-3} (-1)^j M_j, where
    M_j = sum over (j+2)-subsets W of the number of K2-components of G[W]  (each M_j is a
    Kelly count on fewer than n vertices).
"""
import itertools
from collections import Counter

import networkx as nx

LAST_FAIL = None


def _fail(tag):
    global LAST_FAIL
    LAST_FAIL = tag
    print("FAILED sub-claim", tag)
    return False


def dom_edges(G):
    nodes = set(G.nodes())
    return [(u, v) for u, v in G.edges() if nodes <= ({u, v} | set(G[u]) | set(G[v]))]


def dist(G):
    return dict(nx.all_pairs_shortest_path_length(G))


def diam_le(G, k):
    d = dist(G)
    n = G.number_of_nodes()
    return all(len(d[u]) == n and max(d[u].values()) <= k for u in G.nodes())


def far_pair(G, k=3):
    """some pair at distance >= k (unreachable counts)"""
    d = dist(G)
    return any(d[u].get(v, 10 ** 9) >= k for u in G.nodes() for v in G.nodes())


def star_at(G, v):
    """(*) at v: no neighbour x and non-neighbour y != v with deg x = deg y + 1"""
    N = set(G[v])
    return all(G.degree(x) != G.degree(y) + 1
               for x in N for y in G.nodes() if y != v and y not in N)


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    Gc = nx.complement(G)
    conn, cconn = nx.is_connected(G), nx.is_connected(Gc)
    de, dec = dom_edges(G), dom_edges(Gc)

    # T1
    inD = conn and cconn and bool(de)
    if inD != (conn and cconn and far_pair(Gc, 3)):
        return _fail("T1")

    # T2
    both = bool(de) and bool(dec)
    d3 = conn and cconn and nx.diameter(G) == 3 and nx.diameter(Gc) == 3
    if both != bool(d3):
        return _fail("T2")

    # T3
    inQ = conn and cconn and diam_le(G, 2) and diam_le(Gc, 2)
    inP = conn and cconn and (bool(de) or inQ)
    D3 = both
    D2 = cconn and bool(de) and diam_le(G, 2)
    if inP != (D3 or D2 or inQ) or (D3 + D2 + inQ) > 1:
        return _fail("T3")

    # T4
    degs = Counter(dict(G.degree()).values())
    for v in G.nodes():
        N = set(G[v])
        others = [w for w in G.nodes() if w != v]
        c = {w: G.degree(w) - (1 if w in N else 0) for w in others}
        target = degs.copy()
        target[G.degree(v)] -= 1
        prof_N = Counter(c[w] for w in N)
        for S in itertools.combinations(others, len(N)):
            Ss = set(S)
            got = Counter(c[w] + (1 if w in Ss else 0) for w in others)
            if +got != +target:
                continue
            if Counter(c[w] for w in Ss) != prof_N:
                return _fail("T4 level counts")
            if star_at(G, v) and Ss != N:
                return _fail("T4 star")

    # T5
    tri_free = sum(nx.triangles(G).values()) == 0
    if inD and tri_free:
        if not nx.is_bipartite(G) or not dec:
            return _fail("T5")
        for u, v in de:
            if set(G[u]) & set(G[v]) or (set(G[u]) | set(G[v])) != set(G.nodes()):
                return _fail("T5 sides")

    # T6
    if both:
        for u, v in de:
            for x, y in dec:
                ok = False
                for a, b in ((x, y), (y, x)):
                    if (len({a, b, u, v}) == 4 and G.has_edge(a, u) and G.has_edge(b, v)
                            and not G.has_edge(a, v) and not G.has_edge(b, u)
                            and not G.has_edge(a, b)):
                        ok = True
                if not ok:
                    return _fail("T6")

    # T7
    if conn and tri_free and de:
        for (p, q) in de:
            for u, v in ((p, q), (q, p)):
                X, Y = set(G[v]), set(G[u])
                Y0 = {y for y in Y if G.degree(y) == 1}
                others = [w for w in G.nodes() if w != u]
                c = {w: G.degree(w) - (1 if w in Y else 0) for w in others}
                prof = Counter(c[w] for w in Y)
                for S in itertools.combinations(others, len(Y)):
                    Ss = set(S)
                    if any(G.has_edge(a, b) for a, b in itertools.combinations(S, 2)):
                        continue
                    if Counter(c[w] for w in Ss) != prof:
                        continue
                    if Ss == Y:
                        continue
                    if Ss == (X - {u}) | Y0 and len(Y - Y0) == len(X) - 1:
                        continue
                    return _fail("T7")

    # T8
    if de:
        cuts = set(nx.articulation_points(G))
        for u, v in de:
            if not cuts <= {u, v}:
                return _fail("T8")

    # T9
    if conn:
        total = 0
        for j in range(0, n - 2):
            Mj = 0
            for W in itertools.combinations(G.nodes(), j + 2):
                Hs = G.subgraph(W)
                Mj += sum(1 for comp in nx.connected_components(Hs) if len(comp) == 2)
            total += (-1) ** j * Mj
        if total != len(de):
            return _fail("T9")
    return True
