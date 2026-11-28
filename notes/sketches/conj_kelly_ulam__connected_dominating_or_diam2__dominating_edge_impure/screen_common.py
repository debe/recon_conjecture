"""Shared exact encoding of the parent residual predicate and the child splits.

Parent predicate (Lean, verbatim body):
  Connected G, Connected G^c, exists dominating edge (u adj v, every x is u, v or adjacent
  to u or v), NOT PureClass, NOT UniqueCopyPair.
PureClass: exists u such that for all x y x' y' with deg x = deg x' = deg u, x != y,
  x' != y', G-{x,y} iso G-{x',y'} => (x adj y <-> x' adj y').  (y, y' of any degree.)
UniqueCopyPair: exists u != v such that every T with G[T] iso G-{u,v} equals V-{u,v}
  (iso forces |T| = n-2, so: G-{u,v} has exactly one induced copy among (n-2)-subsets),
  and for every g in Aut(G-{u,v}) there is h in Aut(G-{u,v}) with h preserving N(v)
  (restricted) and g.h preserving N(u) (restricted).
Children: TF = exists dominating edge uv with no common neighbour; the second child is
  parent AND NOT TF. Hypomorphism is supplied by the tool (same deck_key), and
  Reconstructible G means: every hypomorphic H is isomorphic to G.
"""
import itertools
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher


def dom_edges(G):
    V = set(G)
    return [(u, v) for u, v in G.edges() if V <= ({u, v} | set(G[u]) | set(G[v]))]


def sub(G, S):
    return G.subgraph(S).copy()


def iso(A, B):
    return A.number_of_edges() == B.number_of_edges() and nx.is_isomorphic(A, B)


def pure_class(G):
    n = len(G); deg = dict(G.degree())
    pairs = [(x, y) for x in G for y in G if x != y]
    cards = {(x, y): sub(G, [w for w in G if w not in (x, y)]) for (x, y) in pairs}
    for d in set(deg.values()):
        P = [(x, y) for (x, y) in pairs if deg[x] == d]
        ok = True
        for (x, y), (a, b) in itertools.combinations(P, 2):
            if G.has_edge(x, y) != G.has_edge(a, b) and iso(cards[(x, y)], cards[(a, b)]):
                ok = False; break
        if ok:
            return True
    return False


def automorphisms(H):
    return [m for m in GraphMatcher(H, H).isomorphisms_iter()]


def unique_copy_pair(G):
    n = len(G)
    for u, v in itertools.permutations(G, 2):
        R = [w for w in G if w not in (u, v)]
        C = sub(G, R)
        unique = all(set(T) == set(R) or not iso(C, sub(G, T))
                     for T in itertools.combinations(G, n - 2))
        if not unique:
            continue
        auts = automorphisms(C)
        Nu = {w for w in R if G.has_edge(u, w)}
        Nv = {w for w in R if G.has_edge(v, w)}
        Sv = [h for h in auts if all((h[x] in Nv) == (x in Nv) for x in R)]
        if all(any(all((g[h[x]] in Nu) == (x in Nu) for x in R) for h in Sv) for g in auts):
            return True
    return False


def parent(G):
    if len(G) < 3:
        return False
    if not nx.is_connected(G) or not nx.is_connected(nx.complement(G)):
        return False
    if not dom_edges(G):
        return False
    return not pure_class(G) and not unique_copy_pair(G)


def tf(G):
    return any(not (set(G[u]) & set(G[v])) for u, v in dom_edges(G))
