"""Shared predicates for the falsity screen of the four children of
conj_kelly_ulam__connected_dominating_or_diam2 (evidence only).

Each child is `Recon.ClassReconstructible P`, i.e. for n >= 3, P n G -> Reconstructible G.
Reconstructible G is encoded exactly for exhaustive n: the deck class of G (over all graphs
on n vertices) contains only G's isomorphism class. P is encoded clause by clause from the
Lean bodies (see each screen_<child>.py).
"""
import itertools
import os
import sys
from collections import defaultdict, Counter

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "search"))
from small_graphs import canon, deck_key, all_graphs  # noqa: E402

_deck_classes = {}
STATS = Counter()


def reconstructible(G):
    """Exact for n <= 7 (atlas). For larger n falls back to True (conjecture verified n<=13)."""
    n = G.number_of_nodes()
    if n > 7:
        return True
    if n not in _deck_classes:
        d = defaultdict(set)
        for H in all_graphs(n):
            d[deck_key(H)].add(canon(H))
        _deck_classes[n] = d
    return len(_deck_classes[n][deck_key(G)]) == 1


def induced(G, S):
    return nx.convert_node_labels_to_integers(G.subgraph(S).copy())


def pure_at(G, u):
    """Lean: forall x y x' y', deg x = deg u -> deg x' = deg u -> x != y -> x' != y' ->
    G - {x,y} ~= G - {x',y'} -> (x ~ y <-> x' ~ y')."""
    a = G.degree(u)
    V = list(G.nodes())
    seen = {}
    for x in V:
        if G.degree(x) != a:
            continue
        for y in V:
            if y == x:
                continue
            k = canon(induced(G, [w for w in V if w not in (x, y)]))
            adj = G.has_edge(x, y)
            if seen.setdefault(k, adj) != adj:
                return False
    return True


def has_pure_class(G):
    return any(pure_at(G, u) for u in G.nodes())


def automorphisms(F):
    nodes = list(F.nodes())
    E = {frozenset(e) for e in F.edges()}
    for p in itertools.permutations(nodes):
        m = dict(zip(nodes, p))
        if all((frozenset((m[a], m[b])) in E) == (frozenset((a, b)) in E)
               for a, b in itertools.combinations(nodes, 2)):
            yield m


def unique_copy_factorizing(G, u, v):
    """Lean: u != v; every Finset T with G[{u,v}^c] ~= G[T] has T = {u,v}^c; and
    forall g in Aut(F) exists h in Aut(F) with v-adjacency preserved by h and
    u-adjacency preserved by g o h (x -> g (h x))."""
    V = list(G.nodes())
    rest = [w for w in V if w not in (u, v)]
    F = G.subgraph(rest).copy()
    cF = canon(nx.convert_node_labels_to_integers(F))
    # only T of size n-2 can be isomorphic to F
    for T in itertools.combinations(V, len(rest)):
        if set(T) == set(rest):
            continue
        if canon(induced(G, T)) == cF:
            return False
    auts = list(automorphisms(F))
    Nu = set(G[u])
    Nv = set(G[v])
    stab_v = [h for h in auts if all((h[x] in Nv) == (x in Nv) for x in rest)]
    for g in auts:
        if not any(all((g[h[x]] in Nu) == (x in Nu) for x in rest) for h in stab_v):
            return False
    return True


def has_unique_copy_pair(G):
    return any(unique_copy_factorizing(G, u, v)
               for u in G.nodes() for v in G.nodes() if u != v)


def dominating_edge(G):
    V = set(G.nodes())
    return any(all(x in (u, v) or G.has_edge(x, u) or G.has_edge(x, v) for x in V)
               for u, v in G.edges())


def diam2_both(G):
    """Lean: forall u v, G.edist u v <= 2 and Gc.edist u v <= 2 (edist = top if unreachable)."""
    C = nx.complement(G)
    for H in (G, C):
        if not nx.is_connected(H):
            return False
        if len(H) > 1 and nx.diameter(H) > 2:
            return False
    return True


def report():
    print("class membership counts (by n):", dict(sorted(STATS.items())))
