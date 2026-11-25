"""Two-deleted gluing lemma, strong form (non-vacuous: uses two cards, one count, one degree).

Let u != v in G, S = V - {u, v}, F = G[S], and suppose every automorphism of F maps N(u) & S to
itself. Let H' be any graph on n vertices with vertices a != b such that
  H' - a is isomorphic to G - u,   H' - b is isomorphic to G - v,
  deg_{H'}(a) = deg_G(u),   and H' has exactly one (n-2)-subset inducing a copy of F.
Then H' is isomorphic to G.

The paper proof of child `unique_two_deleted` uses exactly these four facts about H (the last
one comes from Kelly's induced count), so this tests the gluing argument without presupposing
the conjecture. H' ranges over all one-vertex extensions of G - u.
"""
import itertools, os, sys
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'search'))
from small_graphs import canon


def claim(G):
    n = G.number_of_nodes()
    if n < 4 or n > 9:
        return True
    nodes = list(G.nodes())
    for u in nodes:
        Cu = G.copy(); Cu.remove_node(u)
        for v in nodes:
            if v == u:
                continue
            F = Cu.copy(); F.remove_node(v)
            Nu = set(G[u]) - {v}
            if not all({a[x] for x in Nu} == Nu for a in GraphMatcher(F, F).isomorphisms_iter()):
                continue
            cF = canon(F)
            Cv = G.copy(); Cv.remove_node(v)
            cCv = canon(Cv)
            for S in itertools.combinations(list(Cu.nodes()), G.degree(u)):
                H = Cu.copy(); H.add_node(u); H.add_edges_from((u, s) for s in S)
                # a = u (the new vertex); need some b != a with H - b iso G - v
                ok_b = False
                for b in Cu.nodes():
                    K = H.copy(); K.remove_node(b)
                    if canon(K) == cCv:
                        ok_b = True
                        break
                if not ok_b:
                    continue
                copies = 0
                for x, y in itertools.combinations(nodes, 2):
                    K = H.copy(); K.remove_nodes_from([x, y])
                    if canon(K) == cF:
                        copies += 1
                        if copies > 1:
                            break
                if copies != 1:
                    continue
                if not nx.is_isomorphic(G, H):
                    return False
    return True
