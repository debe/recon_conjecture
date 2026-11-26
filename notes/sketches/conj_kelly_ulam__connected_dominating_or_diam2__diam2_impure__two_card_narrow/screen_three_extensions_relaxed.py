"""Relaxed screen of child three_extensions: the H-free part.  Evidence only.

For every G (n >= 3), u, u', card isomorphism alpha : G - u ~= G - u' (capped at 200 per
pair), x ~ u with alpha(x) not~ u': K2 := G - u' re-attached to alpha(N(u)) is hypomorphic
to G, agrees with G off u' (by construction) and differs from G.  The third member (iso to H)
needs the counterexample and cannot be tested.
"""
import itertools, os, sys
from networkx.algorithms.isomorphism import GraphMatcher
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from screen_common import deck_key, reattach  # noqa: E402


def claim(G):
    if G.number_of_nodes() < 3:
        return True
    dk = None
    for u in G:
        for u2 in G:
            A = G.subgraph([y for y in G if y != u])
            B = G.subgraph([y for y in G if y != u2])
            for al in itertools.islice(GraphMatcher(A, B).isomorphisms_iter(), 200):
                if all(G.has_edge(u2, al[x]) for x in G[u]):
                    continue
                N = frozenset(al[x] for x in G[u])
                K2 = reattach(G, u2, N)
                dk = dk or deck_key(G)
                if deck_key(K2) != dk or set(map(frozenset, K2.edges())) == set(map(frozenset, G.edges())):
                    return False
    return True
