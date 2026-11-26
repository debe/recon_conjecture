"""Faithful screen of child ...__two_card_narrow__three_extensions (assembly).

claim_pair(G, H): n >= 3, G ~ H, G not~= H, alpha : G - u ~= G - u', x ~ u with alpha(x) not
~ u'  ==>  C_G(u') has three pairwise distinct members.  (No NF hypothesis in the Lean.)

Fidelity: alpha ranges over all card isomorphisms (networkx GraphMatcher).  VACUOUS FOR
n <= 13 (no counterexample pair).  See screen_three_extensions_relaxed.py.
"""
import os, sys
from networkx.algorithms.isomorphism import GraphMatcher
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from screen_common import canon, deck_key, extensions  # noqa: E402


def claim_pair(G, H):
    if G.number_of_nodes() < 3 or deck_key(G) != deck_key(H) or canon(G) == canon(H):
        return True
    deck = deck_key(G)
    for u in G:
        for u2 in G:
            A = G.subgraph([y for y in G if y != u])
            B = G.subgraph([y for y in G if y != u2])
            for al in GraphMatcher(A, B).isomorphisms_iter():
                if any(not G.has_edge(u2, al[x]) for x in G[u]):
                    if len(extensions(G, u2, deck)) < 3:
                        return False
                    break
    return True
