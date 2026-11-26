"""Faithful screen of child ...__two_card_narrow__extension_pair_compl (complement transfer).

The Lean statement is (forall counterexamples: low bound) -> (forall counterexamples: bound
at every vertex).  Its pair-local content, which is all the intended proof uses, is encoded:
for a counterexample (G, H) in NF(d): low bound for (G, H) in NF(d) and low bound for
(compl G, compl H) in NF(n-2-d)  ==>  bound at every vertex of G.

Fidelity: the global hypothesis is replaced by its two instances; this is weaker than the
Lean hypothesis, so a witness here would not by itself refute the Lean child.  VACUOUS FOR
n <= 13 (no counterexample pair).
"""
import os, sys
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from screen_common import canon, deck_key, nf_ds, low_bound, all_bound  # noqa: E402


def claim_pair(G, H):
    n = G.number_of_nodes()
    if n < 3 or deck_key(G) != deck_key(H) or canon(G) == canon(H):
        return True
    Gc, Hc = nx.complement(G), nx.complement(H)
    for d in nf_ds(G):
        lowG = low_bound(G, deck_key(G), d)[0]
        lowGc = (n - 2 - d >= 0) and low_bound(Gc, deck_key(Gc), n - 2 - d)[0]
        if lowG and lowGc and not all_bound(G, deck_key(G))[0]:
            return False
    return True
