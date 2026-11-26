"""Faithful screen of child ...__two_card_narrow__low_extension_pair (Stage B, low case).

claim_pair(G, H): for a counterexample pair in NF(d) with the Stage A conclusions holding,
every u of degree d has |C_G(u)| <= 2 (any three extensions are not pairwise distinct).

Fidelity as in screen_extension_eigen.py; VACUOUS FOR n <= 13 (no counterexample pair).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from screen_common import canon, deck_key, nf_ds, stage_a, low_bound  # noqa: E402


def claim_pair(G, H):
    if G.number_of_nodes() < 3 or deck_key(G) != deck_key(H) or canon(G) == canon(H):
        return True
    deck = deck_key(G)
    for d in nf_ds(G):
        a, b, c, dd, _ = stage_a([G, H], deck, d)
        if a and b and c and dd and not low_bound(G, deck, d)[0]:
            return False
    return True
