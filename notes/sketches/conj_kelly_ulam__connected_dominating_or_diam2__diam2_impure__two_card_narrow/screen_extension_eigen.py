"""Faithful screen of child ...__two_card_narrow__extension_eigen (Stage A, (a)-(d)).

claim_pair(G, H): if n >= 3, G in NF(d) (for each admissible d; Lean quantifies d), G ~ H and
G not~= H, then (a), (b), (c) with one global theta, and (d) hold over the hypomorphism class.

Fidelity: Hypomorphic is tested exactly by deck equality.  The class is represented by the
two isomorphism types G, H handed over by the tool (a third type in the same deck class would
be missed; none exists for n <= 13).  Conditions are relabelling-invariant, so one
representative per type suffices.  The tool only hands pairs with equal decks, and for
3 <= n <= 13 every such pair is isomorphic, so the antecedent never fires: THIS SCREEN IS
VACUOUS FOR n <= 13.  See screen_extension_eigen_relaxed.py for the non-vacuous checks.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from screen_common import canon, deck_key, nf_ds, stage_a  # noqa: E402

FIRED = [0]


def claim_pair(G, H):
    if G.number_of_nodes() < 3 or deck_key(G) != deck_key(H) or canon(G) == canon(H):
        return True
    for d in nf_ds(G):
        FIRED[0] += 1
        a, b, c, dd, _ = stage_a([G, H], deck_key(G), d)
        if not (a and b and c and dd):
            return False
    return True
