"""Relaxed screen of child low_extension_pair.  Evidence only.

Drops "G not~= H" but keeps the Stage A hypothesis (a)-(d), evaluated on the hypomorphism
class of G.  Claim: NF(d) + (a)-(d)  ==>  every u of degree d has |C_G(u)| <= 2.
The paper's Stage B (B1-B4) uses the counterexample only through Stage A and NF(d), so this
relaxed form is what the proof route actually needs.  STATS also reports the unconditional
bound (no Stage A hypothesis), which is expected to fail on some graphs.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from screen_common import deck_key, nf_ds, stage_a, low_bound  # noqa: E402

STATS = {"nf": 0, "hyp": 0, "uncond_fail": 0}
EX = []


def claim(G):
    if G.number_of_nodes() < 3:
        return True
    for d in nf_ds(G):
        deck = deck_key(G)
        STATS["nf"] += 1
        ok, u = low_bound(G, deck, d)
        if not ok:
            STATS["uncond_fail"] += 1
            EX.append((sorted(G.edges()), d, u))
        a, b, c, dd, _ = stage_a([G], deck, d)
        if a and b and c and dd:
            STATS["hyp"] += 1
            if not ok:
                return False
    if G.number_of_nodes() == 7 and G.number_of_edges() == 21:
        print("STATS", STATS, "uncond examples:", EX[:3])
    return True
