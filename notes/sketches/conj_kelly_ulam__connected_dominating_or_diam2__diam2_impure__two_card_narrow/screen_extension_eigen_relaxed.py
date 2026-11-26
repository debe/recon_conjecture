"""Relaxed (non-vacuous) screen of child extension_eigen.  Evidence only.

Drops "G not~= H".  The hypomorphism class of G is then (for n <= 13) the labelled copies of
G; one representative K = G suffices by relabelling.  Checks, for every G in NF(d):
  (a) and (c)  must hold without the counterexample (their paper proofs, A0-A2, use only
               NF(d) and membership in the class);  a failure would break the child.
  (d)          the paper's proof (A4/A5) needs a nontrivial extension at every vertex of the
               class of u, which comes from the counterexample (A3).  Checked here only when
               (b) holds as well; the unconditional (d) is reported in STATS.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from screen_common import deck_key, nf_ds, stage_a  # noqa: E402

STATS = {"nf": 0, "b_holds": 0, "d_fails_uncond": 0, "nontriv_pairs": 0, "dpairs": 0}
WIT_D = []


def claim(G):
    if G.number_of_nodes() < 3:
        return True
    deck = None
    for d in nf_ds(G):
        deck = deck or deck_key(G)
        STATS["nf"] += 1
        a, b, c, dd, info = stage_a([G], deck, d)
        STATS["dpairs"] += info["dpairs"]
        if b:
            STATS["b_holds"] += 1
        if not dd:
            STATS["d_fails_uncond"] += 1
            WIT_D.append((G.number_of_nodes(), sorted(G.edges()), d, info["fail"]))
        if not (a and c):
            print("FAIL a/c", d, info["fail"])
            return False
        if b and not dd:
            print("FAIL d given b", d, info["fail"])
            return False
    if G.number_of_nodes() == 7 and G.number_of_edges() == 21:
        print("STATS", STATS, "d-uncond witnesses (first 3):", WIT_D[:3])
    return True
