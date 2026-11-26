"""Class sizes of C3 and its meeting with the residual.  Evidence only.

  python3 t1tri_stats.py 7        exhaustive n = 7: class sizes and the dominating-edge residual
  python3 t1tri_stats.py known    the n = 7, 8 graphs named in earlier sketches
"""
import importlib.util
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import t1tri_lib as L  # noqa: E402
from small_graphs import all_graphs, g6  # noqa: E402

D2 = os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card")
sys.path.insert(0, D2)


def _load(name, fn):
    spec = importlib.util.spec_from_file_location(name, os.path.join(D2, fn))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


US = _load("d2_t1us_lib", "t1us_lib.py")
USS = _load("d2_t1us_stats", "t1us_stats.py")


def residual_flags(G):
    cl = US.classify(G)
    fl = dict(branch=cl["branch"], rem_parent=cl["rem"])
    if cl["rem"]:
        ty = L.pair_types(G)
        cid = L.pointed_classes(G, ty)
        fl["T"] = bool(L.T_pairs(G, ty, cid, mode="rigid"))
        fl["Tplus"] = bool(L.Tplus_pairs(G, ty, cid))
        fl["US"] = bool(USS.us_vertices(G))
        fl["res"] = not (fl["T"] or fl["Tplus"] or fl["US"])
    else:
        fl["res"] = False
    return fl


def report(G):
    fl = residual_flags(G)
    m = L.c3_triples(G, "M")
    o = L.c3_triples(G, "OI")
    return fl, m, o


if __name__ == "__main__":
    arg = sys.argv[1]
    if arg == "known":
        for s in ["Ffk}W", "Ff]mw", "Gl]o^[", "GH?gmg", "GxckIs", "GKYZ}{", "GHvT~o", "GLvnnw"]:
            G = L.from_g6(s)
            fl, m, o = report(G)
            print(s, fl, "C3(M) triples:", len(m), m[:3], "C3(OI) triples:", len(o))
    else:
        n = int(arg)
        c = Counter()
        for G in all_graphs(n):
            c["all"] += 1
            m = bool(L.c3_triples(G, "M"))
            o = bool(L.c3_triples(G, "OI"))
            c["unique triple"] += bool(L.unique_triples(G))
            c["C3(M)"] += m
            c["C3(OI)"] += o
            fl = residual_flags(G)
            if fl["branch"] == "DE":
                c["DE"] += 1
                c["DE C3(M)"] += m
                if fl["rem_parent"]:
                    c["DE parent remainder"] += 1
                    c["DE parent remainder in C3(M)"] += m
                    print("  parent remainder:", g6(G), fl, "C3(M)", m, "C3(OI)", o, flush=True)
                if fl["res"]:
                    c["DE residual (this step)"] += 1
                    c["DE residual in C3(M)"] += m
                    c["DE residual in C3(OI)"] += o
            if fl["branch"] == "D2" and fl["rem_parent"]:
                print("  D2 parent remainder:", g6(G), fl, "C3(M)", m, flush=True)
        print(n, dict(c))
