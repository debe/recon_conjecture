"""Cross-check of the pair-level lead on the known members (evidence only):
T+ with clause (iii) replaced by (iii'): for every (x, y) in the pointed class A and every
automorphism g of G - x - y whose twist of x keeps the level counts of the degree filter
(round-11 t3, section 3.1), g factorizes as in the checked gluing clause.
Both orientations of the twist are tried (g and its inverse range over the same group)."""
import os
import sys
import importlib.util
from collections import Counter, defaultdict

from t3o_lib import *

HERE = os.path.dirname(os.path.abspath(__file__))
p = os.path.join(HERE, "..",
                 "conj_kelly_ulam__connected_dominating_or_diam2__diam2_impure__no_half_pure_no_two_card")
sys.path.insert(0, p)
spec = importlib.util.spec_from_file_location("r11", os.path.join(p, "t3_lib.py"))
r11 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r11)


def tplus_adm(G):
    ty = r11.pair_types(G)
    cid = r11.pointed_classes(G, ty)
    members = defaultdict(list)
    for q, i in cid.items():
        members[i].append(q)
    tsize = Counter(ty.values())
    out = []
    for (u, v) in ty:
        if not cond_i(G, u, v):
            continue
        A = members[cid[(u, v)]]
        chat = {cid[(y, x)] for (x, y) in A}
        if tsize[ty[(u, v)]] - len(A) - sum(len(members[j]) for j in chat) >= len(A):
            continue
        ok = True
        for (x, y) in A:
            S, Au, Nx, Ny = r11.pair_data(G, x, y)
            for g in Au:
                if r11.adm_deg(G, S, Nx, g) and not r11.factor_ok(Au, Nx, Ny, g):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            out.append((u, v))
    return out


if __name__ == "__main__":
    for s in sys.argv[1:]:
        G = from_g6(s)
        print(s, "pairs with (i), (ii), (iii'):", tplus_adm(G))
