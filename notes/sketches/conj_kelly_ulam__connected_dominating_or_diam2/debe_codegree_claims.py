"""Single-graph identities and single-card forms behind sketch debe_codegree. Evidence only.

claim(G) checks, for every graph G:
 (1) Law 0: x !~ y  =>  t(x) + t(y) = t(G) - t(G - x - y)
     Law 1: x ~ y   =>  tbar(x) + tbar(y) = tbar(G) - tbar(G - x - y)
     (plus the codegree forms: x ~ y => t(x) + t(y) = t(G) - t(F) + codeg, and dually).
 (2) If (R) holds: the recursion of Theorem A,
       eps_k(F) = pi_{k'}(F) - pi_{k''}(F) + eps_{k''}(F),
     with k' the unique occurring key with (deg, tbar) = (s + 1 - a, cbar - tbar) and k'' the
     unique occurring key with (deg, t) = (a - 1, c - t'), missing keys counting 0.
 (3) Strong single-card form (no deck presupposed): let u be a vertex such that every pair
     (u, y) is forced by 'deg', 'ref' or 'esc' (debe_codegree_lib.forced_pairs). Then every
     graph H' obtained from the card G - u by adding a vertex of degree deg u that has the
     refined table pi of G (pi_k(F) for every key k and type F) attaches the new vertex to
     exactly N_G(u).  More precisely, per pair: y in S iff y in N(u) for each forced pair.
"""
import itertools
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from debe_codegree_lib import (keys, tri, cotri, codeg, cocodeg, cond_R, pair_types,
                               ref_table, forced_pairs)  # noqa: E402
from t4_lib import degseq  # noqa: E402


def total_tri(G):
    return sum(tri(G, x) for x in G.nodes()) // 3


def total_cotri(G):
    return sum(cotri(G, x) for x in G.nodes()) // 3


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    key = keys(G)
    ty = pair_types(G)
    tG, tbG, eG = total_tri(G), total_cotri(G), G.number_of_edges()
    # (1) laws
    inv = {}
    for (x, y), F in ty.items():
        if x > y:
            continue
        S = [w for w in G.nodes() if w not in (x, y)]
        Fg = G.subgraph(S)
        tF, tbF, eF = total_tri(Fg), total_cotri(Fg), Fg.number_of_edges()
        inv[F] = (eG - eF, tG - tF, tbG - tbF)
        ax, tx, tbx = key[x]
        ay, ty_, tby = key[y]
        if G.has_edge(x, y):
            if ax + ay != eG - eF + 1:
                return False
            if tbx + tby != tbG - tbF:
                return False
            if tx + ty_ != tG - tF + codeg(G, x, y):
                return False
        else:
            if ax + ay != eG - eF:
                return False
            if tx + ty_ != tG - tF:
                return False
            if tbx + tby != tbG - tbF + cocodeg(G, x, y):
                return False
    pi, e = ref_table(G, key, ty)
    # (2) recursion under (R)
    if cond_R(key):
        occ = set(key.values())
        by_dtb = {(a, tb): (a, t, tb) for (a, t, tb) in occ}
        by_dt = {(a, t): (a, t, tb) for (a, t, tb) in occ}
        for F, (s, c, cb) in inv.items():
            for k in occ:
                a, t, tb = k
                k1 = by_dtb.get((s + 1 - a, cb - tb))
                if k1 is None:
                    rhs = 0
                else:
                    k2 = by_dt.get((a - 1, c - k1[1]))
                    rhs = pi[(F, k1)]
                    if k2 is not None:
                        rhs += e[(F, k2)] - pi[(F, k2)]
                if e[(F, k)] != rhs:
                    return False
    # (3) strong single-card form
    fp, R = forced_pairs(G)
    target = degseq(G)
    for u in G.nodes():
        others = [w for w in G.nodes() if w != u]
        forced = [y for y in others if fp[(u, y)]]
        if not forced:
            continue
        N = frozenset(G[u])
        base = G.copy()
        base.remove_node(u)
        for S in itertools.combinations(others, len(N)):
            Ss = frozenset(S)
            if Ss == N:
                continue
            if all((y in Ss) == (y in N) for y in forced):
                continue
            H = base.copy()
            H.add_node(u)
            H.add_edges_from((u, s) for s in Ss)
            if degseq(H) != target:
                continue
            pi_h, _ = ref_table(H)
            if pi_h == pi:
                return False
    return True
