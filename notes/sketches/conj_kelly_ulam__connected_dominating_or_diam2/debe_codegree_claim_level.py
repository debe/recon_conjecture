"""Theorem D of sketch debe_codegree (level-wise half forcing), strong single-card form.

For a vertex u, the card level of y != u is j(y) = deg y - [u ~ y].  Call u *level-forced*
(for a set of labels) if in every level either every neighbour of u in the level is forced
or every non-neighbour of u in the level is forced, where y is forced when one of the
per-pair conditions of debe_codegree_lib.forced_pairs holds:
  'deg' all type-(G-u-y) pairs with first degree deg u have the adjacency of (u, y);
  'esc' triangle / codegree escape;   'ref' (R) and refined purity.

claim(G): for every level-forced u (labels deg, esc, ref together, and deg alone), every
graph obtained from the card G - u by adding a vertex of degree deg u that has the degree
sequence of G and the pair table of G (refined table pi_k(F) for the full label set,
degree-typed table pi_a(F) for 'deg' alone) attaches the new vertex to exactly N_G(u).
Also checks the level balance (T2) on every such extension: it meets every card level in
as many vertices as N(u) does.

These are the only facts about a hypomorphic H that the paper argument uses.
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from debe_codegree_lib import forced_pairs, ref_table, deg_table  # noqa: E402
from t4_lib import degseq  # noqa: E402


def level_forced(G, u, fp, labels):
    N = set(G[u])
    levels = {}
    for y in G.nodes():
        if y == u:
            continue
        levels.setdefault(G.degree(y) - (1 if y in N else 0), ([], []))[0 if y in N else 1].append(y)
    for nb, nn in levels.values():
        if all(fp[(u, y)] & labels for y in nb) or all(fp[(u, y)] & labels for y in nn):
            continue
        return False
    return True


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    fp, _ = forced_pairs(G)
    target = degseq(G)
    tabs = {}
    for labels, which in (({'deg'}, 'deg'), ({'deg', 'esc', 'ref'}, 'key')):
        for u in G.nodes():
            if not level_forced(G, u, fp, labels):
                continue
            if which not in tabs:
                tabs[which] = deg_table(G)[0] if which == 'deg' else ref_table(G)[0]
            N = frozenset(G[u])
            others = [w for w in G.nodes() if w != u]
            lev = {y: G.degree(y) - (1 if y in N else 0) for y in others}
            base = G.copy()
            base.remove_node(u)
            for S in itertools.combinations(others, len(N)):
                Ss = frozenset(S)
                if Ss == N:
                    continue
                H = base.copy()
                H.add_node(u)
                H.add_edges_from((u, s) for s in Ss)
                if degseq(H) != target:
                    continue
                # level balance must hold for every extension with the right degree sequence
                if sorted(lev[y] for y in Ss) != sorted(lev[y] for y in N):
                    return False
                th = deg_table(H)[0] if which == 'deg' else ref_table(H)[0]
                if th == tabs[which]:
                    return False
    return True
