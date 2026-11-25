"""Where Zinchenko's chain (arXiv:2611.13728v1) breaks for tournaments. Evidence only.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/debe_zinchenko_tournament_check.py

Part 1 (exhaustive, n = 4, 5, 6): group all tournaments by deck; for every deck class with at
least two non-isomorphic members print t (number of card types), the score sequences, and the
tournament analogue of the paper's chain:
  normal form   scores {d, d+1}, one card type per score class
  L2.1          card type determines the score of the deleted vertex inside the deck class
  L2.4          A chi = b 1 + theta chi  (A(x, y) = [x -> y], chi = indicator of score d+1)
  L3.1(c)       (A - (theta - s) I) z = k eps_u for z = a_G(u) - a_K(u), K an extension
  L3.3          every RIGHT (theta - s)-eigenvector of A vanishes at u   (uses A = A^T)
  L3.3'         every LEFT one does (this is what the proof gives without symmetry)
  L4.4          every card has exactly two extensions inside the deck class
Part 2: Stockmeyer's pairs B_k, C_k (n = 5, 9, 17): t and the score sets.
Part 3: relaxed single-tournament forms of L3.1(c), L3.3, L3.4 (as in debe_zinchenko_claims.py).
        No tournament with an extension was found for n <= 6, so Part 3 is vacuous there.
"""
import io
import itertools
import os
import sys
from collections import Counter, defaultdict
from contextlib import redirect_stdout

import sympy

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_tournament_check import canon_table, matrix  # noqa: E402


def mask_of(A, pidx):
    m = 0
    for (a, b), e in pidx.items():
        if A[a][b]:
            m |= 1 << e
    return m


def cards(A, n, pidx_small, can_small):
    out = []
    for v in range(n):
        rest = [w for w in range(n) if w != v]
        cm = 0
        for (a, b), e in pidx_small.items():
            if A[rest[a]][rest[b]]:
                cm |= 1 << e
        out.append(int(can_small[cm]))
    return out


def chain(A, n, deck, deck_of, pidx):
    """Tournament analogue of the paper's chain for one member A of a non-trivial deck class."""
    score = [sum(r) for r in A]
    ds = sorted(set(score))
    res = {}
    res["scores"] = sorted(score)
    if len(ds) != 2 or ds[1] != ds[0] + 1:
        res["normal_form"] = False
        return res
    d = ds[0]
    chi = [1 if s == d + 1 else 0 for s in score]
    hi_out = [sum(A[x][y] * chi[y] for y in range(n)) for x in range(n)]
    bs = {hi_out[x] for x in range(n) if not chi[x]}
    es = {hi_out[x] for x in range(n) if chi[x]}
    res["normal_form"] = True
    res["L2.4"] = len(bs) == 1 and len(es) == 1
    if not res["L2.4"]:
        return res
    theta = es.pop() - bs.pop()
    ok31 = ok33 = ok33l = True
    next_counts = []
    for u in range(n):
        s = chi[u]
        M = sympy.Matrix(n, n, lambda i, j: A[i][j] - ((theta - s) if i == j else 0))
        others = [x for x in range(n) if x != u]
        exts = []
        for bits in itertools.product((0, 1), repeat=n - 1):
            K = [row[:] for row in A]
            for x, bt in zip(others, bits):
                K[u][x], K[x][u] = bt, 1 - bt
            if K == A:
                continue
            if deck_of[mask_of(K, pidx)] != deck:
                continue
            z = [A[u][x] - K[u][x] for x in range(n)]
            k = sum(1 for x in z if x == 1)
            exts.append((z, k))
            rhs = [k if x == u else 0 for x in range(n)]
            if list(M * sympy.Matrix(z)) != rhs:
                ok31 = False
        next_counts.append(len(exts) + 1)
        if exts:
            if any(f[u] != 0 for f in M.nullspace()):
                ok33 = False
            if any(f[u] != 0 for f in M.T.nullspace()):
                ok33l = False
    res["L3.1c"] = ok31
    res["L3.3_right"] = ok33
    res["L3.3_left"] = ok33l
    res["extensions_per_card"] = next_counts
    return res


def part1():
    tables = {n: canon_table(n) for n in (3, 4, 5, 6)}
    for n in (4, 5, 6):
        pairs, can = tables[n]
        ppairs, pcan = tables[n - 1]
        pidx = {p: e for e, p in enumerate(pairs)}
        pidx_small = {p: e for e, p in enumerate(ppairs)}
        deck_of_rep = {}
        for mask in sorted(set(can.tolist())):
            A = matrix(n, pairs, mask)
            deck_of_rep[mask] = tuple(sorted(cards(A, n, pidx_small, pcan)))
        deck_of = {m: deck_of_rep[int(c)] for m, c in enumerate(can.tolist())}
        groups = defaultdict(list)
        for rep, dk in deck_of_rep.items():
            groups[dk].append(rep)
        bad = {dk: g for dk, g in groups.items() if len(g) > 1}
        print(f"n={n}: {len(deck_of_rep)} tournaments, {len(groups)} decks, "
              f"{len(bad)} deck classes with non-isomorphic members")
        for dk, g in bad.items():
            t = len(set(dk))
            print(f"  deck class {g}: t = {t}, card multiplicities {sorted(Counter(dk).values())}")
            for rep in g:
                A = matrix(n, pairs, rep)
                cs = cards(A, n, pidx_small, pcan)
                sc = [sum(r) for r in A]
                by_type = defaultdict(set)
                for v in range(n):
                    by_type[cs[v]].add(sc[v])
                l21 = all(len(s) == 1 for s in by_type.values())
                print(f"    {rep}: card type determines score within this tournament: {l21}; "
                      f"{chain(A, n, dk, deck_of, pidx)}")


def part2():
    import networkx as nx
    from networkx.algorithms.isomorphism import DiGraphMatcher
    with redirect_stdout(io.StringIO()):
        from t1_stockmeyer_check import stockmeyer
    for k in (2, 3, 4):
        for name in "BC":
            T = stockmeyer(k, name)
            reps = []
            for v in T:
                S = nx.DiGraph(T.subgraph([w for w in T if w != v]))
                if not any(DiGraphMatcher(S, R).is_isomorphic() for R in reps):
                    reps.append(S)
            print(f"  Stockmeyer {name}_{k} (n={2**k+1}): t = {len(reps)}, "
                  f"score set {sorted(set(dd for _, dd in T.out_degree()))}")




def part3():
    """Relaxed (single-tournament) forms, as in debe_zinchenko_claims.py: a dbe-tournament has
    scores {d, d+1} and constant numbers b, e of high out-neighbours; a dbe-extension at u
    re-orients arcs at u and is again a dbe-tournament with the same (d, b, e)."""
    def dbe(A, n):
        score = [sum(r) for r in A]
        ds = sorted(set(score))
        if len(ds) != 2 or ds[1] != ds[0] + 1:
            return None
        chi = [1 if s == ds[1] else 0 for s in score]
        ho = [sum(A[x][y] * chi[y] for y in range(n)) for x in range(n)]
        bs = {ho[x] for x in range(n) if not chi[x]}
        es = {ho[x] for x in range(n) if chi[x]}
        if len(bs) != 1 or len(es) != 1:
            return None
        return ds[0], bs.pop(), es.pop(), chi

    for n in (5, 6, 7):
        pairs = list(itertools.combinations(range(n), 2))
        seen = tot = ext_cases = c31 = right_fail = left_fail = k_differ = 0
        import random
        rng = random.Random(n)
        masks = range(1 << len(pairs)) if n <= 6 else (rng.getrandbits(len(pairs)) for _ in range(60000))
        for mask in masks:
            A = matrix(n, pairs, mask)
            par = dbe(A, n)
            if par is None:
                continue
            tot += 1
            d, b, e, chi = par
            theta = e - b
            for u in range(1):          # by relabelling, vertex 0 is enough for labelled enumeration
                s = chi[u]
                others = [x for x in range(n) if x != u]
                exts = []
                for bits in itertools.product((0, 1), repeat=n - 1):
                    if sum(bits) != sum(A[u]):
                        continue
                    K = [row[:] for row in A]
                    for x, bt in zip(others, bits):
                        K[u][x], K[x][u] = bt, 1 - bt
                    if K == A:
                        continue
                    p2 = dbe(K, n)
                    if p2 is None or p2[:3] != (d, b, e):
                        continue
                    z = [A[u][x] - K[u][x] for x in range(n)]
                    exts.append((z, sum(1 for x in z if x == 1)))
                if not exts:
                    continue
                ext_cases += 1
                M = sympy.Matrix(n, n, lambda i, j: A[i][j] - ((theta - s) if i == j else 0))
                for z, k in exts:
                    if list(M * sympy.Matrix(z)) != [k if x == u else 0 for x in range(n)]:
                        c31 += 1
                if any(f[u] != 0 for f in M.nullspace()):
                    right_fail += 1
                if any(f[u] != 0 for f in M.T.nullspace()):
                    left_fail += 1
                if len({k for _, k in exts}) > 1:
                    k_differ += 1
        print(f"  n={n}: dbe-tournaments (labelled{'' if n <= 6 else ', sampled'}) {tot}; with a dbe-extension at vertex 0: "
              f"{ext_cases}; L3.1(c) failures {c31}; RIGHT-eigenvector vanishing (L3.3) failures "
              f"{right_fail}; LEFT-eigenvector vanishing failures {left_fail}; "
              f"cases with two extensions of different k (L3.4 conclusion fails) {k_differ}")


if __name__ == "__main__":
    part1()
    part2()
    print("Part 3: relaxed single-tournament forms (vacuous if no extension is found)")
    part3()
