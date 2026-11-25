"""Where the spectral chain of sketch t3 breaks for tournaments. Evidence only, never a result.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t3_tournament_check.py

Enumerates all labelled tournaments on 5 and 6 vertices, groups them by deck, and for every
pair of non-isomorphic tournaments with the same deck prints
  - the characteristic polynomial of the adjacency matrix (lemma S2 would make them equal),
  - the number of directed Hamiltonian cycles (lemma S1 would make them equal),
  - the number of spanning cycles of the underlying K_n by orientation type is NOT computed:
    their total is (n-1)!/2 for every tournament, which is why the Kocay equation is vacuous.
"""
import itertools
import sys
import os
from collections import defaultdict

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import charpoly  # noqa: E402


def canon_table(n):
    """canonical mask for every labelled tournament on n vertices (bit e set: i -> j for pair e=(i<j))"""
    pairs = list(itertools.combinations(range(n), 2))
    idx = {p: e for e, p in enumerate(pairs)}
    m = len(pairs)
    masks = np.arange(1 << m, dtype=np.int64)
    best = masks.copy()
    for perm in itertools.permutations(range(n)):
        out = np.zeros_like(masks)
        for e, (i, j) in enumerate(pairs):
            a, b = perm[i], perm[j]
            bit = (masks >> e) & 1          # 1: i -> j
            if a < b:
                out |= bit << idx[(a, b)]
            else:
                out |= (1 - bit) << idx[(b, a)]
        best = np.minimum(best, out)
    return pairs, best


def matrix(n, pairs, mask):
    A = [[0] * n for _ in range(n)]
    for e, (i, j) in enumerate(pairs):
        if (mask >> e) & 1:
            A[i][j] = 1
        else:
            A[j][i] = 1
    return A


def ham_cycles(A):
    n = len(A)
    return sum(1 for p in itertools.permutations(range(1, n))
               if all(A[s][t] for s, t in zip((0,) + p, p + (0,))))


def main():
    tables = {}
    for n in (4, 5, 6):
        tables[n] = canon_table(n)
    for n in (5, 6):
        pairs, can = tables[n]
        ppairs, pcan = tables[n - 1]
        pidx = {p: e for e, p in enumerate(ppairs)}
        reps = sorted(set(can.tolist()))
        decks = defaultdict(list)
        for mask in reps:
            A = matrix(n, pairs, mask)
            cards = []
            for v in range(n):
                rest = [w for w in range(n) if w != v]
                cm = 0
                for (a, b), e in pidx.items():
                    if A[rest[a]][rest[b]]:
                        cm |= 1 << e
                cards.append(int(pcan[cm]))
            decks[tuple(sorted(cards))].append(mask)
        print(f"n={n}: {len(reps)} tournaments, {len(decks)} decks")
        for key, group in decks.items():
            if len(group) < 2:
                continue
            for mask in group:
                A = matrix(n, pairs, mask)
                cp = [int(c) for c in charpoly(A)]
                print(f"   mask {mask:>6}: charpoly coefficients {cp}  directed Hamiltonian cycles {ham_cycles(A)}"
                      f"  scores {sorted(sum(r) for r in A)}")
            print("   --")


if __name__ == "__main__":
    main()


def walk_profile_check():
    """n = 6: for each pair with the same deck, compare (card type, out-walk profile, in-walk
    profile, closed-walk profile) vertex by vertex, and the rank of the out-walk matrix."""
    from t3_lib import matvec, rank
    n = 6
    pairs, can = canon_table(n)
    ppairs, pcan = canon_table(n - 1)
    pidx = {p: e for e, p in enumerate(ppairs)}
    reps = sorted(set(can.tolist()))
    decks = defaultdict(list)
    info = {}
    for mask in reps:
        A = matrix(n, pairs, mask)
        At = [list(r) for r in zip(*A)]
        out, inn, x, y = [], [], [1] * n, [1] * n
        P = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
        closed = []
        for _ in range(n + 1):
            out.append(x)
            inn.append(y)
            closed.append([P[i][i] for i in range(n)])
            x, y = matvec(A, x), matvec(At, y)
            P = [[sum(P[i][l] * A[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        cards = []
        for v in range(n):
            rest = [w for w in range(n) if w != v]
            cm = 0
            for (a, b), e in pidx.items():
                if A[rest[a]][rest[b]]:
                    cm |= 1 << e
            cards.append(int(pcan[cm]))
        decks[tuple(sorted(cards))].append(mask)
        info[mask] = dict(
            closed=sorted((cards[v], tuple(c[v] for c in closed)) for v in range(n)),
            outw=sorted((cards[v], tuple(c[v] for c in out)) for v in range(n)),
            inw=sorted((cards[v], tuple(c[v] for c in inn)) for v in range(n)),
            rank=rank(out[:n]))
    for group in decks.values():
        if len(group) == 2:
            a, b = (info[g] for g in group)
            print(f"   n=6 pair {group}: closed-walk profiles by card agree: {a['closed'] == b['closed']};"
                  f" out-walk profiles by card agree: {a['outw'] == b['outw']};"
                  f" in-walk: {a['inw'] == b['inw']}; rank of out-walk matrix: {a['rank']}, {b['rank']}")


if __name__ == "__main__":
    walk_profile_check()
