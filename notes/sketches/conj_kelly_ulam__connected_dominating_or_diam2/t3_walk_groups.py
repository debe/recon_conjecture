"""Lemmas S5 / S6 of sketch t3 in labelled form, exhaustively. Evidence only, never a result.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t3_walk_groups.py [n_max]

For every unlabelled graph G on n vertices (one labelled representative) find EVERY labelled
graph H' on the same vertex set with the same walk matrix W = [1, A1, ..., A^(n-1) 1]
(no deck is presupposed: this is the pure linear-algebra content). Check:

  S5   rank W >= n - 1            =>  H' = G is the only one;
  S6   rank W  = n - 2, H' != G   =>  Delta = A_G - A_H' is a balanced block switch
       (P1, P2, Q1, Q2; +1 on P1xQ1, P2xQ2; -1 on P1xQ2, P2xQ1; |P1| = |P2|, |Q1| = |Q2|),
       and if |P1| = 1 the transposition of P1, P2 maps G onto H' (same for Q).
Also reports how often rank Delta attains the bound n - rank W.
"""
import itertools
import os
import sys
from collections import Counter

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import all_graphs  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import rank  # noqa: E402


def walk_keys(A):
    """A: (B, n, n) int64 -> (B, n*n) walk matrices flattened"""
    B, n, _ = A.shape
    x = np.ones((B, n), dtype=np.int64)
    cols = []
    for _ in range(n):
        cols.append(x)
        x = np.einsum("bij,bj->bi", A, x)
    return np.stack(cols, axis=2).reshape(B, n * n)


def block_switch(D):
    """Return (P1, P2, Q1, Q2) if D is a balanced block switch, else None."""
    n = len(D)
    supp = [i for i in range(n) if any(D[i])]
    if not supp:
        return None
    i0 = supp[0]
    Q1 = {j for j in range(n) if D[i0][j] == 1}
    Q2 = {j for j in range(n) if D[i0][j] == -1}
    Q = Q1 | Q2
    P = set(supp) - Q
    if not Q1 or not Q2:
        return None
    j0 = min(Q1)
    P1 = {i for i in P if D[i][j0] == 1}
    P2 = {i for i in P if D[i][j0] == -1}
    if P1 | P2 != P or len(P1) != len(P2) or len(Q1) != len(Q2):
        return None
    for i in range(n):
        for j in range(n):
            want = 0
            if (i in P1 and j in Q1) or (i in P2 and j in Q2) or (j in P1 and i in Q1) or (j in P2 and i in Q2):
                want = 1
            if (i in P1 and j in Q2) or (i in P2 and j in Q1) or (j in P1 and i in Q2) or (j in P2 and i in Q1):
                want = -1
            if D[i][j] != want:
                return None
    return P1, P2, Q1, Q2


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    for n in range(3, n_max + 1):
        pairs = list(itertools.combinations(range(n), 2))
        m = len(pairs)
        reps = {}
        for G in all_graphs(n):
            A = np.zeros((1, n, n), dtype=np.int64)
            for u, v in G.edges():
                A[0, u, v] = A[0, v, u] = 1
            reps[walk_keys(A)[0].tobytes()] = reps.get(walk_keys(A)[0].tobytes(), []) + [A[0]]
        found = Counter()
        bad = []
        rank_attained = Counter()
        chunk = 1 << 16
        for start in range(0, 1 << m, chunk):
            masks = np.arange(start, min(start + chunk, 1 << m), dtype=np.int64)
            A = np.zeros((len(masks), n, n), dtype=np.int64)
            for e, (u, v) in enumerate(pairs):
                bit = (masks >> e) & 1
                A[:, u, v] = bit
                A[:, v, u] = bit
            keys = walk_keys(A)
            for b in range(len(masks)):
                kb = keys[b].tobytes()
                if kb not in reps:
                    continue
                for AG in reps[kb]:
                    D = (AG - A[b]).tolist()
                    if not any(any(r) for r in D):
                        continue
                    W = np.frombuffer(kb, dtype=np.int64).reshape(n, n)
                    r = rank(W.T.tolist())
                    cor = n - r
                    found[cor] += 1
                    rd = rank(D)
                    rank_attained[(cor, rd)] += 1
                    if cor <= 1:
                        bad.append(("S5", AG.tolist(), A[b].tolist()))
                    if cor == 2:
                        bs = block_switch(D)
                        if bs is None:
                            bad.append(("S6 shape", AG.tolist(), A[b].tolist()))
                            continue
                        P1, P2, Q1, Q2 = bs
                        for X1, X2 in ((P1, P2), (Q1, Q2)):
                            if len(X1) == 1:
                                a, c = next(iter(X1)), next(iter(X2))
                                perm = list(range(n))
                                perm[a], perm[c] = c, a
                                img = [[AG[perm[i]][perm[j]] for j in range(n)] for i in range(n)]
                                if img != A[b].tolist():
                                    bad.append(("S6 transposition", AG.tolist(), A[b].tolist()))
        print(f"n={n}: labelled H' != G with W(H') = W(G), by corank of W(G): {dict(sorted(found.items()))}")
        print(f"       (corank, rank Delta) counts: {dict(sorted(rank_attained.items()))}")
        print(f"       violations: {len(bad)}")
        for b in bad[:3]:
            print("       ", b)


if __name__ == "__main__":
    main()
