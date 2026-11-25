"""Is the degree-refined walk count a function of the card? Evidence only, never a result.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t3_degree_walks.py [n_max]

Candidate lemma S7 of sketch t3 (NOT relied on): for a hypomorphism sigma : G -> H and all
j, k, the number of walks of length j from v that end in a vertex of degree k equals the same
number for sigma(v) in H. Lemma B of t2 is the case j = 1; lemma S4 is the sum over k.

Non-vacuous single-graph test: if G - x and G - y are isomorphic, the transposition (x y) is a
hypomorphism G -> G, so x and y must have the same degree-refined walk counts. Pseudo-similar
pairs exist from n = 8 on. Also tested: the same with "ends in" replaced by "starts in the
set of vertices whose card is of a given isomorphism type" (the finest refinement).
"""
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon, card, g6  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import adj, matvec  # noqa: E402
from t1_stats import graphs  # noqa: E402
from t3_pseudosimilar import orbits_key  # noqa: E402


def refined(G, classes):
    """for every vertex: tuple over classes C and j <= n of (A^j 1_C)_v"""
    nodes = sorted(G.nodes())
    n = len(nodes)
    A = adj(G, nodes)
    out = {v: [] for v in nodes}
    for C in classes:
        x = [1 if v in C else 0 for v in nodes]
        for _ in range(n + 1):
            for i, v in enumerate(nodes):
                out[v].append(x[i])
            x = matvec(A, x)
    return {v: tuple(p) for v, p in out.items()}


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    for n in range(4, n_max + 1):
        pairs = pseudo = bad_deg = bad_card = 0
        ex_deg = ex_card = None
        for G in graphs(n):
            by_card = defaultdict(list)
            for v in G.nodes():
                by_card[canon(card(G, v))].append(v)
            if all(len(c) == 1 for c in by_card.values()):
                continue
            degs = defaultdict(set)
            for v in G.nodes():
                degs[G.degree(v)].add(v)
            rd = refined(G, [degs[k] for k in sorted(degs)])
            rc = refined(G, [set(c) for _, c in sorted(by_card.items())])
            for cls in by_card.values():
                for i, a in enumerate(cls):
                    for b in cls[i + 1:]:
                        pairs += 1
                        if rd[a] != rd[b]:
                            bad_deg += 1
                            ex_deg = ex_deg or (g6(G), a, b)
                        if rc[a] != rc[b]:
                            bad_card += 1
                            ex_card = ex_card or (g6(G), a, b)
        print(f"n={n}: pairs with isomorphic cards: {pairs}; degree-refined walk mismatch: {bad_deg}"
              f" {ex_deg or ''}; card-type-refined walk mismatch: {bad_card} {ex_card or ''}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
