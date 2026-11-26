"""Proposition L_k of the sketch (block lemma) on circulants minus a vertex. Evidence only;
the proposition has a paper argument for all n and k.

X = circulant C_m(conn), G = X - 0.  For k = 1, 2, 3 (and 4 if asked): the k-sets K of V(G)
such that G - K has a unique copy among the k-subsets.  CLAIM (L_k): K + {0} is then a block of
imprimitivity of Aut(X) (so k + 1 divides m); here the blocks through 0 of the translation
group are the subgroups of Z_m, and blocks of Aut(X) are among them.
"""
import itertools
import sys
from collections import Counter

from t3o_lib import *


def circulant(m, conn):
    X = nx.Graph()
    X.add_nodes_from(range(m))
    for i in range(m):
        for s in conn:
            X.add_edge(i, (i + s) % m)
    return X


def subgroups(m):
    return {frozenset(range(0, m, m // d)) for d in range(1, m + 1) if m % d == 0}


cases = [(12, (1, 2, 3)), (12, (1, 5)), (12, (1, 3, 4)), (13, (1, 2, 4)), (13, (1, 5)),
         (14, (1, 2, 4)), (15, (1, 2, 6)), (15, (1, 4)), (16, (1, 2, 5)), (16, (1, 4, 6))]
kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
for m, conn in cases:
    X = circulant(m, conn)
    G = nx.convert_node_labels_to_integers(X.subgraph(range(1, m)), first_label=1)
    G = X.subgraph(range(1, m))
    sg = subgroups(m)
    row = []
    ok = True
    for k in range(1, kmax + 1):
        ty = {K: canon(nx.convert_node_labels_to_integers(G.subgraph([x for x in G if x not in K])))
              for K in itertools.combinations(sorted(G), k)}
        cnt = Counter(ty.values())
        uniq = [K for K, F in ty.items() if cnt[F] == 1]
        is_block = [frozenset(K) | {0} in sg for K in uniq]
        ok = ok and all(is_block)
        row.append((k, "min copies %d" % min(cnt.values()), "unique:", uniq))
    print(f"C_{m}{conn} - 0: |Aut X| = {len(auts(X))};", row, "| all unique-copy sets are subgroups minus 0:", ok)
