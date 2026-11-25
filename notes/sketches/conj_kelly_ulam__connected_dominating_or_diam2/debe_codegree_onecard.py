"""One-card classes with vertex-key data (sketch debe_codegree, section 7). Evidence only.

For a vertex u and a set S of the right size let G_S be the graph that agrees with G off u
and has N(u) = S.  Classes (each: for SOME u, EVERY S passing the filter has G_S isomorphic
to G):
  OCdeg : filter = degree sequence of G_S equals that of G        (level balance)
  OCkey : filter = multiset of keys (deg, t, tbar) of G_S equals that of G
  OCtab : OCkey filter and the degree-typed pair table pi_a(F) of G_S equals that of G

  python3 .../debe_codegree_onecard.py [n_max]         exhaustive statistics (default 7)
  python3 .../debe_codegree_onecard.py g6 <graph6>...  single graphs
"""
import itertools
import os
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon  # noqa: E402
from debe_codegree_lib import keys, deg_table  # noqa: E402


def level_sets(G, u):
    """All S != N(u) with the degree sequence of G (level balance), as frozensets."""
    N = frozenset(G[u])
    levels = {}
    for y in sorted(G.nodes()):
        if y == u:
            continue
        levels.setdefault(G.degree(y) - (1 if y in N else 0), []).append(y)
    choices = []
    for j, L in sorted(levels.items()):
        k = sum(1 for y in L if y in N)
        choices.append([frozenset(C) for C in itertools.combinations(L, k)])
    for combo in itertools.product(*choices):
        S = frozenset().union(*combo)
        if S != N:
            yield S


def ext(G, u, S):
    H = G.copy()
    H.remove_node(u)
    H.add_node(u)
    H.add_edges_from((u, s) for s in S)
    return H


def onecard(G, want=("OCdeg", "OCkey", "OCtab")):
    cg = canon(G)
    kms = sorted(keys(G).values())
    tab = None
    res = {w: False for w in want}
    for u in sorted(G.nodes()):
        bad = {w: False for w in want}
        for S in level_sets(G, u):
            H = ext(G, u, S)
            iso = None
            if "OCdeg" in want and not bad["OCdeg"]:
                iso = canon(H) == cg
                if not iso:
                    bad["OCdeg"] = True
            need = [w for w in ("OCkey", "OCtab") if w in want and not bad[w]]
            if not need:
                if all(bad.values()):
                    break
                continue
            if sorted(keys(H).values()) != kms:
                continue
            if iso is None:
                iso = canon(H) == cg
            if iso:
                continue
            if "OCkey" in need:
                bad["OCkey"] = True
            if "OCtab" in need:
                if tab is None:
                    tab = deg_table(G)[0]
                if deg_table(H)[0] == tab:
                    bad["OCtab"] = True
        for w in want:
            if not bad[w]:
                res[w] = True
        if all(res.values()):
            break
    return res


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "g6":
        for g6 in sys.argv[2:]:
            G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
            print(g6, onecard(G), flush=True)
        return
    from t1_stats import graphs
    from debe_codegree_stats import residual_kind
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    for n in range(4, n_max + 1):
        cnt = Counter()
        out = {"OCdeg": [], "OCkey": [], "OCtab": []}
        for G in graphs(n):
            r = onecard(G)
            k = residual_kind(G)
            cnt["all"] += 1
            if k:
                cnt[k] += 1
            for w, v in r.items():
                if v:
                    cnt["all_" + w] += 1
                    if k:
                        cnt[k + "_" + w] += 1
                elif len(out[w]) < 40:
                    out[w].append(nx.to_graph6_bytes(G, header=False).decode().strip())
        print(n, dict(cnt), flush=True)
        for w in out:
            print(n, "outside", w, ":", out[w], flush=True)


if __name__ == "__main__":
    main()
