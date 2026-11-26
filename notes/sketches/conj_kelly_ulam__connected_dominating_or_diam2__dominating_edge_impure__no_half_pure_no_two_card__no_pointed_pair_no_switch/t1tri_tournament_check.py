"""Sanity check of the three-card gluing argument on NON-reconstructible objects.  Evidence only.

The argument of sketch t1 (unique copy of T - {u,v,w}, straightness (S), orbit intersection (OI))
uses nothing graph-specific, so it holds verbatim for tournaments.  Stockmeyer's tournaments
B_k, C_k (n = 2^k + 1) are hypomorphic and not isomorphic, so NO triple of B_k or C_k may satisfy
(U), (S) and (OI) together.  A triple that does would be a witness against the paper argument.
Printed: how many triples have (U), (U)+(S), (U)+(S)+(OI).
"""
import io
import itertools
import os
import sys
from collections import Counter
from contextlib import redirect_stdout

import networkx as nx
from networkx.algorithms.isomorphism import DiGraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "conj_kelly_ulam__connected_dominating_or_diam2"))
with redirect_stdout(io.StringIO()):
    from t1_stockmeyer_check import stockmeyer, hypomorphic, iso  # noqa: E402


def sub(T, drop):
    return nx.DiGraph(T.subgraph([w for w in T if w not in drop]))


def classes(T, k):
    reps, ty = [], {}
    for D in itertools.combinations(sorted(T), k):
        S = sub(T, D)
        for i, R in enumerate(reps):
            if DiGraphMatcher(S, R).is_isomorphic():
                break
        else:
            reps.append(S)
            i = len(reps) - 1
        ty[D] = i
    return ty


def auts(T, drop):
    S = sub(T, drop)
    return list(DiGraphMatcher(S, S).isomorphisms_iter())


def img(g, X):
    return frozenset(g[x] for x in X)


def analyse(T, name):
    V = sorted(T)
    t3 = classes(T, 3)
    t2 = classes(T, 2)
    cnt = Counter(t3.values())
    c = Counter()
    for D in t3:
        c["triples"] += 1
        if cnt[t3[D]] != 1:
            continue
        c["U"] += 1
        ok = True
        for x in D:
            y, z = [t for t in D if t != x]
            typ = t2[tuple(sorted((x, y)))] != t2[tuple(sorted((x, z)))]
            swap = any(g[y] == z and g[z] == y for g in auts(T, (x,)))
            if not (typ or swap):
                ok = False
        if not ok:
            continue
        c["U+S"] += 1
        A = auts(T, D)
        R = [x for x in V if x not in D]
        tr = {x: frozenset(r for r in R if T.has_edge(r, x)) for x in D}
        for u, v, w in itertools.permutations(D):
            oW = {img(g, tr[u]) for g in A if img(g, tr[w]) == tr[w]}
            oV = {img(g, tr[u]) for g in A if img(g, tr[v]) == tr[v]}
            oVW = {img(g, tr[u]) for g in A if img(g, tr[v]) == tr[v] and img(g, tr[w]) == tr[w]}
            if (oW & oV) == oVW:
                c["U+S+OI (ordered roles)"] += 1
                print("   WITNESS against the argument:", name, (u, v, w))
    print(name, dict(c))


if __name__ == "__main__":
    for k in (2, 3):
        B, Cc = stockmeyer(k, "B"), stockmeyer(k, "C")
        print("k =", k, "n =", B.number_of_nodes(), "hypomorphic:", hypomorphic(B, Cc), "isomorphic:", iso(B, Cc))
        analyse(B, "B_%d" % k)
        analyse(Cc, "C_%d" % k)


def anchored_check(G, H, name):
    """Direct test of the gluing lemma on a non-isomorphic hypomorphic pair (G, H): list the
    fully anchored configurations (u,v,w) -> (a,b,c) and test (OI) at (u; v, w) and (M) (w -> u).
    The lemma says: fully anchored + (OI) => G iso H.  So (OI) must fail at every one of them."""
    V, W = sorted(G), sorted(H)
    I = {}
    for u in V:
        for a in W:
            A, B = sub(G, (u,)), sub(H, (a,))
            I[(u, a)] = list(DiGraphMatcher(A, B).isomorphisms_iter())
    c = Counter()
    for u, v, w in itertools.permutations(V, 3):
        for a in W:
            for f in I[(u, a)]:
                b, cc = f[v], f[w]
                if not any(h[u] == a and h[w] == cc for h in I[(v, b)]):
                    continue
                if not any(h[u] == a and h[v] == b for h in I[(w, cc)]):
                    continue
                c["fully anchored"] += 1
                A = auts(G, (u, v, w))
                R = [x for x in V if x not in (u, v, w)]
                tr = {x: frozenset(r for r in R if G.has_edge(r, x)) for x in (u, v, w)}
                oW = {img(g, tr[u]) for g in A if img(g, tr[w]) == tr[w]}
                oV = {img(g, tr[u]) for g in A if img(g, tr[v]) == tr[v]}
                oVW = {img(g, tr[u]) for g in A if img(g, tr[v]) == tr[v] and img(g, tr[w]) == tr[w]}
                if (oW & oV) == oVW:
                    c["fully anchored with OI (a witness against the lemma unless G iso H)"] += 1
                if all(img(g, tr[u]) == tr[u] for g in A if img(g, tr[w]) == tr[w]):
                    c["fully anchored with M (a witness against the lemma unless G iso H)"] += 1
    print(name, dict(c))


if __name__ == "__main__":
    for k in (2, 3):
        B, Cc = stockmeyer(k, "B"), stockmeyer(k, "C")
        anchored_check(B, Cc, "B_%d -> C_%d" % (k, k))
        anchored_check(B, B, "B_%d -> B_%d (control: isomorphic, OI may hold)" % (k, k))
