"""Check of the fibre calculus (sketch t3, Lemma J) on small lexicographic products X[A], X prime.
Evidence only.   python3 t3s_fibre.py
Predictions, for G = X[A], u = (p,a), v = (p',b), w = (s,e):
  I-in   p = p' = s           : W3_G(u,v,w)  <=>  W3_A(a,b,e)
  I-out  p = p' != s          : W3_G(u,v,w)  <=>  W2_A(a,b)   (pair window census, kill over all of Aut(A-c-c'))
  II     p != p', clause (i)  : (W) holds;  (K) <=> no vertex c removal-similar to a (pinned copy when s = p)
                                 has a (pinned) automorphism of A - c that moves N_A(c)
Prints the number of classes of each kind and the number of disagreements.
"""
import sys
from collections import Counter, defaultdict

import networkx as nx

from t3s_lib import *


def w2_set(A):
    """ordered pairs at which the pair analogue W2 (window census, kill (K) over all of Aut(A-x-y)) holds."""
    C = Census(A, triples=False)
    members = defaultdict(list)
    for p, r in C.c2.items():
        members[r].append(p)
    bytype = defaultdict(list)
    for p, F in C.ty.items():
        bytype[F].append(p)
    out = set()
    for r, Acl in members.items():
        u, v = Acl[0]
        dv = A.degree(v) - int(A.has_edge(u, v))
        chat = {C.c2[(y, x)] for (x, y) in Acl}
        Rs = [p for p in bytype[C.ty[(u, v)]] if C.c2[p] not in chat and A.degree(p[0]) - dv in (0, 1)]
        if not len(Rs) < len(Acl):
            continue
        ok = True
        for (x, y) in Acl:
            S, Au, Nu, Nv, Ku, Kv = C.pd(x, y)
            if not all(k_trivial(A, x, y, S, Nu, g) or k_DP(A, S, g) for g in Au):
                ok = False
                break
        if ok:
            out.update(Acl)
    return out


def untwisted(A, a, pin=None):
    """no c removal-similar to a (with matching pin) has an automorphism of A-c (fixing the pin) moving N_A(c)."""
    V = sorted(A)
    for c in V:
        if pin is None:
            if canon_marked(A, (c,), ()) != canon_marked(A, (a,), ()):
                continue
            pins = [None]
        else:
            pins = [e for e in V if e != c and canon_marked(A, (c,), (e,)) == canon_marked(A, (a,), (pin,))]
            if not pins:
                continue
        S = [t for t in V if t != c]
        N = set(A[c])
        for h in auts(A, S):
            for e in pins:
                if e is not None and h[e] != e:
                    continue
                if {h[t] for t in N} != N:
                    return False
    return True


def run(nameX, X, nameA, A):
    G, lab, inv = lex(X, A)
    A = nx.convert_node_labels_to_integers(A)
    C = Census(G)
    got = w3_set(G, C)
    cl = {t: c for c in classes(G, C) for t in c["A"]}
    w3A = w3_set(A) if A.number_of_nodes() >= 3 else set()
    w2A = w2_set(A)
    cnt, bad = Counter(), Counter()
    ex = {}
    for (u, v, w) in C.c3:
        (p, a), (p2, b), (s, e) = inv[u], inv[v], inv[w]
        if p == p2 == s:
            kind, pred = "I-in", (a, b, e) in w3A
        elif p == p2:
            kind, pred = "I-out", (a, b) in w2A
        elif cond_i(G, u, v):
            kind = "II"
            pred = untwisted(A, a, e if s == p else None)
            if not cl[(u, v, w)]["W"]:
                bad["II: census fails"] += 1
        else:
            kind, pred = "II-no(i)", None
        cnt[kind] += 1
        if pred is not None and pred != ((u, v, w) in got):
            bad[kind] += 1
            ex.setdefault(kind, ((p, a), (p2, b), (s, e), pred))
        if pred is None and (u, v, w) in got:
            cnt["II-no(i) in W3"] += 1
    print("%s[%s] n=%d in W3: %s | classes %s | disagreements %s %s" % (
        nameX, nameA, G.number_of_nodes(), bool(got), dict(cnt), dict(bad), ex), flush=True)


XS = {"P4": nx.path_graph(4), "C5": nx.cycle_graph(5), "bull": nx.Graph([(0, 1), (1, 2), (0, 2), (0, 3), (1, 4)])}
AS = {"P3": nx.path_graph(3), "K1+K2": nx.Graph([(0, 1)]), "paw": nx.Graph([(0, 1), (1, 2), (0, 2), (2, 3)]),
      "P4": nx.path_graph(4), "claw": nx.star_graph(3), "K1+P3": nx.Graph([(0, 1), (1, 2)])}
AS["K1+K2"].add_node(2)
AS["K3"] = nx.complete_graph(3)
AS["E3"] = nx.empty_graph(3)
AS["C4"] = nx.cycle_graph(4)
AS["K1+P3"].add_node(3)
todo = sys.argv[1:] or ["P4:P3", "P4:K1+K2", "bull:P3", "C5:P3", "P4:paw", "P4:P4", "P4:claw", "P4:K1+P3", "P4:K3", "P4:E3", "bull:K3", "P4:C4"]
for t in todo:
    x, a = t.split(":")
    run(x, XS[x], a, AS[a])
