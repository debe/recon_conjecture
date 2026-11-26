"""Red team, independent re-encoding of Theorem U of t1.md (strong single-card form).

claim(G): for every integer pair (a, b) with G 2wl(a, b) (unique for non-regular G; for
regular G every a in a window, b = d^2 - a d), every vertex u' with lambda = a - deg u'
not an eigenvalue of A_G:
  (1) at most one S != N(u'), S subset V - u', |S| = deg u', with G_S := (G - u') + u'~S
      2wl(a, b);
  (2) if some card iso alpha: G - u -> G - u' maps N(u) off N(u'), every such G_S is
      isomorphic to G.
Fidelity: (2) is strictly stronger than the Lean US child (which only asks reconstructible),
because the paper proof only uses: H 2wl(a,b) (REC), deg_H(sigma u') = deg u' (T0), and a
card iso H - sigma u' = G - u'. Written independently of t1us_lib.py.
"""
import itertools
from fractions import Fraction
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher


def det_int(M):
    n = len(M)
    M = [[Fraction(x) for x in row] for row in M]
    d = Fraction(1)
    for i in range(n):
        p = next((r for r in range(i, n) if M[r][i] != 0), None)
        if p is None:
            return 0
        if p != i:
            M[i], M[p] = M[p], M[i]
            d = -d
        d *= M[i][i]
        for r in range(i + 1, n):
            f = M[r][i] / M[i][i]
            if f:
                for c in range(i, n):
                    M[r][c] -= f * M[i][c]
    return d


def w2(G, x):
    return sum(G.degree(y) for y in G[x])


def pairs(G):
    n = G.number_of_nodes()
    degs = sorted(set(d for _, d in G.degree()))
    if len(degs) == 1:
        d = degs[0]
        return [(a, d * d - a * d) for a in range(-n - 2, 2 * n + 3)]
    x1 = next(v for v in G if G.degree(v) == degs[0])
    x2 = next(v for v in G if G.degree(v) == degs[1])
    num = w2(G, x2) - w2(G, x1)
    den = degs[1] - degs[0]
    if num % den:
        return []
    a = num // den
    b = w2(G, x1) - a * degs[0]
    if all(w2(G, x) == a * G.degree(x) + b for x in G):
        return [(a, b)]
    return []


def is2wl(G, a, b):
    return all(w2(G, x) == a * G.degree(x) + b for x in G)


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    nodes = list(G)
    A = [[1 if G.has_edge(i, j) else 0 for j in nodes] for i in nodes]
    for a, b in pairs(G):
        for up in nodes:
            lam = a - G.degree(up)
            M = [[A[i][j] - (lam if i == j else 0) for j in range(n)] for i in range(n)]
            if det_int(M) == 0:
                continue
            Nup = set(G[up])
            others = [v for v in nodes if v != up]
            alts = []
            for S in itertools.combinations(others, len(Nup)):
                S = set(S)
                if S == Nup:
                    continue
                K = G.copy()
                K.remove_edges_from([(up, y) for y in Nup])
                K.add_edges_from([(up, y) for y in S])
                if is2wl(K, a, b):
                    alts.append(K)
            if len(alts) > 1:
                return False
            if not alts:
                continue
            # does some card iso G-u -> G-u' fail to extend?
            Gup = G.subgraph(others)
            nonext = False
            for u in nodes:
                if G.degree(u) != G.degree(up):
                    continue
                Gu = G.subgraph([v for v in nodes if v != u])
                for m in GraphMatcher(Gu, Gup).isomorphisms_iter():
                    if {m[y] for y in G[u]} != Nup:
                        nonext = True
                        break
                if nonext:
                    break
            if nonext and not nx.is_isomorphic(alts[0], G):
                return False
    return True
