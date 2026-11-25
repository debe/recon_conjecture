"""Shared helpers for sketch t3 (algebraic / spectral synthesis). Evidence only, never a result.

Everything here is exact integer arithmetic (no floating point).
"""
import itertools
from collections import Counter
from fractions import Fraction

import networkx as nx


# ----------------------------------------------------------------------------- matrices

def adj(G, order=None):
    order = list(G.nodes()) if order is None else list(order)
    idx = {v: i for i, v in enumerate(order)}
    n = len(order)
    A = [[0] * n for _ in range(n)]
    for u, v in G.edges():
        if u in idx and v in idx:
            A[idx[u]][idx[v]] = A[idx[v]][idx[u]] = 1
    return A


def matvec(A, x):
    return [sum(a * b for a, b in zip(row, x)) for row in A]


def walk_vectors(A, seed=None, count=None):
    """[seed, A seed, A^2 seed, ...] (count vectors, default n)"""
    n = len(A)
    x = [1] * n if seed is None else list(seed)
    out = []
    for _ in range(n if count is None else count):
        out.append(x)
        x = matvec(A, x)
    return out


def rank(rows):
    """exact rank of an integer/rational matrix given as a list of rows"""
    M = [[Fraction(a) for a in r] for r in rows]
    r = 0
    ncols = len(M[0]) if M else 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        p = M[r][c]
        for i in range(r + 1, len(M)):
            if M[i][c] != 0:
                f = M[i][c] / p
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
        if r == len(M):
            break
    return r


def walk_rank(G, seeds=None):
    """rank of the walk matrix [1, A1, ..., A^(n-1) 1] (or of the multi-seed version)"""
    A = adj(G, sorted(G.nodes()))
    if seeds is None:
        return rank(walk_vectors(A))
    rows = []
    for s in seeds:
        rows.extend(walk_vectors(A, s))
    return rank(rows)


def charpoly(A):
    """coefficients c_0..c_n of det(xI - A) = sum c_k x^(n-k), by Faddeev-LeVerrier (exact)"""
    n = len(A)
    c = [Fraction(1)]
    M = [[Fraction(0)] * n for _ in range(n)]
    for k in range(1, n + 1):
        # M_k = A M_{k-1} + c_{k-1} I
        AM = [[sum(A[i][l] * M[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        M = [[AM[i][j] + (c[k - 1] if i == j else 0) for j in range(n)] for i in range(n)]
        AMk = [[sum(A[i][l] * M[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        c.append(-sum(AMk[i][i] for i in range(n)) / k)
    return tuple(c)


# ----------------------------------------------------------------------------- classes

def diam_le2(G):
    n = G.number_of_nodes()
    return all(len(nx.single_source_shortest_path_length(G, u, cutoff=2)) == n for u in G.nodes())


def in_Q(G):
    """both diameters <= 2 (second disjunct of the frozen class)"""
    return G.number_of_nodes() >= 2 and diam_le2(G) and diam_le2(nx.complement(G))


def star_at(G, v):
    N = set(G[v])
    return all(G.degree(x) != G.degree(y) + 1
               for x in N for y in G.nodes() if y != v and y not in N)


def forced_sets(G, v):
    """Forced sets of the card G - v, computed from the card alone.
    Fplus: endpoints of non-adjacent card pairs without a common card neighbour.
    Fminus: endpoints of adjacent card pairs without a common card non-neighbour."""
    C = G.copy()
    C.remove_node(v)
    nodes = list(C.nodes())
    full = set(nodes)
    Fp, Fm = set(), set()
    for x, y in itertools.combinations(nodes, 2):
        if C.has_edge(x, y):
            if (set(C[x]) | set(C[y]) | {x, y}) == full:
                Fm |= {x, y}
        else:
            if not (set(C[x]) & set(C[y])):
                Fp |= {x, y}
    return Fp, Fm


def star2_at(G, v):
    """(*2) at v: on every card-degree level L, either all of N(v) & L is forced in,
    or all of L - N(v) is forced out."""
    N = set(G[v])
    Fp, Fm = forced_sets(G, v)
    others = [w for w in G.nodes() if w != v]
    c = {w: G.degree(w) - (1 if w in N else 0) for w in others}
    for k in set(c.values()):
        L = {w for w in others if c[w] == k}
        if not ((L & N) <= Fp or (L - N) <= Fm):
            return False
    return True


def feasible_sets(G, v, use_Q=True, use_spec=False, use_tri=False):
    """All S (subsets of the card at v) other than N(v) that satisfy
    (a) the level counts of N(v);
    (b) [use_Q] re-attaching v to S gives a graph with both diameters <= 2;
    (c) [use_tri] the same number of edges inside S as inside N(v);
    (d) [use_spec] the one-card spectral constraints: for all k,
        1^T A_c^k 1_S = 1^T A_c^k 1_N and 1_S^T A_c^k 1_S = 1_N^T A_c^k 1_N."""
    N = set(G[v])
    others = sorted(w for w in G.nodes() if w != v)
    c = {w: G.degree(w) - (1 if w in N else 0) for w in others}
    prof = Counter(c[w] for w in N)
    levels = {}
    for w in others:
        levels.setdefault(c[w], []).append(w)
    base = G.copy()
    base.remove_node(v)
    Ac = adj(base, others)
    m = len(others)

    def spec(S):
        b = [1 if w in S else 0 for w in others]
        out = []
        x = b
        for _ in range(m):
            out.append((sum(x), sum(p * q for p, q in zip(x, b))))
            x = matvec(Ac, x)
        return tuple(out)

    specN = spec(N) if use_spec else None
    eN = sum(1 for a, b in itertools.combinations(sorted(N), 2) if G.has_edge(a, b))
    choices = [itertools.combinations(levels[k], prof.get(k, 0)) for k in sorted(levels)]
    out = []
    for parts in itertools.product(*choices):
        S = set(itertools.chain.from_iterable(parts))
        if S == N:
            continue
        if use_tri and sum(1 for a, b in itertools.combinations(sorted(S), 2)
                           if G.has_edge(a, b)) != eN:
            continue
        if use_spec and spec(S) != specN:
            continue
        if use_Q:
            H = base.copy()
            H.add_node(v)
            H.add_edges_from((v, s) for s in S)
            if not in_Q(H):
                continue
        out.append(S)
    return out


def card_orbit(G, v):
    """images of N(v) under the automorphisms of the card G - v"""
    from networkx.algorithms.isomorphism import GraphMatcher
    C = G.copy()
    C.remove_node(v)
    N = set(G[v])
    return {frozenset(a[x] for x in N) for a in GraphMatcher(C, C).isomorphisms_iter()}


def decided_at(G, v, use_spec=False):
    """every feasible S at v is the image of N(v) under an automorphism of the card"""
    S = feasible_sets(G, v, use_Q=True, use_spec=use_spec)
    if not S:
        return True
    orb = card_orbit(G, v)
    return all(frozenset(s) in orb for s in S)
