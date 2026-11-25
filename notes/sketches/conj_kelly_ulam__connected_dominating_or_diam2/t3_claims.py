"""Single-graph claims behind sketch t3. Evidence only, never a result.

  python3 tools/search/small_graphs.py counterexample \
      --claim notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t3_claims.py \
      --n-min 3 --n-max 6 --random 300 --random-n 7 8

Every test is an identity or implication about ONE labelled graph (plus, in X5/X6, every
re-attachment of one vertex). Reconstructibility itself is never tested: it holds for
n <= 13 (McKay), so such a test says nothing.

X1  partition expansion of the characteristic polynomial (lemma S2):
      det(xI - A) = sum over set partitions of V of prod g(G[S]),
      g(single) = x, g(S) = -(number of cyclic permutations of S along edges) for |S| >= 2.
X2  two-block inclusion-exclusion (lemma S0): for F1 = G[S0], F2 = G[V - S0],
      #{S : G[S] ~ F1 and G[V - S] ~ F2} = sum_t (-1)^t sum_{|T| = t} ind(F1, G-T) ind(F2, G-T).
X3  edge-subset expansion (lemma S1): C(m, j) = sum over partitions and splits of prod a_j,
    and  ham(G) = a_n(G) - sum_{k<n} u_k(G)  with u_k counted as (k-cycle, n-k other edges).
X4  walks from v out of four characteristic polynomials (lemma S4):
      with R_vv = phi(G-v)/phi(G) etc.,  (sum_k (A^k 1)_v x^-(k+1))^2 is the series
      (1 + 1^T R 1)(R_vv + Rbar_vv(-x-1)).
X5  one-card spectral constraints (lemma S5', Hong's step): if re-attaching v to S gives a
    graph with the characteristic polynomial of G whose complement has that of co-G, then
    S and N(v) have the same walk counts in the card (from the set, and set to set).
X6  forced sets (lemma D3): in a graph with both diameters <= 2, Fplus(v) is inside N(v)
    and Fminus(v) is disjoint from N[v]; and (*2) at v leaves no feasible S other than N(v).
"""
import itertools
import os
import sys
from fractions import Fraction
from math import comb

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import (adj, charpoly, feasible_sets, forced_sets, in_Q, matvec,  # noqa: E402
                    star2_at)

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon  # noqa: E402

FAIL = []


def _fail(tag):
    FAIL.append(tag)
    print("FAILED TEST:", tag, file=sys.stderr)
    return False


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for k in range(len(rest) + 1):
        for others in itertools.combinations(rest, k):
            block = (first,) + others
            remaining = [x for x in rest if x not in others]
            for p in set_partitions(remaining):
                yield [block] + p


def cyc_count(G, S):
    """number of cyclic permutations rho of S with (i, rho i) an edge for all i"""
    S = list(S)
    if len(S) == 1:
        return 0
    if len(S) == 2:
        return 1 if G.has_edge(S[0], S[1]) else 0
    first, rest = S[0], S[1:]
    total = 0
    for perm in itertools.permutations(rest):
        seq = (first,) + perm
        if all(G.has_edge(seq[i], seq[(i + 1) % len(seq)]) for i in range(len(seq))):
            total += 1
    return total


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pmul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def connected_edge_subsets(G, S):
    """a_j(G[S]) for all j: number of j-edge subsets connecting S"""
    S = list(S)
    edges = [e for e in G.subgraph(S).edges()]
    out = [0] * (len(edges) + 1)
    for j in range(len(S) - 1, len(edges) + 1):
        for F in itertools.combinations(edges, j):
            T = nx.Graph()
            T.add_nodes_from(S)
            T.add_edges_from(F)
            if nx.is_connected(T):
                out[j] += 1
    return out


def series_div(num, den, terms):
    """power series num/den in t (lists, den[0] != 0)"""
    out = []
    num = [Fraction(a) for a in num] + [Fraction(0)] * terms
    for k in range(terms):
        c = num[k] / den[0]
        out.append(c)
        for j, d in enumerate(den):
            if k + j < len(num):
                num[k + j] -= c * d
    return out


def series_mul(a, b, terms):
    out = [Fraction(0)] * terms
    for i, x in enumerate(a[:terms]):
        for j, y in enumerate(b[:terms - i]):
            out[i + j] += x * y
    return out


def resolvent_diag(cG, cGv, terms):
    """phi(G-v)/phi(G) as a series in t = 1/x:  sum_k (A^k)_vv t^(k+1)  ->  returns coefficients
    of t^1, t^2, ... shifted to start at t^0 (i.e. the list (A^k)_vv, k >= 0)."""
    # phi(G) = x^n sum c_k t^k ; phi(G-v) = x^(n-1) sum d_k t^k ; ratio = t * (sum d)/(sum c)
    return series_div(list(cGv), list(cG), terms)


def claim(G):
    n = G.number_of_nodes()
    if n < 3:
        return True
    nodes = sorted(G.nodes())
    A = adj(G, nodes)
    cG = charpoly(A)
    m = G.number_of_edges()

    # X1 (n <= 6: Bell(6) = 203 partitions)
    if n <= 6:
        total = [0]
        for p in set_partitions(nodes):
            term = [1]
            for block in p:
                g = [0, 1] if len(block) == 1 else [-cyc_count(G, block)]
                term = pmul(term, g)
            total = padd(total, term)
        # total is in ascending powers of x; charpoly gives c_k for x^(n-k)
        want = [cG[n - i] for i in range(n + 1)]
        total = total + [0] * (n + 1 - len(total))
        if [Fraction(a) for a in total] != list(want):
            return _fail("X1 partition expansion of charpoly")

    # X2 (one split per graph, n <= 6)
    if n <= 6:
        k = n // 2
        S0 = nodes[:k]
        c1 = canon(nx.convert_node_labels_to_integers(G.subgraph(S0)))
        c2 = canon(nx.convert_node_labels_to_integers(G.subgraph(nodes[k:])))

        def ind(c, size, avoid):
            pool = [w for w in nodes if w not in avoid]
            return sum(1 for W in itertools.combinations(pool, size)
                       if canon(nx.convert_node_labels_to_integers(G.subgraph(W))) == c)
        lhs = sum(1 for W in itertools.combinations(nodes, k)
                  if canon(nx.convert_node_labels_to_integers(G.subgraph(W))) == c1
                  and canon(nx.convert_node_labels_to_integers(
                      G.subgraph([w for w in nodes if w not in W]))) == c2)
        rhs = 0
        for t in range(0, n + 1):
            for T in itertools.combinations(nodes, t):
                rhs += (-1) ** t * ind(c1, k, T) * ind(c2, n - k, T)
        if lhs != rhs:
            return _fail("X2 two-block inclusion-exclusion")

    # X3 (n <= 6)
    if n <= 6:
        a_cache = {}

        def a(S):
            key = tuple(S)
            if key not in a_cache:
                a_cache[key] = connected_edge_subsets(G, S)
            return a_cache[key]
        gen = [0]
        for p in set_partitions(nodes):
            term = [1]
            for block in p:
                term = pmul(term, a(block))
            gen = padd(gen, term)
        gen = gen + [0] * (m + 1 - len(gen))
        if gen[:m + 1] != [comb(m, j) for j in range(m + 1)]:
            return _fail("X3 edge-subset expansion")
        aV = a(tuple(nodes))
        a_n = aV[n] if n < len(aV) else 0
        ham = cyc_count(G, nodes) // 2
        edges = list(G.edges())
        uk_total = 0
        for k in range(3, n):
            for W in itertools.combinations(nodes, k):
                first, rest = W[0], W[1:]
                for perm in itertools.permutations(rest):
                    if perm[0] > perm[-1]:
                        continue
                    seq = (first,) + perm
                    cyc = [frozenset((seq[i], seq[(i + 1) % k])) for i in range(k)]
                    if not all(G.has_edge(*tuple(e)) for e in cyc):
                        continue
                    restE = [e for e in edges if frozenset(e) not in cyc]
                    for F in itertools.combinations(restE, n - k):
                        T = nx.Graph()
                        T.add_nodes_from(nodes)
                        T.add_edges_from(F)
                        T.add_edges_from(tuple(e) for e in cyc)
                        if nx.is_connected(T):
                            uk_total += 1
        if ham != a_n - uk_total:
            return _fail("X3 hamiltonian cycles from unicyclic counts")

    # X4
    Gc = nx.complement(G)
    Ac = adj(Gc, nodes)
    cGc = charpoly(Ac)
    terms = n + 3
    # 1^T R 1 from phi(Gbar; y) = (-1)^n phi(G; x)(1 + 1^T R(x) 1) at x = -y-1 : test directly
    walks = []
    x = [1] * n
    for _ in range(terms):
        walks.append(x)
        x = matvec(A, x)
    for i, v in enumerate(nodes):
        Gv = G.copy()
        Gv.remove_node(v)
        rest = [w for w in nodes if w != v]
        cGv = charpoly(adj(Gv, rest))
        cGcv = charpoly(adj(nx.complement(Gv), rest))
        Rvv = resolvent_diag(cG, cGv, terms)          # (A^k)_vv
        Rbvv = resolvent_diag(cGc, cGcv, terms)       # (Abar^k)_vv
        # closed walks check
        Ak = [[1 if a == b else 0 for b in range(n)] for a in range(n)]
        for k in range(terms):
            if Rvv[k] != Ak[i][i]:
                return _fail("X4 closed walks from phi(G-v)/phi(G)")
            Ak = [[sum(Ak[a][l] * A[l][b] for l in range(n)) for b in range(n)] for a in range(n)]
        # Work with series in t = 1/x.  R_vv(x) = t * sum_k (A^k)_vv t^k.
        # Rbar_vv(y) at y = -x-1: 1/y = -t/(1+t).  Rbar_vv(y) = (1/y) sum_k (Abar^k)_vv (1/y)^k.
        inv_y = series_div([0, -1], [1, 1], terms)     # -t/(1+t)
        pw = [Fraction(1)] + [Fraction(0)] * (terms - 1)
        Rb = [Fraction(0)] * terms
        for k in range(terms):
            pw = series_mul(pw, inv_y, terms)          # (1/y)^(k+1)
            Rb = [p + Rbvv[k] * q for p, q in zip(Rb, pw)]
        Rv = [Fraction(0)] + [Rvv[k] for k in range(terms - 1)]     # t * sum
        tot = [Fraction(0)] + [Fraction(sum(walks[k])) for k in range(terms - 1)]  # 1^T R 1
        one_plus = [1 + tot[0]] + tot[1:]
        lhs = series_mul(one_plus, [p + q for p, q in zip(Rv, Rb)], terms)
        wv = [Fraction(0)] + [Fraction(walks[k][i]) for k in range(terms - 1)]      # e_v^T R 1
        rhs = series_mul(wv, wv, terms)
        if lhs != rhs:
            return _fail("X4 walks from v, squared")

    # X5 (n <= 7): every S with the two characteristic polynomials has the walk counts
    if n <= 7:
        for v in nodes:
            N = set(G[v])
            rest = [w for w in nodes if w != v]
            base = G.copy()
            base.remove_node(v)
            Acard = adj(base, rest)

            def spec(S):
                b = [1 if w in S else 0 for w in rest]
                out, x = [], b
                for _ in range(len(rest)):
                    out.append((sum(x), sum(p * q for p, q in zip(x, b))))
                    x = matvec(Acard, x)
                return out
            sN = spec(N)
            for S in itertools.combinations(rest, len(N)):
                Ss = set(S)
                if Ss == N:
                    continue
                H = base.copy()
                H.add_node(v)
                H.add_edges_from((v, s) for s in Ss)
                if charpoly(adj(H, nodes)) != cG:
                    continue
                if charpoly(adj(nx.complement(H), nodes)) != cGc:
                    continue
                if spec(Ss) != sN:
                    return _fail("X5 one-card spectral constraints")

    # X6
    if in_Q(G):
        for v in nodes:
            N = set(G[v])
            Fp, Fm = forced_sets(G, v)
            if not Fp <= N or (Fm & (N | {v})):
                return _fail("X6 forced sets")
            if n <= 8 and star2_at(G, v) and feasible_sets(G, v, use_Q=True):
                return _fail("X6 (*2) leaves a second feasible set")
    return True
