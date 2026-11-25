"""Consistency check for the "what breaks" section of sketch t1. Evidence only.

Question: the degree-level lemma (*) looks like pure counting, so why does it not also
reconstruct tournaments (scores instead of degrees)? Stockmeyer's tournaments B_k, C_k
(J. Graph Theory 1 (1977) 19-25; construction as recalled, UNVERIFIED against the paper, but
the script checks hypomorphic + non-isomorphic directly) are the test.

Tournament analogue of (*) at v: no in-neighbour x of v and out-neighbour y of v with
score(x) - 1 = score(y)   (score = out-degree; x beats v, so deleting v lowers score(x) by 1).

Finding: for k = 2 (n = 5) the analogue of (*) HOLDS at two vertices of C_2, although B_2 and
C_2 are hypomorphic and not isomorphic. The step of the proof that fails is
"the deleted vertex has the same degree on both sides": for graphs
deg v = |E(G)| - |E(G - v)| is read off the card; a tournament card always has C(n-1, 2) arcs,
and the matched vertices have different scores (printed below).
"""
import networkx as nx
from networkx.algorithms.isomorphism import DiGraphMatcher


def odd(x):
    while x % 2 == 0:
        x //= 2
    return x


def stockmeyer(k, variant):
    m = 2 ** k
    T = nx.DiGraph()
    T.add_nodes_from(range(0, m + 1))
    for i in range(1, m + 1):
        for j in range(1, m + 1):
            if i != j and odd(j - i) % 4 == 1:
                T.add_edge(i, j)
    for j in range(1, m + 1):
        zero_wins = (j % 2 == 1) if variant == "B" else (j % 2 == 0)
        T.add_edge(0, j) if zero_wins else T.add_edge(j, 0)
    return T


def iso(A, B):
    return DiGraphMatcher(A, B).is_isomorphic()


def hypomorphic(A, B):
    ca = [A.subgraph([w for w in A if w != v]) for v in A]
    cb = [B.subgraph([w for w in B if w != v]) for v in B]
    used = set()
    for x in ca:
        for i, y in enumerate(cb):
            if i not in used and iso(x, y):
                used.add(i)
                break
        else:
            return False
    return True


def star_at(T, v):
    ins, outs = set(T.predecessors(v)), set(T.successors(v))
    return all(T.out_degree(x) - 1 != T.out_degree(y) for x in ins for y in outs)


for k in (2, 3):
    B, C = stockmeyer(k, "B"), stockmeyer(k, "C")
    print(f"k={k} n={2**k+1}: hypomorphic {hypomorphic(B, C)}, isomorphic {iso(B, C)}, "
          f"same scores {sorted(d for _, d in B.out_degree()) == sorted(d for _, d in C.out_degree())}, "
          f"(*) holds at some vertex of B: {any(star_at(B, v) for v in B)}, "
          f"of C: {any(star_at(C, v) for v in C)}")

# Why (*) at a vertex of C_2 does not contradict the lemma: the lemma also needs the score of
# the deleted vertex to be the same on both sides. For graphs that is automatic
# (deg v = |E(G)| - |E(G - v)|, checked steps kelly_edge_count + kelly_card_edges_add_degree);
# for tournaments every card has the same number of arcs, and the scores differ:
B, C = stockmeyer(2, "B"), stockmeyer(2, "C")
for v in C:
    if star_at(C, v):
        cv = C.subgraph([w for w in C if w != v])
        partners = [w for w in B if iso(cv, B.subgraph([x for x in B if x != w]))]
        print(f"C_2 vertex {v}: (*) holds, score {C.out_degree(v)}; B_2 vertices with an "
              f"isomorphic card: {[(w, B.out_degree(w)) for w in partners]} (vertex, score)")
