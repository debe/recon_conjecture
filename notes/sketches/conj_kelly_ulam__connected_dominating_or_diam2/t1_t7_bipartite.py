"""T7 on random triangle-free graphs with a dominating edge, n = 6..11. Evidence only.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t1_t7_bipartite.py

G: sides X (u first) and Y (v first), u joined to all of Y, v to all of X, the rest random.
For the card G - u, list every independent S with the level profile of Y = N(u).
Claim T7: S = Y, or S = (X - u) + Y0 with |Y - Y0| = |X| - 1 (the "balanced swap").
Also reported: how often the swap occurs, and whether the swapped graph is isomorphic
to G or at least hypomorphic to G (it must be isomorphic whenever it is hypomorphic,
n <= 13, McKay).
"""
import itertools, os, random, sys
from collections import Counter
import networkx as nx
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon, deck_key

rng = random.Random(7)
tested = swaps = swap_iso = swap_hypo_not_iso = 0
for trial in range(6000):
    n = rng.randint(6, 11)
    a = rng.randint(2, n - 2)
    X, Y = list(range(a)), list(range(a, n))
    u, v = X[0], Y[0]
    G = nx.Graph(); G.add_nodes_from(range(n))
    G.add_edges_from((u, y) for y in Y); G.add_edges_from((x, v) for x in X)
    p = rng.choice((0.15, 0.3, 0.5, 0.7))
    G.add_edges_from((x, y) for x in X[1:] for y in Y[1:] if rng.random() < p)
    Ys, Xs = set(Y), set(X)
    Y0 = {y for y in Y if G.degree(y) == 1}
    others = [w for w in G.nodes() if w != u]
    c = {w: G.degree(w) - (1 if w in Ys else 0) for w in others}
    prof = Counter(c[w] for w in Ys)
    tested += 1
    for S in itertools.combinations(others, len(Y)):
        Ss = set(S)
        if Ss == Ys or Counter(c[w] for w in Ss) != prof:
            continue
        if any(G.has_edge(x, y) for x, y in itertools.combinations(S, 2)):
            continue
        if not (Ss == (Xs - {u}) | Y0 and len(Ys - Y0) == len(Xs) - 1):
            print("T7 FAILS", sorted(G.edges()), sorted(Ss)); sys.exit(1)
        swaps += 1
        H = G.copy(); H.remove_node(u); H.add_node(u); H.add_edges_from((u, s) for s in Ss)
        if canon(H) == canon(G):
            swap_iso += 1
        elif deck_key(H) == deck_key(G):
            swap_hypo_not_iso += 1
print(f"T7 holds on {tested} graphs; balanced swaps: {swaps}, of which isomorphic to G: "
      f"{swap_iso}, hypomorphic but not isomorphic: {swap_hypo_not_iso}")

# An explicit n = 11 pair (found by exhaustive-sample search over 5 x 5 biadjacency matrices):
# G is triangle-free with a dominating edge; H is G with vertex 10 re-attached to the other
# side (the balanced swap). Same card at vertex 10, same degree sequence, both triangle-free,
# not isomorphic, and (as McKay's n <= 13 result demands) not hypomorphic.
G = nx.from_graph6_bytes(b"J?B}RBOW?N_"); H = nx.from_graph6_bytes(b"J?B}RBOWFo?")
Gu, Hu = G.copy(), H.copy(); Gu.remove_node(10); Hu.remove_node(10)
nodes = set(G.nodes())
dom = [(a, b) for a, b in G.edges() if nodes <= ({a, b} | set(G[a]) | set(G[b]))]
print("example n=11:",
      "G tri-free", sum(nx.triangles(G).values()) == 0,
      "| H tri-free", sum(nx.triangles(H).values()) == 0,
      "| G dominating edges", dom,
      "| same card at 10", canon(Gu) == canon(Hu),
      "| same degree sequence", sorted(d for _, d in G.degree()) == sorted(d for _, d in H.degree()),
      "| isomorphic", canon(G) == canon(H),
      "| hypomorphic", deck_key(G) == deck_key(H))
