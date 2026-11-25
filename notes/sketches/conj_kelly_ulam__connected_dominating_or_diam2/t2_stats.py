"""How much each proposed child bites on the D2 class. Evidence only, never a result.

  python3 t2_stats.py            # exhaustive n = 5..7, random n = 8, 9, 10

Columns:
  D2     graphs with every pair at distance <= 2 in G and in the complement
  reg    regular
  sep    some vertex v with no neighbour u / non-neighbour w having deg w + 1 = deg u
  one    some card G - v such that every one-vertex extension with the degree sequence of G is
         isomorphic to G  (semantic closure of sep)
  W      some pair {u, v} with G - {u, v} asymmetric and not isomorphic to any other
         (n-2)-vertex induced subgraph of G
  res    D2 and not sep and not W          (residual of the proposed reduction)
  res1   D2 and not one and not W          (residual if the semantic class is used instead)
"""
import itertools, os, sys
from collections import Counter
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'search'))
from small_graphs import all_graphs, random_graphs, canon, g6
from t2_lib import in_D2, is_regular, sep_vertices, degseq


def one_card(G):
    deg = dict(G.degree())
    target = degseq(G)
    for v in G.nodes():
        C = G.copy(); C.remove_node(v)
        ok = True
        for S in itertools.combinations(list(C.nodes()), deg[v]):
            H = C.copy(); H.add_node(v); H.add_edges_from((v, s) for s in S)
            if degseq(H) == target and not nx.is_isomorphic(G, H):
                ok = False
                break
        if ok:
            return True
    return False


def asymmetric(K):
    it = GraphMatcher(K, K).isomorphisms_iter()
    next(it)
    return next(it, None) is None


def in_W(G):
    n = G.number_of_nodes()
    if n < 8:
        return False  # no asymmetric graph on 2..5 vertices
    subs = {}
    for u, v in itertools.combinations(G.nodes(), 2):
        K = G.copy(); K.remove_nodes_from([u, v])
        subs[(u, v)] = (canon(K), K)
    cnt = Counter(c for c, _ in subs.values())
    return any(cnt[c] == 1 and asymmetric(K) for c, K in subs.values())


def row(n, graphs, label):
    c = Counter()
    smallest = []
    for G in graphs:
        if not in_D2(G):
            continue
        c['D2'] += 1
        reg = is_regular(G); sep = bool(sep_vertices(G)); w = in_W(G)
        one = sep or (n <= 9 and one_card(G))
        c['reg'] += reg; c['sep'] += sep; c['one'] += one; c['W'] += w
        if not sep and not w:
            c['res'] += 1
            if len(smallest) < 3:
                smallest.append(g6(G))
        if not one and not w:
            c['res1'] += 1
    print(f"n={n} ({label}): " + ' '.join(f"{k}={c[k]}" for k in ('D2', 'reg', 'sep', 'one', 'W', 'res', 'res1')),
          'examples of res:', smallest, flush=True)


if __name__ == '__main__':
    for n in (5, 6, 7):
        gs = all_graphs(n)
        print(f"n={n}: {len(gs)} graphs")
        row(n, gs, 'exhaustive')
    for n, cnt in ((8, 1500), (9, 600), (10, 300)):
        seen = {}
        for G in random_graphs(n, cnt, seed=7):
            seen.setdefault(canon(G), G)
        row(n, seen.values(), f'random sample, {len(seen)} distinct' + (', one not computed' if n > 9 else ''))
