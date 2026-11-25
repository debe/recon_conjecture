"""Variant W': some pair {u,v}, S = V - {u,v}, with (i) G[S] not isomorphic to G[T] for any other
(n-2)-set T and (ii) every automorphism of G[S] fixes N(u) & S setwise (or the same for v).
W is the special case where G[S] is asymmetric. Evidence only: how much W' adds on D2."""
import itertools, os, sys, random
from collections import Counter
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'search'))
from small_graphs import all_graphs, canon, g6
from t2_lib import in_D2, sep_vertices


def in_Wp(G):
    subs = {}
    for u, v in itertools.combinations(G.nodes(), 2):
        K = G.copy(); K.remove_nodes_from([u, v])
        subs[(u, v)] = (canon(K), K)
    cnt = Counter(c for c, _ in subs.values())
    for (u, v), (c, K) in subs.items():
        if cnt[c] != 1:
            continue
        autos = list(GraphMatcher(K, K).isomorphisms_iter())
        for z in (u, v):
            Nz = set(G[z]) & set(K.nodes())
            if all({a[x] for x in Nz} == Nz for a in autos):
                return True
    return False


def run(n, graphs, label):
    c = Counter(); ex = []
    for G in graphs:
        if not in_D2(G):
            continue
        sep = bool(sep_vertices(G)); wp = in_Wp(G)
        c['D2'] += 1; c['sep'] += sep; c['Wp'] += wp
        if not sep and not wp:
            c['res'] += 1
            if len(ex) < 4: ex.append(g6(G))
    print(f"n={n} ({label}): " + ' '.join(f"{k}={c[k]}" for k in ('D2', 'sep', 'Wp', 'res')), ex, flush=True)


if __name__ == '__main__':
    for n in (5, 6, 7):
        run(n, all_graphs(n), 'exhaustive')
    rng = random.Random(11)
    for n, cnt in ((8, 600), (9, 400), (10, 300)):
        seen = {}
        for _ in range(cnt):
            G = nx.gnp_random_graph(n, 0.5, seed=rng.randrange(1 << 30))
            if in_D2(G):
                seen.setdefault(canon(G), G)
        run(n, seen.values(), f'G(n,1/2) sample of {cnt}')
