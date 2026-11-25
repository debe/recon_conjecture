"""Bite of the class `one2` (some card G - v such that every one-vertex extension of it with the
same neighbour-degree data as G is isomorphic to G) on D2 and on all graphs. Evidence only.
Neighbour-degree data: multiset over x of (deg x, sorted degrees of the neighbours of x)."""
import itertools, os, sys, random
from collections import Counter
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'search'))
from small_graphs import all_graphs, canon, g6
from t2_lib import in_D2, sep_vertices


def inv2(G):
    d = dict(G.degree())
    return tuple(sorted((d[x], tuple(sorted(d[y] for y in G[x]))) for x in G.nodes()))


def one2(G):
    target = inv2(G)
    for v in G.nodes():
        C = G.copy(); C.remove_node(v)
        ok = True
        for S in itertools.combinations(list(C.nodes()), G.degree(v)):
            H = C.copy(); H.add_node(v); H.add_edges_from((v, s) for s in S)
            if inv2(H) == target and not nx.is_isomorphic(G, H):
                ok = False; break
        if ok:
            return True
    return False


def run(n, graphs, label):
    c = Counter(); ex = []; exall = []
    for G in graphs:
        o = one2(G); d2 = in_D2(G)
        c['all'] += 1; c['all_one2'] += o
        if not o and len(exall) < 4: exall.append(g6(G))
        if d2:
            c['D2'] += 1; c['D2_sep'] += bool(sep_vertices(G)); c['D2_one2'] += o
            if not o and len(ex) < 4: ex.append(g6(G))
    print(f"n={n} ({label}): " + ' '.join(f"{k}={c[k]}" for k in ('all', 'all_one2', 'D2', 'D2_sep', 'D2_one2')),
          'D2 not one2:', ex, 'any not one2:', exall, flush=True)


if __name__ == '__main__':
    for n in (3, 4, 5, 6, 7):
        run(n, all_graphs(n), 'exhaustive')
    rng = random.Random(5)
    for n, cnt in ((8, 500), (9, 300), (10, 150)):
        seen = {}
        for _ in range(cnt):
            G = nx.gnp_random_graph(n, 0.5, seed=rng.randrange(1 << 30))
            seen.setdefault(canon(G), G)
        run(n, seen.values(), f'G(n,1/2) sample of {cnt}')
