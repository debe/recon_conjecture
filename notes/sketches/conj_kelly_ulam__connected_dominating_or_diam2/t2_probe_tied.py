"""Tied version of one2 (as in child D): the ambiguous H must match the neighbour-degree data along
a bijection that sends v to the vertex whose card is shared. Checks the five n = 8 graphs of the
dominating-edge branch that fail the untied test. Evidence only."""
import itertools, os, sys
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from t2_stats_one2 import inv2


def tied_good_vertices(G):
    d = dict(G.degree()); target = inv2(G); good = []
    for v in G.nodes():
        nds_v = tuple(sorted(d[y] for y in G[v]))
        C = G.copy(); C.remove_node(v)
        ok = True
        for S in itertools.combinations(list(C.nodes()), d[v]):
            H = C.copy(); H.add_node(v); H.add_edges_from((v, s) for s in S)
            dh = dict(H.degree())
            if inv2(H) == target and tuple(sorted(dh[y] for y in H[v])) == nds_v \
                    and not nx.is_isomorphic(G, H):
                ok = False; break
        if ok:
            good.append(v)
    return good


if __name__ == '__main__':
    for s in ['GCpdag', 'GIdc\\?', 'G\\DIKC', 'GuozjS', 'Gv`ip{']:
        G = nx.from_graph6_bytes(s.encode())
        print(s, 'vertices where the tied one-card test succeeds:', tied_good_vertices(G))
