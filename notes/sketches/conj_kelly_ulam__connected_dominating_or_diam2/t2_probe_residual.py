"""Probe the residual examples: would stronger one-card invariants determine them?
inv1 = degree sequence; inv2 = multiset of (deg x, sorted degrees of neighbours of x);
inv3 = inv2 plus number of triangles and induced-P3 through each vertex (all recognizable
per deleted vertex, literature; UNVERIFIED here). Evidence only."""
import itertools, sys, os
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from t2_lib import degseq, in_D2

def inv2(G):
    d = dict(G.degree())
    return tuple(sorted((d[x], tuple(sorted(d[y] for y in G[x]))) for x in G.nodes()))

def determined(G, inv):
    target = inv(G); good = []
    for v in G.nodes():
        C = G.copy(); C.remove_node(v)
        ok = True
        for S in itertools.combinations(list(C.nodes()), G.degree(v)):
            H = C.copy(); H.add_node(v); H.add_edges_from((v, s) for s in S)
            if inv(H) == target and not nx.is_isomorphic(G, H):
                ok = False; break
        if ok: good.append(v)
    return good

for s in ['FdZKO', 'Fhff?', 'GekjIo', 'GGtofK', 'G\\Qgpg', 'HT\\]FCn', 'HVIMHNK', 'IFWPMTlWW']:
    G = nx.from_graph6_bytes(s.encode())
    print(s, 'D2' if in_D2(G) else 'notD2', 'degs', degseq(G), 'one-card by degseq:', determined(G, degseq), 'by inv2:', determined(G, inv2))
