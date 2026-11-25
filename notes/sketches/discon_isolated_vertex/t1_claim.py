"""Small-graph tests for sketch t1 (degree route) of discon_isolated_vertex.

Evidence only. Run:
  python3 tools/search/small_graphs.py counterexample \
      --claim notes/sketches/discon_isolated_vertex/t1_claim.py --n-min 3 --n-max 7

claim(G) tests two single-graph facts:
  D  deg v = e(G) - e(G - v) for every vertex v            (kelly_card_edges_add_degree)
  X  extension: if v is isolated in G, then every graph H on the same number of vertices
     that has an isolated vertex w with H - w isomorphic to G - v is isomorphic to G.
claim_pair(G, H) tests the pointwise degree identity on a same-deck pair:
  P  whenever a card G - x is isomorphic to a card H - y, deg_G x = deg_H y.
     (Stronger than what the sketch uses, which only needs y = sigma x.)

Negative control (expected to produce a WITNESS): --n-min 2 --n-max 2, where P fails for
G = 2K1, H = K2. That is the n = 2 anchor, and it shows where 3 <= n enters.
"""
import sys
sys.path.insert(0, "/home/db/repositories/recon_conjecture/tools/search")
from small_graphs import all_graphs, card, canon

_index = {}


def _isolated_index(n):
    """canon(H - w) -> set of canon(H), over all H on n vertices and isolated w."""
    if n not in _index:
        idx = {}
        for H in all_graphs(n):
            for w in H.nodes():
                if H.degree(w) == 0:
                    idx.setdefault(canon(card(H, w)), set()).add(canon(H))
        _index[n] = idx
    return _index[n]


def claim(G):
    n = G.number_of_nodes()
    m = G.number_of_edges()
    for v in G.nodes():
        if G.degree(v) != m - card(G, v).number_of_edges():        # D
            return False
    idx = _isolated_index(n)
    cg = canon(G)
    for v in G.nodes():
        if G.degree(v) == 0:
            if idx.get(canon(card(G, v)), set()) != {cg}:           # X
                return False
    return True


def claim_pair(G, H):
    cg = {x: canon(card(G, x)) for x in G.nodes()}
    ch = {y: canon(card(H, y)) for y in H.nodes()}
    for x in G.nodes():
        for y in H.nodes():
            if cg[x] == ch[y] and G.degree(x) != H.degree(y):       # P
                return False
    return True
