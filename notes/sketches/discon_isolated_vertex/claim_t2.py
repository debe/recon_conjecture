"""Claims behind sketch t2 (discon_isolated_vertex). Evidence only, never a result.

Run:  python3 tools/search/small_graphs.py counterexample \
          --claim notes/sketches/discon_isolated_vertex/claim_t2.py --n-min 3 --n-max 7
"""
import networkx as nx
from small_graphs import card, canon


def _isolated(G):
    return [v for v in G.nodes if G.degree(v) == 0]


def claim(G):
    """L1: a card has |E(G)| edges iff it is the card of an isolated vertex.
    L3 (self-pair form): any two cards at isolated vertices are isomorphic."""
    m = G.number_of_edges()
    for v in G.nodes:
        if (card(G, v).number_of_edges() == m) != (G.degree(v) == 0):
            return False
    iso = _isolated(G)
    return len({canon(card(G, v)) for v in iso}) <= 1


def claim_pair(G, H):
    """For a hypomorphic pair with n >= 3:
    L0: equal edge counts.
    L2: G has an isolated vertex iff H has one (the transfer step).
    L3: if v is isolated in G, w is isolated in H and G - v ~ H - w, then G ~ H.
    Conclusion: an isolated vertex in G forces G ~ H."""
    if G.number_of_edges() != H.number_of_edges():
        return False
    ig, ih = _isolated(G), _isolated(H)
    if bool(ig) != bool(ih):
        return False
    for v in ig:
        for w in ih:
            if canon(card(G, v)) == canon(card(H, w)) and canon(G) != canon(H):
                return False
    if ig and canon(G) != canon(H):
        return False
    return True


def _all_pairs_check(n_max=6):
    """Stronger than claim_pair (which only ever sees hypomorphic pairs, and those are
    isomorphic for n <= 7): for ALL pairs (G, H) with |E(G)| = |E(H)|, every isolated v of G
    and every w of H with G - v ~ H - w, check that w is isolated in H and G ~ H.
    This is exactly the pair of facts the Lean proof uses after kelly_edge_count."""
    import sys
    sys.path.insert(0, "tools/search")
    from small_graphs import all_graphs
    checked = 0
    for n in range(1, n_max + 1):
        gs = list(all_graphs(n))
        cards = {id(G): [canon(card(G, x)) for x in G.nodes] for G in gs}
        for G in gs:
            ig = _isolated(G)
            if not ig:
                continue
            for H in gs:
                if G.number_of_edges() != H.number_of_edges():
                    continue
                for v in ig:
                    for w in H.nodes:
                        if cards[id(G)][v] == cards[id(H)][w]:
                            checked += 1
                            if H.degree(w) != 0 or canon(G) != canon(H):
                                return ("WITNESS", n, sorted(G.edges), sorted(H.edges), v, w)
    return ("NO WITNESS", checked)


if __name__ == "__main__":
    print(_all_pairs_check())
