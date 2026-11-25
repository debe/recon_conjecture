"""Red-team screen for conj_kelly_ulam__connected_dominating_or_diam2.

Lean class: fun n G => G.Connected ∧ Gᶜ.Connected ∧
  ((∃ u v, G.Adj u v ∧ ∀ x, x = u ∨ x = v ∨ G.Adj x u ∨ G.Adj x v) ∨
   ∀ u v, G.edist u v ≤ 2 ∧ Gᶜ.edist u v ≤ 2)
ClassReconstructible: ∀ n ≥ 3, ∀ G in class, ∀ H, Hypomorphic G H → Nonempty (G ≃g H).

Encoding: exact. edist u u = 0 ≤ 2; edist = ⊤ for disconnected pairs, which the
shortest-path dictionary represents by absence (treated as > 2).
"""
import networkx as nx


def dominating_edge(G):
    nodes = set(G.nodes())
    for u, v in G.edges():
        if nodes <= ({u, v} | set(G[u]) | set(G[v])):
            return True
    return False


def diam_le2(G):
    d = dict(nx.all_pairs_shortest_path_length(G, cutoff=2))
    n = G.number_of_nodes()
    return all(len(d[u]) == n for u in G.nodes())


def in_class(G):
    Gc = nx.complement(G)
    if not (nx.is_connected(G) and nx.is_connected(Gc)):
        return False
    return dominating_edge(G) or (diam_le2(G) and diam_le2(Gc))


def claim_pair(G, H):
    if not in_class(G):
        return True
    return nx.is_isomorphic(G, H)
