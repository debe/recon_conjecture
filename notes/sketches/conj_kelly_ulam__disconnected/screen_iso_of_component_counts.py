"""Screen: conj_kelly_ulam__disconnected__iso_of_component_counts.

Lean: ∀ n, ∀ G H : SimpleGraph (Fin n),
  (∀ k, ∀ F on Fin k, F.Connected → #{components of G ≃ F} = #{components of H ≃ F}) →
  Nonempty (G ≃g H)

Encoding: claim(G) enumerates every H on the same n; if the multisets of component
isomorphism classes agree (equivalent to the hypothesis, since every component is connected
and nonempty), H must be isomorphic to G. Run with --n-min 0. Fidelity: exact for tested n.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from _screen_common import graphs_with_sigs, component_signature


def claim(G):
    n = G.number_of_nodes()
    cg = component_signature(G)
    for H, _, ch in graphs_with_sigs(n):
        if ch == cg and not nx.is_isomorphic(G, H):
            return False
    return True
