"""Screen: conj_kelly_ulam__disconnected__component_counts_of_induced_counts.

Lean: ∀ n, ∀ G H : SimpleGraph (Fin n), ¬G.Connected → ¬H.Connected →
  (∀ k < n, ∀ F on Fin k, induced counts of F agree) →
  ∀ k, ∀ F on Fin k, F.Connected → #{components ≃ F} agree.

Encoding: claim(G) enumerates EVERY H on the same n (not only hypomorphic ones), keeps those
that are Lean-disconnected (n = 0 counts as disconnected: Connected needs Nonempty) with the
same k<n induced signature, and checks the component multisets agree. Run with --n-min 0.
Fidelity: exact for the tested n.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _screen_common import lean_connected, graphs_with_sigs, induced_signature, component_signature


def claim(G):
    if lean_connected(G):
        return True
    n = G.number_of_nodes()
    sg, cg = induced_signature(G), component_signature(G)
    for H, sh, ch in graphs_with_sigs(n):
        if lean_connected(H) or sh != sg:
            continue
        if ch != cg:
            return False
    return True
