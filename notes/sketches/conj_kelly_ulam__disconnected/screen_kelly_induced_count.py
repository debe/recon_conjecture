"""Screen: conj_kelly_ulam__disconnected__kelly_induced_count.

Lean: ∀ n, ∀ G H : SimpleGraph (Fin n), Hypomorphic G H → ∀ k < n, ∀ F : SimpleGraph (Fin k),
  #{S : Finset (Fin n) | G[S] ≃g F} = #{S | H[S] ≃g F}

Encoding: claim_pair on every hypomorphic pair compares, for each k < n, the multiset of
isomorphism classes of k-vertex induced subgraphs. Run with --n-min 0 since the Lean
statement has no lower bound on n. Fidelity: exact for the tested n (hypomorphic = equal deck
multiset; ncard over finsets = count of k-subsets with that induced iso class).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _screen_common import induced_signature


def claim_pair(G, H):
    return induced_signature(G) == induced_signature(H)
