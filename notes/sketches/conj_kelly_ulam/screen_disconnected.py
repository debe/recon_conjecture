"""Red-team screen for conj_kelly_ulam__disconnected.

Lean: Recon.ClassReconstructible (fun n G => ¬ G.Connected)
  = ∀ n ≥ 3, ∀ G : SimpleGraph (Fin n), ¬ G.Connected →
      ∀ H, Hypomorphic G H → Nonempty (G ≃g H)

Encoding: claim_pair(G, H) is called by the search tool on every pair with equal deck
(multiset of canonical cards), which is exactly Recon.Hypomorphic for finite graphs on the
same vertex count. Fidelity: exact for n >= 3 (tool default --n-min 3). Mathlib
`Connected` requires Nonempty; n >= 3 so this coincides with nx.is_connected.
"""
import networkx as nx


def in_class(G):
    return not nx.is_connected(G)


def claim_pair(G, H):
    if not in_class(G):
        return True
    return nx.is_isomorphic(G, H)
