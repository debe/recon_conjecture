"""Screen: conj_kelly_ulam__disconnected__connected_recognizable.

Lean: Recon.Recognizable (fun n G => G.Connected)
  = ∀ n, 3 ≤ n → ∀ G H : SimpleGraph (Fin n), Hypomorphic G H → (G.Connected ↔ H.Connected)

Encoding: claim_pair runs on every pair with equal deck (= Recon.Hypomorphic for finite
graphs on the same vertex count). Run with the default --n-min 3, matching `3 ≤ n`.
Fidelity: exact for the tested n. (At n = 2 it would fail, K2 vs 2K1, but Recognizable
excludes n = 2.)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _screen_common import lean_connected


def claim_pair(G, H):
    return lean_connected(G) == lean_connected(H)
