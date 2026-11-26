"""Are the remainder members found by the hunts prime (no module M with 1 < |M| < n)?
Evidence only; decides whether modular / P4 carving (attack option 7) can bite.

  python3 .../t3_check_prime.py <graph6> [<graph6> ...]
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import from_g6  # noqa: E402


def min_module(G, a, b):
    M = {a, b}
    changed = True
    while changed:
        changed = False
        for x in G:
            if x in M:
                continue
            nb = [G.has_edge(x, m) for m in M]
            if any(nb) and not all(nb):
                M.add(x)
                changed = True
    return M


def prime(G):
    n = G.number_of_nodes()
    return all(len(min_module(G, a, b)) == n for a, b in itertools.combinations(G, 2))


if __name__ == "__main__":
    res = [(s, prime(from_g6(s))) for s in sys.argv[1:]]
    print("graphs:", len(res), "prime:", sum(p for _, p in res),
          "not prime:", [s for s, p in res if not p])
