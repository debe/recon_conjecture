#!/usr/bin/env python3
"""Small-graph laboratory: decks, hypomorphism and counterexample search.

Evidence only, never a result. A witness found here must be turned into a Lean proof of the
negated twin (`gate.py check <id>_neg ...`) before it counts.

Exhaustive for n <= 7 (networkx graph atlas) and, with nauty installed, n <= 10 (geng); random
sampling above that.

  python3 tools/search/small_graphs.py verify-recon --n-max 7
      sanity check of this tool: every deck class for n >= 3 has one graph
  python3 tools/search/small_graphs.py deck "<graph6>"
  python3 tools/search/small_graphs.py counterexample --claim notes/sketches/<id>/claim.py \
          [--n-min 3] [--n-max 7] [--random 2000 --random-n 8 9 10]
      The claim file defines one or both of
        def claim(G) -> bool                 # must hold for every graph G
        def claim_pair(G, H) -> bool         # must hold for every hypomorphic pair (G, H)
      (G, H are networkx.Graph objects with nodes 0..n-1.)
  python3 tools/search/small_graphs.py lean "<graph6>"
      print the graph as a Lean `SimpleGraph (Fin n)` term with decidable adjacency

As a library:  from small_graphs import all_graphs, card, deck_key, hypomorphic, canon
"""
from __future__ import annotations

import argparse
import importlib.util
import itertools
import random
import shutil
import subprocess
import sys
from collections import defaultdict
from functools import lru_cache

import networkx as nx


# --------------------------------------------------------------------------- canonical forms

def _refine(adj: list[frozenset[int]], cells: list[list[int]]) -> list[list[int]]:
    """Colour refinement of an ordered partition. Cells are split by (own cell, sorted counts
    of neighbours per cell) and ordered by that signature, so the result is isomorphism
    invariant: it depends only on the graph and the input partition, not on vertex names."""
    while True:
        where = {v: i for i, c in enumerate(cells) for v in c}
        out: list[list[int]] = []
        for i, c in enumerate(cells):
            if len(c) == 1:
                out.append(c)
                continue
            groups: dict[tuple, list[int]] = defaultdict(list)
            for v in c:
                counts: dict[int, int] = defaultdict(int)
                for u in adj[v]:
                    counts[where[u]] += 1
                groups[tuple(sorted(counts.items()))].append(v)
            out.extend(groups[k] for k in sorted(groups))
        if len(out) == len(cells):
            return out
        cells = out


def _leaves(adj: list[frozenset[int]], cells: list[list[int]]):
    """Discrete partitions reachable by individualise-and-refine (a generator: no lists of
    permutations are ever materialised)."""
    cells = _refine(adj, cells)
    target = min((i for i, c in enumerate(cells) if len(c) > 1),
                 key=lambda i: (len(cells[i]), i), default=None)
    if target is None:
        yield [c[0] for c in cells]
        return
    cell = cells[target]
    # Twin pruning: if all vertices of the cell have the same neighbourhood outside each
    # other, swapping any two is an automorphism that fixes every cell, so all branches
    # give the same leaves up to that swap: one branch suffices (K_n, K_{a,b}, empty graphs).
    first = cell[0]
    twins = all(adj[v] - {first} == adj[first] - {v} for v in cell[1:])
    for v in (cell[:1] if twins else cell):
        rest = [u for u in cells[target] if u != v]
        yield from _leaves(adj, cells[:target] + [[v], rest] + cells[target + 1:])


def canon(G: nx.Graph) -> tuple:
    """Exact canonical form: the least edge list over the leaves of the individualise-and-
    refine search tree (the branching cell is chosen invariantly, so isomorphic graphs give
    the same set of leaves up to relabelling, hence the same minimum)."""
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [frozenset(idx[u] for u in G[v]) for v in nodes]
    n = len(nodes)
    edges = [(idx[a], idx[b]) for a, b in G.edges()]
    best = None
    for order in _leaves(adj, [list(range(n))] if n else []):
        pos = {v: i for i, v in enumerate(order)}
        b = tuple(sorted((min(pos[a], pos[b]), max(pos[a], pos[b])) for a, b in edges))
        if best is None or b < best:
            best = b
    return (n, best or ())


def card(G: nx.Graph, v) -> nx.Graph:
    H = G.copy()
    H.remove_node(v)
    return nx.convert_node_labels_to_integers(H)


def deck_key(G: nx.Graph) -> tuple:
    """The deck as a sorted tuple of canonical cards (a multiset)."""
    return tuple(sorted(canon(card(G, v)) for v in G.nodes()))


def hypomorphic(G: nx.Graph, H: nx.Graph) -> bool:
    return G.number_of_nodes() == H.number_of_nodes() and deck_key(G) == deck_key(H)


GENG = shutil.which("geng") or shutil.which("nauty-geng")


def geng(n: int):
    """Stream all graphs on n vertices up to isomorphism from nauty's geng (graph6 lines)."""
    if not GENG:
        raise ValueError(f"exhaustive n={n} needs nauty's geng (apt install nauty); "
                         "use random_graphs instead")
    with subprocess.Popen([GENG, "-q", str(n)], stdout=subprocess.PIPE) as p:
        assert p.stdout is not None
        for line in p.stdout:
            yield nx.from_graph6_bytes(line.rstrip(b"\n"))


@lru_cache(maxsize=None)
def _atlas(n: int) -> tuple[nx.Graph, ...]:
    return tuple(nx.convert_node_labels_to_integers(G) for G in nx.graph_atlas_g()
                 if G.number_of_nodes() == n)


def all_graphs(n: int):
    """All graphs on n vertices up to isomorphism: the networkx atlas for n <= 7 (cached),
    nauty's geng above that (streamed: n=9 has 274668 graphs, n=10 about 12 million)."""
    if n <= 7:
        return _atlas(n)
    return geng(n)


def random_graphs(n: int, count: int, seed: int = 0):
    rng = random.Random(seed)
    for _ in range(count):
        p = rng.choice((0.2, 0.35, 0.5, 0.65, 0.8))
        yield nx.gnp_random_graph(n, p, seed=rng.randrange(1 << 30))


# --------------------------------------------------------------------------- output helpers

def g6(G: nx.Graph) -> str:
    return nx.to_graph6_bytes(G, header=False).decode().strip()


def from_g6(s: str) -> nx.Graph:
    return nx.from_graph6_bytes(s.encode())


def lean_term(G: nx.Graph) -> str:
    n = G.number_of_nodes()
    edges = sorted((min(a, b), max(a, b)) for a, b in G.edges())
    lst = ", ".join(f"({a}, {b})" for a, b in edges)
    return (f"(SimpleGraph.fromRel (fun a b : Fin {n} => "
            f"((a.val, b.val) ∈ ([{lst}] : List (ℕ × ℕ))) : SimpleGraph (Fin {n}))")


def describe(G: nx.Graph) -> str:
    return f"n={G.number_of_nodes()} m={G.number_of_edges()} graph6={g6(G)} edges={sorted(G.edges())}"


# --------------------------------------------------------------------------- commands

def cmd_verify(a) -> int:
    bad = 0
    for n in range(a.n_min, a.n_max + 1):
        classes = defaultdict(list)
        count = 0
        for G in all_graphs(n):
            classes[deck_key(G)].append(G)
            count += 1
        multi = [gs for gs in classes.values() if len(gs) > 1]
        print(f"n={n}: {count} graphs, {len(classes)} decks, "
              f"{len(multi)} decks shared by >1 graph")
        for gs in multi:
            print("   shared deck:", " | ".join(describe(G) for G in gs))
            bad += n >= 3
    return 1 if bad else 0


def cmd_deck(a) -> int:
    G = from_g6(a.graph6)
    print(describe(G))
    for v in G.nodes():
        print(f"  card -{v}: {describe(card(G, v))}")
    return 0


def load_claim(path: str):
    spec = importlib.util.spec_from_file_location("claim_module", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return getattr(mod, "claim", None), getattr(mod, "claim_pair", None)


def cmd_counterexample(a) -> int:
    claim, claim_pair = load_claim(a.claim)
    if not claim and not claim_pair:
        print("claim file defines neither claim(G) nor claim_pair(G, H)")
        return 2
    checked = 0
    top = min(a.n_max, 10 if GENG else 7)
    if top < a.n_max:
        print(f"note: exhaustive search stops at n={top} (install nauty for geng up to n=10)")
    for n in range(a.n_min, top + 1):
        classes = defaultdict(list)
        for G in all_graphs(n):
            checked += 1
            if claim and not claim(G):
                print(f"WITNESS claim fails: {describe(G)}\nLean: {lean_term(G)}")
                return 0
            if claim_pair:
                classes[deck_key(G)].append(G)
        if claim_pair:
            for cls in classes.values():
                for G, H in itertools.product(cls, repeat=2):
                    checked += 1
                    if not claim_pair(G, H):
                        print(f"WITNESS claim_pair fails:\n  G: {describe(G)}\n  H: {describe(H)}"
                              f"\nLean G: {lean_term(G)}\nLean H: {lean_term(H)}")
                        return 0
    for n in a.random_n or []:
        for G in random_graphs(n, a.random, seed=n):
            checked += 1
            if claim and not claim(G):
                print(f"WITNESS claim fails (random): {describe(G)}\nLean: {lean_term(G)}")
                return 0
            if claim_pair and not claim_pair(G, G):
                print(f"WITNESS claim_pair(G, G) fails (random): {describe(G)}")
                return 0
    print(f"NO WITNESS after {checked} checks "
          f"(exhaustive n={a.n_min}..{top}, random n={a.random_n or []})")
    return 1


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("verify-recon"); p.add_argument("--n-min", type=int, default=2)
    p.add_argument("--n-max", type=int, default=6); p.set_defaults(fn=cmd_verify)
    p = sub.add_parser("deck"); p.add_argument("graph6"); p.set_defaults(fn=cmd_deck)
    p = sub.add_parser("counterexample"); p.add_argument("--claim", required=True)
    p.add_argument("--n-min", type=int, default=3); p.add_argument("--n-max", type=int, default=7)
    p.add_argument("--random", type=int, default=500)
    p.add_argument("--random-n", type=int, nargs="*")
    p.set_defaults(fn=cmd_counterexample)
    p = sub.add_parser("lean"); p.add_argument("graph6")
    p.set_defaults(fn=lambda a: print(lean_term(from_g6(a.graph6))) or 0)
    a = ap.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
