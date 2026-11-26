"""Hunt for graphs outside C3 in families with much pseudo-similarity. Evidence only.
  python3 t2_hunt_misc.py trees 9 11 | prod | kneser | random 9 200
"""
import itertools
import random
import sys
from collections import Counter

import networkx as nx

from t2_lib import *


def report(name, G, c, out):
    G = nx.convert_node_labels_to_integers(G)
    C = Census(G)
    tw = triple_census_w(G, C)
    c3 = in_triple_class_w(G, C, "K", tw) is not None
    c2 = in_pair_class_w(G, C, "K") is not None
    c["G"] += 1
    c["C3"] += c3
    c["C2"] += c2
    if not c3:
        out.append((name, g6(G), len(tw)))


def main():
    kind = sys.argv[1]
    c, out = Counter(), []
    if kind == "trees":
        for n in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
            c, out = Counter(), []
            for T in nx.nonisomorphic_trees(n):
                report("tree", T, c, out)
            print("trees n =", n, dict(c), "outside C3:", out, flush=True)
        return
    if kind == "prod":
        fam = {
            "K3xK3": nx.cartesian_product(nx.complete_graph(3), nx.complete_graph(3)),
            "C4xK2": nx.cartesian_product(nx.cycle_graph(4), nx.complete_graph(2)),
            "C5xK2": nx.cartesian_product(nx.cycle_graph(5), nx.complete_graph(2)),
            "P3xP3": nx.cartesian_product(nx.path_graph(3), nx.path_graph(3)),
            "P3xP4": nx.cartesian_product(nx.path_graph(3), nx.path_graph(4)),
            "C3xP3": nx.cartesian_product(nx.cycle_graph(3), nx.path_graph(3)),
            "C4xP3": nx.cartesian_product(nx.cycle_graph(4), nx.path_graph(3)),
            "K4xK3": nx.cartesian_product(nx.complete_graph(4), nx.complete_graph(3)),
            "3K3": nx.disjoint_union_all([nx.complete_graph(3)] * 3),
            "2C5": nx.disjoint_union(nx.cycle_graph(5), nx.cycle_graph(5)),
            "C5+C6": nx.disjoint_union(nx.cycle_graph(5), nx.cycle_graph(6)),
            "2P4": nx.disjoint_union(nx.path_graph(4), nx.path_graph(4)),
            "P4+P5": nx.disjoint_union(nx.path_graph(4), nx.path_graph(5)),
            "K3,3,3": nx.complete_multipartite_graph(3, 3, 3),
            "K2,3,4": nx.complete_multipartite_graph(2, 3, 4),
            "W7": nx.wheel_graph(8),
            "Moebius8": nx.circulant_graph(8, [1, 4]),
            "Heawood": nx.heawood_graph(),
            "Frucht": nx.frucht_graph(),
            "Pappus-v": None,
        }
        for name, G in fam.items():
            if G is None:
                continue
            base = nx.convert_node_labels_to_integers(G)
            report(name, base, c, out)
            seen = set()
            for v in base:
                H = base.copy()
                H.remove_node(v)
                k = canon(H)
                if k in seen:
                    continue
                seen.add(k)
                report(name + "-v%d" % v, H, c, out)
            seen = set()
            for a, b in base.edges():
                H = base.copy()
                H.remove_edge(a, b)
                k = canon(H)
                if k in seen:
                    continue
                seen.add(k)
                report(name + "-e%d,%d" % (a, b), H, c, out)
        print("products etc.", dict(c), "outside C3:", out, flush=True)
        return
    if kind == "random":
        n, count = int(sys.argv[2]), int(sys.argv[3])
        rng = random.Random(5)
        for p in (0.2, 0.35, 0.5):
            c, out = Counter(), []
            for _ in range(count):
                G = nx.gnp_random_graph(n, p, seed=rng.randrange(10 ** 9))
                report("gnp", G, c, out)
            print("random n =", n, "p =", p, dict(c), "outside C3:", out, flush=True)


main()
