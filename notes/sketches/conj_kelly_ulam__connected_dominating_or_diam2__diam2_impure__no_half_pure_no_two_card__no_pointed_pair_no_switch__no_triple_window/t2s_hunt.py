"""Hunt for phantoms beyond n = 8.  Evidence only.

A phantom K of G at F = G-u-v has a vertex a with K-a isomorphic to a card G-x, x a first entry of
a pair of type F, and deg_K a = deg x.  So every phantom (at any F) is, up to isomorphism, a
re-attachment  G[x -> A]  (x re-attached to a set A of deg x vertices).  For a graph G:
  1. enumerate all re-attachments K = G[x -> A], A != N(x), with keys(K) = keys(G)
     (keys = multiset of (deg, w2)); count those not isomorphic to G        ("key twins")
  2. for each key twin K and each two-deleted type F of G compare slice_F(K) with slice_F(G)
     -> phantoms (G, F, K); G is outside PC+ iff every pair (u, v) has a phantom.
Families: named graphs of rounds 10-12, random graphs, random nearly regular graphs
(random regular graph minus a vertex / minus an edge / plus an edge).

  python3 t2s_hunt.py named
  python3 t2s_hunt.py random <n> <count> <p> [seed]
  python3 t2s_hunt.py nearreg <n> <d> <count> [seed]
"""
import itertools
import os
import random
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t2s_lib import *  # noqa


def keys(G):
    return sorted((G.degree(x), sum(G.degree(y) for y in G[x])) for x in G)


def key_twins(G):
    """Re-attachments with the keys of G, not isomorphic to G, up to isomorphism."""
    kG = keys(G)
    cG = canon(G)
    deg = dict(G.degree())
    w2 = {x: sum(deg[y] for y in G[x]) for x in G}
    V = sorted(G)
    out = {}
    n_same_keys = 0
    for x in V:
        Nx = set(G[x])
        rest = [y for y in V if y != x]
        d = deg[x]
        # degree multiset must be preserved: quick filter on the multiset of degrees
        base = Counter(deg.values())
        for A in itertools.combinations(rest, d):
            A = set(A)
            if A == Nx:
                continue
            lost, gained = Nx - A, A - Nx
            if Counter(deg[t] - 1 for t in lost) != Counter(deg[t] for t in gained):
                continue  # level counts
            K = G.copy()
            K.remove_edges_from([(x, t) for t in lost])
            K.add_edges_from((x, t) for t in gained)
            if keys(K) != kG:
                continue
            n_same_keys += 1
            c = canon(K)
            if c != cG and c not in out:
                out[c] = K
    return n_same_keys, list(out.values())


def analyse(name, G):
    G = nx.convert_node_labels_to_integers(G)
    n_same, twins = key_twins(G)
    res = {"n": G.number_of_nodes(), "re-attachments with the keys of G": n_same, "key twins (non-isomorphic)": len(twins)}
    if twins:
        C = Census(G, triples=False)
        sl = slices(G, C)
        amb = set()
        for K in twins:
            slK = slices(K)
            for F, cnt in sl.items():
                if slK.get(F) == cnt:
                    amb.add(F)
        res["two-deleted types"] = len(sl)
        res["types with a phantom"] = len(amb)
        res["OUTSIDE PC+"] = len(amb) == len(sl)
    print(name, res, flush=True)
    return res


def main():
    mode = sys.argv[1]
    tot = Counter()
    if mode == "named":
        fam = {
            "C13(1,2,4)-0  KbcrMZwA~c@r": from_g6("KbcrMZwA~c@r"),
            "C12(1,2,3)-0  J~[ww[F_}B_": from_g6("J~[ww[F_}B_"),
            "D6 member JhCkmT`kIw_": from_g6("JhCkmT`kIw_"),
            "D6 member JUwkeXelqv?": from_g6("JUwkeXelqv?"),
            "Ffk}W": from_g6("Ffk}W"), "Ff]mw": from_g6("Ff]mw"), "Gl]o^[": from_g6("Gl]o^["),
            "GhEJ]o": from_g6("GhEJ]o"),
            "Petersen - v": nx.petersen_graph().subgraph(range(1, 10)).copy(),
            "Frucht": nx.frucht_graph(),
            "Frucht - v0": nx.frucht_graph().subgraph(range(1, 12)).copy(),
            "Paley13 - v": nx.paley_graph(13).to_undirected().subgraph(range(1, 13)).copy(),
        }
        Fr = nx.frucht_graph()
        e = list(Fr.edges())[0]
        Fe = Fr.copy(); Fe.remove_edge(*e)
        fam["Frucht - e"] = Fe
        ne = next((a, b) for a in Fr for b in Fr if a < b and not Fr.has_edge(a, b))
        Fp = Fr.copy(); Fp.add_edge(*ne)
        fam["Frucht + e"] = Fp
        import networkx.generators.classic as _c  # noqa
        S = nx.Graph()
        for i in range(4):
            for j in range(4):
                for (a, b) in [(1, 0), (0, 1), (1, 1)]:
                    S.add_edge((i, j), ((i + a) % 4, (j + b) % 4))
        S = nx.convert_node_labels_to_integers(S)
        fam["Shrikhande - v"] = S.subgraph(range(1, 16)).copy()
        for name, G in fam.items():
            analyse(name, G)
        return
    if mode == "random":
        n, count, p = int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
        rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
        for i in range(count):
            G = nx.gnp_random_graph(n, p, seed=rng.randrange(10 ** 9))
            r = analyse("gnp(%d,%.2f)#%d %s" % (n, p, i, g6(G)), G)
            tot["graphs"] += 1
            tot["with key twins"] += bool(r["key twins (non-isomorphic)"])
            tot["with a phantom"] += bool(r.get("types with a phantom"))
            tot["outside PC+"] += bool(r.get("OUTSIDE PC+"))
    if mode == "nearreg":
        n, d, count = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
        for i in range(count):
            R = nx.random_regular_graph(d, n, seed=rng.randrange(10 ** 9))
            variants = {}
            v = rng.choice(sorted(R))
            variants["-v"] = R.subgraph([x for x in R if x != v]).copy()
            e = rng.choice(sorted(R.edges()))
            X = R.copy(); X.remove_edge(*e); variants["-e"] = X
            ne = rng.choice([(a, b) for a in R for b in R if a < b and not R.has_edge(a, b)])
            X = R.copy(); X.add_edge(*ne); variants["+e"] = X
            for tag, G in variants.items():
                r = analyse("reg(%d,%d)#%d%s %s" % (n, d, i, tag, g6(nx.convert_node_labels_to_integers(G))), G)
                tot["graphs"] += 1
                tot["with key twins"] += bool(r["key twins (non-isomorphic)"])
                tot["with a phantom"] += bool(r.get("types with a phantom"))
                tot["outside PC+"] += bool(r.get("OUTSIDE PC+"))
    print("TOTAL", dict(tot))


if __name__ == "__main__":
    main()
