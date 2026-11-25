"""How much the t3 classes bite on Q = {both diameters <= 2}. Evidence only, never a result
and never an argument: it only says where the residual of the sketch starts.

  python3 notes/sketches/conj_kelly_ulam__connected_dominating_or_diam2/t3_stats.py [n_max] [samples]

Exhaustive for n <= 8 (n = 8 by vertex extension, as in t1_stats.py); G(n, 1/2) samples above.

Columns (each is a property of ONE graph G in Q)
  star     (*) at some vertex                                   (t1 K1 / t2 degree separation)
  star2    (*2) at some vertex: levels decided by forced sets   (t3 lemma D4)
  U2       some v such that every level-feasible S with (G - v) + S in Q is the image of N(v)
           under an automorphism of the card G - v                                (t3 D5)
  U2s      the same with the one-card spectral constraints added                  (t3 S5')
  U2s~     some v such that every such S gives a graph isomorphic to G  (semantic, cf. t2 one2)
  cor<=1   rank of the walk matrix >= n - 1                     (t3 S5, Godsil-McKay)
  hong     some card G - v has a walk matrix of full rank n - 1 (Hong 1982)
  res0     in neither U2 nor cor<=1   (the residual R of the sketch: no spectral one-card input)
  res      in none of star2, U2s, cor<=1, hong   (the residual R+ of the sketch)
"""
import os
import random
import sys
from collections import Counter

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "tools", "search"))
from small_graphs import canon, g6  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import decided_at, feasible_sets, in_Q, star2_at, star_at, walk_rank  # noqa: E402
from t1_stats import graphs  # noqa: E402


def flags(G, with_iso=True):
    n = G.number_of_nodes()
    f = {}
    f["star"] = any(star_at(G, v) for v in G.nodes())
    f["star2"] = any(star2_at(G, v) for v in G.nodes())
    f["U2"] = any(decided_at(G, v) for v in G.nodes())
    spec = {v: feasible_sets(G, v, use_Q=True, use_spec=True) for v in G.nodes()}
    f["U2s"] = any(decided_at(G, v, use_spec=True) for v in G.nodes())
    if with_iso:
        cg = canon(G)
        ok = False
        for v, sets in spec.items():
            good = True
            for S in sets:
                H = G.copy()
                H.remove_node(v)
                H.add_node(v)
                H.add_edges_from((v, s) for s in S)
                if canon(H) != cg:
                    good = False
                    break
            if good:
                ok = True
                break
        f["U2s~"] = ok
    r = walk_rank(G)
    f["cor"] = n - r
    f["cor<=1"] = r >= n - 1
    hong = False
    for v in G.nodes():
        C = G.copy()
        C.remove_node(v)
        C = nx.convert_node_labels_to_integers(C)
        if walk_rank(C) == n - 1:
            hong = True
            break
    f["hong"] = hong
    f["res0"] = not (f["U2"] or f["cor<=1"])
    f["res"] = not (f["star2"] or f["U2s"] or f["cor<=1"] or f["hong"])
    return f


def report(n, Qs, label):
    tot = Counter()
    cors = Counter()
    res = []
    for G in Qs:
        f = flags(G)
        for k, val in f.items():
            if k != "cor" and val:
                tot[k] += 1
        cors[f["cor"]] += 1
        if f["res0"]:
            res.append((g6(G), f["cor"], f["res"]))
    keys = ["star", "star2", "U2", "U2s", "U2s~", "cor<=1", "hong", "res0", "res"]
    print(f"n={n} ({label}): Q={len(Qs)}  " + "  ".join(f"{k}={tot[k]}" for k in keys))
    print(f"      corank of the walk matrix: {dict(sorted(cors.items()))}")
    if res:
        print(f"      members of R (graph6, corank, also in R+): {res[:12]}{' ...' if len(res) > 12 else ''}")
    sys.stdout.flush()


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    samples = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    for n in range(5, min(n_max, 8) + 1):
        Qs = [G for G in graphs(n) if in_Q(G)]
        report(n, Qs, "exhaustive")
    rng = random.Random(3)
    for n in range(9, n_max + 1):
        Qs, seen = [], set()
        tries = 0
        while len(Qs) < samples and tries < 200 * samples:
            tries += 1
            G = nx.gnp_random_graph(n, 0.5, seed=rng.randrange(10 ** 9))
            if not in_Q(G):
                continue
            key = canon(G)
            if key in seen:
                continue
            seen.add(key)
            Qs.append(G)
        report(n, Qs, f"G(n,1/2) sample, {tries} draws")


if __name__ == "__main__":
    main()
