"""Exhaustive test of the abstract statement CORE of sketch t2 (section 7) on labelled graphs
(evidence only):  python3 notes/sketches/<step>/t2_core_check.py [n_max]   (default 6; 7 is slow)

CORE: let F be a family of graphs on Fin n with common parameters (d, q, b, e) such that every
K in F has, for every vertex u, a member K' != K of F agreeing with K off u. Then no G in F has
two further members agreeing with G off v at *every* low vertex v.

The hypothesis is monotone in F and the conclusion is antitone, so it suffices to test the
largest such family F* inside each full parameter class (greatest fixed point of "delete a graph
with no partner at some vertex").
"""
import itertools
import sys
from collections import defaultdict


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for n in range(3, n_max + 1):
        pairs = list(itertools.combinations(range(n), 2))
        fam = defaultdict(list)
        for bits in range(1 << len(pairs)):
            adj = [0] * n
            for i, (a, b) in enumerate(pairs):
                if bits >> i & 1:
                    adj[a] |= 1 << b
                    adj[b] |= 1 << a
            deg = [bin(m).count("1") for m in adj]
            lo, hi = min(deg), max(deg)
            if hi != lo + 1:
                continue
            high = sum(1 << x for x in range(n) if deg[x] == hi)
            h = [bin(adj[x] & high).count("1") for x in range(n)]
            bs = {h[x] for x in range(n) if deg[x] == lo}
            es = {h[x] for x in range(n) if deg[x] == hi}
            if len(bs) != 1 or len(es) != 1:
                continue
            fam[(lo, bin(high).count("1"), bs.pop(), es.pop())].append((bits, tuple(deg)))
        n_fam = n_star = n_graphs = worst = 0
        bad = 0
        for key, members in fam.items():
            n_fam += 1
            d = key[0]
            alive = {bits: deg for bits, deg in members}
            masks = []
            for u in range(n):
                m = 0
                for i, (a, b) in enumerate(pairs):
                    if a != u and b != u:
                        m |= 1 << i
                masks.append(m)
            while True:
                groups = [defaultdict(int) for _ in range(n)]
                for bits in alive:
                    for u in range(n):
                        groups[u][bits & masks[u]] += 1
                dead = [bits for bits in alive
                        if any(groups[u][bits & masks[u]] < 2 for u in range(n))]
                if not dead:
                    break
                for bits in dead:
                    del alive[bits]
            if not alive:
                continue
            n_star += 1
            n_graphs += len(alive)
            for bits, deg in alive.items():
                low = [v for v in range(n) if deg[v] == d]
                m = min(groups[v][bits & masks[v]] - 1 for v in low) if low else 99
                worst = max(worst, m)
                if m >= 2:
                    bad += 1
        print("n=%d: parameter classes %d, with nonempty F* %d, labelled graphs in some F* %d, "
              "max over G of (min over low v of partners) = %d, violations %d"
              % (n, n_fam, n_star, n_graphs, worst, bad), flush=True)


if __name__ == "__main__":
    main()
