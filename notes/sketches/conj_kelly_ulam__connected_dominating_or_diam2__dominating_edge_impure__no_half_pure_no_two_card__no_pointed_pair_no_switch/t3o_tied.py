"""Which graphs are census-tied?  Exhaustive n <= N, evidence only.

pair census (k = 2):  some pair (u, v) with
    [T]   (v, u) ~ (u, v) as pointed cards and |B| < |A|,  or
    [T+]  degree clause (i) and |R| < |A|
  (the census clauses of Theorems T, T+ of round 11, WITHOUT the twist clauses (d), (iii)).
triple census (k = 3): some apex triple with (a1), (a2), (b) of Theorem T3 (without Helly).
Printed per n: counts, and the graphs tied at k = 2, with regularity, |Aut|, number of card types,
and whether they are tied at k = 3 as well.
"""
import sys
from collections import Counter, defaultdict

from t3o_lib import *
from small_graphs import all_graphs


def pair_census(G, cid):
    members = defaultdict(list)
    for p, i in cid.items():
        members[i].append(p)
    ty = {p: ctype(G, p) for p in cid}
    tsize = Counter(ty.values())
    t_ok = tp_ok = False
    for (u, v) in cid:
        A = members[cid[(u, v)]]
        n_f = tsize[ty[(u, v)]]
        if cid[(v, u)] == cid[(u, v)] and n_f - len(A) < len(A):
            t_ok = True
        if cond_i(G, u, v):
            chat = {cid[(y, x)] for (x, y) in A}
            C = sum(len(members[j]) for j in chat)
            if n_f - len(A) - C < len(A):
                tp_ok = True
        if t_ok and tp_ok:
            break
    return t_ok, tp_ok


def main(N):
  for n in range(4, N + 1):
      c = Counter()
      tied = []
      for G in all_graphs(n):
          G = nx.convert_node_labels_to_integers(G)
          cid2 = pointed_classes(G, 2)
          t_ok, tp_ok = pair_census(G, cid2)
          c["all"] += 1
          c["T census"] += t_ok
          c["T+ census"] += tp_ok
          if t_ok or tp_ok:
              continue
          c["tied at k=2"] += 1
          t3 = bool(T3_apex(G, None, "none"))
          c["tied at k=2 and k=3"] += (not t3)
          degs = sorted(set(d for _, d in G.degree()))
          orb, na = vertex_orbits(G)
          nct = len({ctype(G, (v,)) for v in G})
          tied.append((g6(G), "regular" if len(degs) == 1 else "degs %s" % degs, "|Aut| %d" % na,
                       "orbits %d" % len(orb), "card types %d" % nct,
                       "connected" if nx.is_connected(G) else "disconnected",
                       "co-connected" if nx.is_connected(nx.complement(G)) else "co-disconnected",
                       "tied at 3" if not t3 else "T3 census ok"))
      print("n =", n, dict(c), flush=True)
      for row in tied:
          print("   ", row, flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]))
