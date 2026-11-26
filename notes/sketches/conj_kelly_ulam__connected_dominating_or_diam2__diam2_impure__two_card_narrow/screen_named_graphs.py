"""Relaxed Stage A / Stage B checks on named graphs that carry extensions (evidence only).

python3 screen_named_graphs.py   # prints, per graph: NF d values, (a) (b) (c) (d), theta,
                                 # |C_G(u)| per vertex, and whether the low bound holds.
"""
import os, sys, time
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "search"))
from small_graphs import from_g6  # noqa: E402
from screen_common import deck_key, nf_ds, stage_a, extensions  # noqa: E402


def minus0(F):
    F = nx.convert_node_labels_to_integers(F)
    F.remove_node(0)
    return nx.convert_node_labels_to_integers(F)


def clebsch():
    """Folded 5-cube: Q4 plus the antipodal matching, srg(16, 5, 0, 2)."""
    Q = nx.convert_node_labels_to_integers(nx.hypercube_graph(4), label_attribute="b")
    lab = {Q.nodes[v]["b"]: v for v in Q}
    for b, v in lab.items():
        Q.add_edge(v, lab[tuple(1 - t for t in b)])
    return Q


NAMED = {
    "member GhEJ]o": from_g6("GhEJ]o"),
    "C5-v": minus0(nx.cycle_graph(5)),
    "C7-v": minus0(nx.cycle_graph(7)),
    "prism-v": minus0(nx.circular_ladder_graph(3)),
    "cube-v": minus0(nx.hypercube_graph(3)),
    "K33-v": minus0(nx.complete_bipartite_graph(3, 3)),
    "Moebius8-v": minus0(nx.circulant_graph(8, [1, 4])),
    "Petersen-v": minus0(nx.petersen_graph()),
    "C10(1,2)-v": minus0(nx.circulant_graph(10, [1, 2])),
    "member K[N_ZpBVe`q{": from_g6("K[N_ZpBVe`q{"),
    "Paley13-v": minus0(nx.paley_graph(13).to_undirected()),
    "Paley9=K3xK3-v": minus0(nx.paley_graph(9).to_undirected()),
    "T5=compl(Petersen)-v": minus0(nx.complement(nx.petersen_graph())),
    "T6-v": minus0(nx.line_graph(nx.complete_graph(6))),
    "K4xK4-v": minus0(nx.cartesian_product(nx.complete_graph(4), nx.complete_graph(4))),
    "Clebsch-v": minus0(clebsch()),
    "Paley17-v": minus0(nx.paley_graph(17).to_undirected()),
    "member OpyHvCM]IFJpsMdwu`pJp": from_g6("OpyHvCM]IFJpsMdwu`pJp"),
}
only = sys.argv[1:]
for name, G in NAMED.items():
    if only and name not in only:
        continue
    t = time.time()
    deck = deck_key(G)
    for d in nf_ds(G):
        a, b, c, dd, info = stage_a([G], deck, d)
        deg = dict(G.degree())
        sizes = {u: len(extensions(G, u, deck)) for u in G}
        low_ok = all(sizes[u] <= 2 for u in G if deg[u] == d)
        all_ok = all(s <= 2 for s in sizes.values())
        print(f"{name} n={len(G)} d={d} a={a} b={b} c={c} d={dd} theta={sorted(info['theta'])} "
              f"|C|={sorted(set(sizes.values()))} low_bound={low_ok} all_bound={all_ok} "
              f"fail={info['fail'] if info['fail'] and info['fail'][0] != 'b' else None} "
              f"({time.time()-t:.0f}s)", flush=True)
    if not nf_ds(G):
        print(f"{name}: not NF", flush=True)
