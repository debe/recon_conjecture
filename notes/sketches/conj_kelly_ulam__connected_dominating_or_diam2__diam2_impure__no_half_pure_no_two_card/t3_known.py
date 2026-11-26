"""Known face members and SRG-minus-vertex graphs against the remainder and the new classes."""
import sys, os
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_lib import *  # noqa

KNOWN = ["GhdYLc", "GhEKzW", "GhEJ]o", "K[N_ZpBVe`q{", "KbcrMZwA~c@r", "OpyHvCM]IFJpsMdwu`pJp"]

def srg_minus():
    out = {}
    P = nx.paley_graph(13).to_undirected(); out["Paley13-v"] = P
    R = nx.cartesian_product(nx.complete_graph(4), nx.complete_graph(4)); out["Rook4x4-v"] = R
    res = {}
    for k, X in out.items():
        X = nx.convert_node_labels_to_integers(X)
        X.remove_node(0)
        res[k] = nx.convert_node_labels_to_integers(X)
    return res

def report(name, G):
    fl, ty = remainder_flags(G)
    ucp = unique_copy_pairs(G, ty)
    fg = glue_pairs(G, ty, f_deg)
    fgc = glue_pairs(G, ty, f_deg_codeg)
    print(name, "n=%d" % G.number_of_nodes(), "|Aut|=%d" % len(auts(G)), fl,
          "uniq pairs=%d" % len(ucp), "FG_deg=%d" % len(fg), "FG_deg_codeg=%d" % len(fgc), flush=True)

if __name__ == "__main__":
    for s in KNOWN:
        report(s, from_g6(s))
    for k, X in srg_minus().items():
        report(k, X)
