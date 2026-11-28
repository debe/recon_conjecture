"""t1: check that the residual members reported in t4 sec. 8 satisfy the Lean hypotheses of
diam2_impure clause by clause (screen_lib transcription). Evidence that the class is non-empty;
says nothing about reconstructibility."""
import os, sys
import networkx as nx
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'conj_kelly_ulam__connected_dominating_or_diam2'))
from screen_lib import diam2_both, has_pure_class, has_unique_copy_pair

MEMBERS = ['GhdYLc', 'GhEKzW', 'GhEJ]o', 'K[N_ZpBVe`q{', 'KbcrMZwA~c@r']
for g6 in MEMBERS:
    G = nx.from_graph6_bytes(g6.encode())
    Gc = nx.complement(G)
    row = dict(n=G.number_of_nodes(), conn=nx.is_connected(G), coconn=nx.is_connected(Gc),
               d2=diam2_both(G), pure=has_pure_class(G), glue=has_unique_copy_pair(G),
               selfcompl=nx.is_isomorphic(G, Gc),
               degs=sorted(d for _, d in G.degree()))
    print(g6, row, 'IN CLASS' if row['conn'] and row['coconn'] and row['d2'] and not row['pure'] and not row['glue'] else 'not in class')
