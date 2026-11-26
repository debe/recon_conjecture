"""Latin-square graph of the cyclic group Z_m (a Cayley graph on Z_m x Z_m, SRG, not rank 3 for
m = 6) minus a vertex: frozen remainder? class US?  Evidence only.
  python3 .../t1us_probe_latin6.py [m]      (default 6; slow)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1us_probe_srg import latin_graph, report  # noqa: E402

m = int(sys.argv[1]) if len(sys.argv) > 1 else 6
report("L3(Z%d)" % m, latin_graph([[(r + c) % m for c in range(m)] for r in range(m)]))
