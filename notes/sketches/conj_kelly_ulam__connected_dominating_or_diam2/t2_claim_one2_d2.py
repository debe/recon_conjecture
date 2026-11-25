"""Hypothesis H* (NOT relied on by the sketch; a red-team target): every graph with all distances
<= 2 in G and in the complement has a card G - v such that every one-vertex extension of that card
with the same neighbour-degree data as G is isomorphic to G.

A witness against H* is the first concrete member of the residual child `diam2_ambiguous`
(up to the tie between the card vertex and the bijection, which only shrinks the residual).
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from t2_lib import in_D2
from t2_stats_one2 import one2


def claim(G):
    return (not in_D2(G)) or one2(G)
