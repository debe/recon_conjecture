"""Check of Proposition V (sketch t3): orbit calculus for G = X - r, X vertex-transitive, under tightness.
Predictions for a class (u, v, w), T = {r, u, v}, Gamma = Aut(X):
  (W) holds  <=>  clause (i) at (u, v)  or  the class is symmetric:
        some gamma in Gamma fixes w and (gamma{r,u} = {r,v}, gamma v = u) or (gamma{r,u} = {u,v}, gamma v = r);
  (K) at an (i)-class  <=>  every gamma in Gamma with gamma T = T, gamma w = w fixes N_X(u) minus T or N_X(r) minus T.
A disagreement means that tightness fails for that X (or that the calculus is wrong).
Evidence only.   python3 t3s_vtminus.py
"""
import networkx as nx

from t3s_lib import *

XS = {"Q3": nx.hypercube_graph(3), "Petersen": nx.petersen_graph(), "K3xK3": nx.cartesian_product(nx.complete_graph(3), nx.complete_graph(3)),
      "C5xK2": nx.circular_ladder_graph(5), "C9(1,2)": nx.circulant_graph(9, [1, 2]), "C10(1,4)": nx.circulant_graph(10, [1, 4]),
      "C11(1,2)": nx.circulant_graph(11, [1, 2]), "C11(1,3)": nx.circulant_graph(11, [1, 3]),
      "C12(1,5)": nx.circulant_graph(12, [1, 5]), "C12(1,3)": nx.circulant_graph(12, [1, 3]),
      "C13(1,5)": nx.circulant_graph(13, [1, 5]), "Paley13": nx.circulant_graph(13, [1, 3, 4]),
      "C13(1,2,4)": nx.circulant_graph(13, [1, 2, 4]), "icosahedron": nx.icosahedral_graph(),
      "K4xK3": nx.cartesian_product(nx.complete_graph(4), nx.complete_graph(3)), "Heawood": nx.heawood_graph()}
for name, X in XS.items():
    X = nx.convert_node_labels_to_integers(X)
    N = X.number_of_nodes()
    r = N - 1
    Gam = auts(X)
    G = X.copy()
    G.remove_node(r)
    C = Census(G)
    cls = classes(G, C)
    badW = badK = nW = nK = ni = 0
    for c in cls:
        u, v, w = c["rep"]
        sym = any(g[w] == w and (({g[r], g[u]} == {r, v} and g[v] == u) or ({g[r], g[u]} == {u, v} and g[v] == r)) for g in Gam)
        predW = c["i"] or sym
        badW += predW != c["W"]
        nW += c["W"]
        if c["i"]:
            ni += 1
            T = {r, u, v}
            Nu, Nr = set(X[u]) - T, set(X[r]) - T
            predK = all({g[t] for t in Nu} == Nu or {g[t] for t in Nr} == Nr
                        for g in Gam if g[w] == w and {g[r], g[u], g[v]} == T)
            if c["W"]:
                badK += predK != c["K"]
                nK += bool(c["K"])
    in3 = sum(1 for c in cls if c["W"] and c["K"])
    print("%s - r: n=%d |Aut X|=%d classes=%d with(i)=%d  W holds=%d (W disagreements %d)  (i)-classes with K=%d (K disagreements %d)  classes in W3=%d" % (
        name, N - 1, len(Gam), len(cls), ni, nW, badW, nK, badK, in3), flush=True)
