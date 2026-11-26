# Independent encoding of the proposed child triple_gluing_stabilizer (Lean body, sketch t1 §8)
import itertools, networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
def ind(G,S): return G.subgraph(S).copy()
def iso(A,B): return nx.is_isomorphic(A,B)
def auts(H): return list(GraphMatcher(H,H).isomorphisms_iter())
def c3m(G):
    n=G.number_of_nodes(); V=list(G); wits=[]
    for u,v,w in itertools.permutations(V,3):
        R=[x for x in V if x not in (u,v,w)]; K=ind(G,R)
        # (U): every Finset T with G[T] ~ K equals R  (only |T| = n-3 possible)
        if any(iso(ind(G,T),K) for T in itertools.combinations(V,n-3) if set(T)!=set(R)): continue
        def S(x,y,z):
            Gx=ind(G,[t for t in V if t!=x])
            if not iso(ind(G,[t for t in V if t not in (x,y)]),ind(G,[t for t in V if t not in (x,z)])): return True
            return any(r[y]==z for r in auts(Gx))
        if not (S(u,v,w) and S(v,u,w) and S(w,u,v)): continue
        ok=all(all(G.has_edge(u,g[x])==G.has_edge(u,x) for x in R) for g in auts(K) if all(G.has_edge(w,g[x])==G.has_edge(w,x) for x in R))
        if ok: wits.append((u,v,w))
    return wits
def claim(G):  # for small_graphs: nothing; library use
    return True
if __name__=='__main__':
    for s in ['Ffk}W','Ff]mw','Gl]o^[']:
        G=nx.from_graph6_bytes(s.encode()); print(s, c3m(G))
