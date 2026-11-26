# Independent clause-by-clause encoding of the frozen Lean body of step
# ..._no_pointed_pair_no_switch (C1..C10 as read from desk.py status).
import itertools, sys, networkx as nx
from fractions import Fraction
import numpy as np
from networkx.algorithms.isomorphism import GraphMatcher, categorical_node_match
nm=categorical_node_match('m',0)
def dele(G,S):
    return G.subgraph([x for x in G if x not in S]).copy()
def iso(A,B): return nx.is_isomorphic(A,B)
def isos(A,B): return GraphMatcher(A,B).isomorphisms_iter()
def ptd(G,p1,p2,u,v):  # exists e: G-p1 -> G-u with e(p2)=v
    A=dele(G,[p1]); B=dele(G,[u])
    nx.set_node_attributes(A,{x:int(x==p2) for x in A},'m'); nx.set_node_attributes(B,{x:int(x==v) for x in B},'m')
    return GraphMatcher(A,B,node_match=nm).is_isomorphic()
def member(G, why=False):
    n=G.number_of_nodes(); V=list(G); deg=dict(G.degree()); adj=G.has_edge
    if not nx.is_connected(G) or not nx.is_connected(nx.complement(G)): return 'C1C2'
    if not any(all(x in (u,v) or adj(x,u) or adj(x,v) for x in V) for u,v in G.edges()): return 'C3'
    pairs=[(x,y) for x in V for y in V if x!=y]
    d2={p:dele(G,p) for p in pairs}
    def iso2(p,q): return iso(d2[p],d2[q])
    # C4
    for u in V:
        D=[p for p in pairs if deg[p[0]]==deg[u]]
        if all(adj(*p)==adj(*q) for p in D for q in D if iso2(p,q)): return 'C4'
    # C5
    for u,v in pairs:
        K=d2[(u,v)]
        if any(iso(K,G.subgraph(T)) for T in itertools.combinations(V,n-2) if set(T)!=set(V)-{u,v}): continue
        A=list(isos(K,K))
        if all(any(all(adj(v,h[x])==adj(v,x) for x in K) and all(adj(u,g[h[x]])==adj(u,x) for x in K) for h in A) for g in A): return 'C5'
    # C6
    for u in V:
        ok=True
        for j in range(n+2):
            Aj=all(adj(xp,yp) for y in V if y!=u and adj(u,y) and deg[y]==j+1 for (xp,yp) in pairs if deg[xp]==deg[u] and iso2((u,y),(xp,yp)))
            Bj=all(not adj(xp,yp) for y in V if y!=u and not adj(u,y) and deg[y]==j for (xp,yp) in pairs if deg[xp]==deg[u] and iso2((u,y),(xp,yp)))
            if not (Aj or Bj): ok=False;break
        if ok: return 'C6'
    cards={x:dele(G,[x]) for x in V}
    def badtwist(u,up):  # exists alpha: G-u ~ G-u', x: u~x, not u'~alpha x
        for al in isos(cards[u],cards[up]):
            if any(adj(u,x) and not adj(up,al[x]) for x in cards[u]): return True
        return False
    # C7
    ds=set(deg.values())
    if max(ds)-min(ds)<=1 and all(iso(cards[x],cards[y]) for x in V for y in V if deg[x]==deg[y]):
        if any(badtwist(u,up) for u in V for up in V): return 'C7'
    # C8, C9
    def Y(u,v): return {(p1,p2) for (p1,p2) in pairs if ptd(G,p1,p2,u,v)}
    def degpres(x,y):
        K=d2[(x,y)]; return all(all(deg[g[z]]==deg[z] for z in K) for g in isos(K,K))
    for u,v in pairs:
        Yuv=Y(u,v)
        same=[p for p in pairs if iso2(p,(u,v))]
        # C8
        c1 = (not adj(u,v)) or (deg[u]+1!=deg[v] and deg[u]!=deg[v])
        c2 = adj(u,v) or (deg[u]!=deg[v] and deg[u]!=deg[v]+1)
        if c1 and c2:
            X=[p for p in same if p not in Yuv and not any(ptd(G,p[0],p[1],yp,xp) for (xp,yp) in Yuv)]
            if len(X)<len(Yuv) and all(degpres(x,y) for (x,y) in Yuv): return 'C8'
        # C9
        if ptd(G,u,v,v,u):
            X=[p for p in same if p not in Yuv]
            if len(X)<len(Yuv) and degpres(u,v): return 'C9'
    # C10
    M=nx.to_numpy_array(G,nodelist=V); dv=np.array([deg[x] for x in V])
    s=M@dv
    # integer (a,b) with s = a*deg + b
    sols=None
    if len(set(dv))==1:
        sols='any'
    else:
        x0,x1=[V.index(x) for x in V][:1]+[next(i for i in range(n) if dv[i]!=dv[0])]
        a=Fraction(int(s[x1]-s[x0]),int(dv[x1]-dv[x0])); b=Fraction(int(s[x0]))-a*int(dv[x0])
        if a.denominator==1 and b.denominator==1 and all(s[i]==a*int(dv[i])+b for i in range(n)): sols=[int(a)]
        else: sols=[]
    ev=np.linalg.eigvals(M)
    def noteig(l): return min(abs(ev-l))>1e-7
    for up in V:
        if sols=='any': okA=True
        else: okA=any(noteig(a-deg[up]) for a in sols)
        if okA and any(badtwist(u,up) for u in V): return 'C10'
    return 'IN'
if __name__=='__main__':
    if sys.argv[1]=='members':
        for s in ['Ffk}W','Ff]mw','Gl]o^[']:
            print(s, member(nx.from_graph6_bytes(s.encode())))
    else:
        from collections import Counter
        sys.path.insert(0,'/home/db/repositories/recon_conjecture/tools/search')
        import small_graphs as sg
        c=Counter(); ins=[]
        for G in sg.all_graphs(int(sys.argv[1])) if hasattr(sg,'all_graphs') else []:
            r=member(G); c[r]+=1
            if r=='IN': ins.append(nx.to_graph6_bytes(G,header=False).decode().strip())
        print(c, ins)
