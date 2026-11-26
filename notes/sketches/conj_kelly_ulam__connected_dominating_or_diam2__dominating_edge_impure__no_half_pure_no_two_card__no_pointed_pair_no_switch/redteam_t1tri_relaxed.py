"""Red team (round12-sweep) on t1.md, Theorem G3. Relaxed single-graph form, stronger than
t1tri_claims.py: H = (G - u) + a with ANY neighbourhood of a; require (i) H has exactly one
(n-3)-set inducing K = G - {u,v,w} and (ii) distinct b, c (any vertices != a) with
G - v ~ H - b, G - w ~ H - c. If G satisfies (U), (S), (OI) at {u,v,w}, claim H ~ G.
Fidelity: (U), (S), (OI) transcribed from the Lean bodies C3M/C3OI of t1 section 8 (OI tested in the
first role found; it is symmetric by t1 section 4.4). Lemma C is the only use of the full deck; here it is
replaced by hypothesis (i), so the test does not presuppose a hypomorphic pair. Evidence only."""
import sys, itertools, random, networkx as nx
sys.path.insert(0,'/home/db/repositories/recon_conjecture/tools/search')
import small_graphs as sg
from networkx.algorithms.isomorphism import GraphMatcher
def dele(G,S): return G.subgraph([x for x in G if x not in S]).copy()
def auts(K): return list(GraphMatcher(K,K).isomorphisms_iter())
def hyp(G):
    n=len(G); V=list(G); out={}
    t3={D:sg.canon(dele(G,D)) for D in itertools.combinations(V,3)}
    from collections import Counter
    cnt=Counter(t3.values())
    for D,k in t3.items():
        if cnt[k]!=1: continue
        good=True
        for x in D:
            y,z=[t for t in D if t!=x]
            if sg.canon(dele(G,(x,y)))==sg.canon(dele(G,(x,z))):
                if not any(r[y]==z for r in auts(dele(G,[x]))): good=False;break
        if not good: continue
        R=[t for t in V if t not in D]; K=dele(G,D); A=auts(K)
        pres=lambda g,u: all(G.has_edge(u,g[x])==G.has_edge(u,x) for x in R)
        for u,v,w in itertools.permutations(D):
            AW=[g for g in A if pres(g,w)]; AV=[g for g in A if pres(g,v)]; AVW=[g for g in AV if pres(g,w)]
            OI=all(any(pres({x:g1[h[x]] for x in R},u) for h in AVW) for g1 in AW for g3 in AV if pres({x:g1[g3[x]] for x in R},u))
            if OI:
                out.setdefault(u,[]).append((v,w,t3[D])); break
    return out
def test(G,stats):
    n=len(G); V=list(G); H0=hyp(G)
    if not H0: return True
    cG=sg.canon(G); cards={x:sg.canon(dele(G,[x])) for x in V}
    for u,lst in H0.items():
        others=[x for x in V if x!=u]
        for bits in range(1<<(n-1)):
            H=G.copy(); H.remove_edges_from([(u,x) for x in others])
            H.add_edges_from((u,others[i]) for i in range(n-1) if bits>>i&1)
            if sg.canon(H)==cG: continue
            hc={x:sg.canon(dele(H,[x])) for x in V}
            for v,w,kK in lst:
                bs=[b for b in V if b!=u and hc[b]==cards[v]]; cs=[c for c in V if c!=u and hc[c]==cards[w]]
                if not any(b!=c for b in bs for c in cs): continue
                cnt=sum(1 for D in itertools.combinations(V,3) if sg.canon(dele(H,D))==kK)
                stats['matched']+=1
                if cnt==1:
                    print('WITNESS', sg.g6(G), (u,v,w), sg.g6(H)); return False
    return True
if __name__=='__main__':
    from collections import Counter
    st=Counter()
    if sys.argv[1]=='all':
        gs=sg.all_graphs(int(sys.argv[2]))
    else:
        gs=sg.random_graphs(int(sys.argv[2]),int(sys.argv[3]),seed=int(sys.argv[4]))
    k=0
    for G in gs:
        k+=1
        test(G,st)
    print(k,'graphs',st)

def claim(G):
    from collections import Counter
    return test(G, Counter())
