# Exact read number per edge of an AND/OR circuit (proof-tree count vectors, Pareto/capped).
import sys, itertools
def analyze(n, gates, out, edges, cap=6):
    def val(x):
        w=list(x)
        for op,(a,b) in gates: w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
        return w
    F=lambda x: any(x[a] and x[b] for a,b in edges)
    ok=all(val(x)[out]==F(x) for x in itertools.product([0,1],repeat=n))
    res={}
    for (a,b) in edges:
        R=[set() for _ in range(n+len(gates))]
        R[a]={(1,0)}; R[b]={(0,1)}
        for j,(op,(p,q)) in enumerate(gates):
            if op=='or': R[n+j]=R[p]|R[q]
            else: R[n+j]={(min(u[0]+v[0],cap),min(u[1]+v[1],cap)) for u in R[p] for v in R[q]}
        res[(a,b)]=min(max(v) for v in R[out]) if R[out] else None
    return ok,res
if __name__=="__main__":
    g=[('or',(0,2)),('and',(1,4)),('or',(0,5)),('or',(4,5)),('and',(7,9)),('or',(6,10)),('or',(3,11)),('or',(6,11)),('and',(12,13)),('and',(14,15)),('or',(8,16))]
    E=[(0,4),(0,5),(0,6),(1,4),(2,5),(3,6)]
    print(analyze(7,g,17,E))
