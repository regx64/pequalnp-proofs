import itertools, subprocess, sys
def canon(n,E):
    best=None
    for p in itertools.permutations(range(n)):
        k=tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in E))
        if best is None or k<best: best=k
    return best
def bipartite(n,E):
    col=[-1]*n; adj=[[] for _ in range(n)]
    for a,b in E: adj[a].append(b); adj[b].append(a)
    for s in range(n):
        if col[s]<0:
            col[s]=0; st=[s]
            while st:
                u=st.pop()
                for v in adj[u]:
                    if col[v]<0: col[v]=1-col[u]; st.append(v)
                    elif col[v]==col[u]: return False
    return True
def tau(n,E):
    for k in range(n+1):
        for T in itertools.combinations(range(n),k):
            if all(a in T or b in T for a,b in E): return k
def c4free(n,E):
    adj=[set() for _ in range(n)]
    for a,b in E: adj[a].add(b); adj[b].add(a)
    return all(len(adj[a]&adj[b])<=1 for a,b in itertools.combinations(range(n),2))
seen=set(); out=[]
for n in range(2,7):
    pairs=list(itertools.combinations(range(n),2))
    for m in range(1,len(pairs)+1):
        for E in itertools.combinations(pairs,m):
            deg=[0]*n
            for a,b in E: deg[a]+=1; deg[b]+=1
            if min(deg)==0 or not bipartite(n,E): continue
            c=canon(n,E)
            if (n,c) in seen: continue
            seen.add((n,c)); out.append((n,list(c)))
print(len(out),"graphs",file=sys.stderr)
for n,E in out:
    t=tau(n,E); star=len(E)+t-1; cf=c4free(n,E)
    es=",".join(f"{a}-{b}" for a,b in E)
    res=None
    for s in range(n-1, star+1):
        if s>8: res="skip(>8)"; break
        r=subprocess.run(["./enumrk",str(s),str(n),es],capture_output=True,text=True).stdout.strip()
        first=r.splitlines()[0]
        if "circuits=0" not in first: res=r; break
    print(f"n={n} E={len(E)} tau={t} star={star} C4free={cf} edges={es}\n   {res}",flush=True)
