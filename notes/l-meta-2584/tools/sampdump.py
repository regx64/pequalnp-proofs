# Sample AO2 circuits of size s for an edge function with CaDiCaL (random seeds, blocking clauses),
# normalize by the implicant lift, compute the read number, and test two shrinking rewrites.
import sys, itertools, subprocess, os, random
CAD=os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical")
n=int(sys.argv[1]); E=[tuple(map(int,e.split('-'))) for e in sys.argv[2].split(',')]; s=int(sys.argv[3]); K=int(sys.argv[4])
Fr=lambda r: any(r>>a&1 and r>>b&1 for a,b in E)
mins=[(1<<a)|(1<<b) for a,b in E]
maxz=[r for r in range(1<<n) if not Fr(r) and all(Fr(r|(1<<i)) for i in range(n) if not r>>i&1)]
rows=mins+maxz
# ---- CNF (monotone AO2 normal form, as syn4) ----
cl=[]; nv=[0]
def new(): nv[0]+=1; return nv[0]
def exactly_one(vs):
    cl.append(list(vs)); cl.extend([[-a,-b] for a,b in itertools.combinations(vs,2)])
sel=[[[new() for k in range(n+j)] for e in range(2)] for j in range(s)]
opA=[new() for j in range(s)]
val=[{r:new() for r in rows} for j in range(s)]
va=[[{r:new() for r in rows} for e in range(2)] for j in range(s)]
for j in range(s):
    for e in range(2): exactly_one(sel[j][e])
    for ka in range(n+j):
        for kb in range(ka+1): cl.append([-sel[j][0][ka],-sel[j][1][kb]])
def wire(k,r): return ((r>>k)&1==1) if k<n else val[k-n][r]
for j in range(s):
    for r in rows:
        for e in range(2):
            v=va[j][e][r]
            for k in range(n+j):
                w=wire(k,r)
                if isinstance(w,bool): cl.append([-sel[j][e][k], v if w else -v])
                else: cl.append([-sel[j][e][k],-w,v]); cl.append([-sel[j][e][k],w,-v])
        g=val[j][r]; a=va[j][0][r]; b=va[j][1][r]
        cl += [[-opA[j],-g,a],[-opA[j],-g,b],[-opA[j],g,-a,-b],[opA[j],g,-a],[opA[j],g,-b],[opA[j],-g,a,b]]
for r in rows: cl.append([val[s-1][r]] if Fr(r) else [-val[s-1][r]])
for j in range(s-1): cl.append([sel[jj][e][n+j] for jj in range(j+1,s) for e in range(2)])
# ---- circuit tools ----
X=list(range(1<<n)); FT=[int(Fr(x)) for x in X]
def evalc(gs):
    W=[[x>>i&1 for x in X] for i in range(n)]
    for op,a,b in gs: W.append([(p&q) if op=='and' else (p|q) for p,q in zip(W[a],W[b])])
    return W
def computes(gs,o): W=evalc(gs); return o<len(W) and W[o]==FT
def readnum(gs,o,cap=6):
    worst=0
    for a,b in E:
        R=[set() for _ in range(n+len(gs))]; R[a]={(1,0)}; R[b]={(0,1)}
        for j,(op,p,q) in enumerate(gs):
            R[n+j]= R[p]|R[q] if op=='or' else {(min(u[0]+v[0],cap),min(u[1]+v[1],cap)) for u in R[p] for v in R[q]}
        worst=max(worst,min(max(v) for v in R[o]))
    return worst
def below(Wv): return all(not(v and not f) for v,f in zip(Wv,FT))
def normalize(gs,o):
    for _ in range(100):
        W=evalc(gs)
        top=set(); st=[o] if o>=n and gs[o-n][0]=='or' else []
        while st:
            x=st.pop()
            if x in top: continue
            top.add(x); op,a,b=gs[x-n]
            for c in (a,b):
                if c>=n and gs[c-n][0]=='or': st.append(c)
        pick=None
        for j,(op,a,b) in enumerate(gs):
            x=n+j
            if x in top or x==o or op!='or': continue
            for c,z in ((a,b),(b,a)):
                if any(W[c]) and below(W[c]): pick=(j,c,z); break
            if pick: break
        if not pick: return gs,o
        j,c,z=pick; x=n+j
        mp=lambda i: (z if i==x else i)
        ng=[]
        for q,(op,a,b) in enumerate(gs):
            if q==j: continue
            a2,b2=mp(a),mp(b); a2-= (a2>x); b2-=(b2>x); ng.append((op,a2,b2))
        no=mp(o); no-=(no>x); nc=c-(c>x)
        ng.append(('or',min(no,nc),max(no,nc))); gs,o=ng,n+len(ng)-1
    return None,None
def redirect_shrinks(gs,o):
    W=n+len(gs)
    for j in range(len(gs)):
        x=n+j; rd=[n+q for q,(op,a,b) in enumerate(gs) if x in (a,b)]
        for t in range(W):
            if t==x or (rd and t>=min(rd)): continue
            mp=lambda i: (t if i==x else i); ng=[]; ok=True
            for q,(op,a,b) in enumerate(gs):
                if q==j: continue
                a2,b2=mp(a),mp(b); a2-=(a2>x); b2-=(b2>x)
                if max(a2,b2)>=n+len(ng): ok=False
                ng.append((op,a2,b2))
            no=mp(o); no-=(no>x)
            if ok and computes(ng,no): return True
    return False
def dist_applies(gs,o):
    readers=lambda x: [q for q,(op,a,b) in enumerate(gs) if x in (a,b)]+([-1] if x==o else [])
    for j,(op,a,b) in enumerate(gs):
        if op!='and' or a<n or b<n: continue
        u,v=gs[a-n],gs[b-n]
        if u[0]!='or' or v[0]!='or': continue
        if set(u[1:])&set(v[1:]) and readers(a)==[j] and readers(b)==[j]: return True
    return False
# ---- sampling loop ----
stats={}; bad=[]
fn=f"smp_{os.getpid()}.cnf"; seen=set()
for it in range(K):
    with open(fn,"w") as f:
        f.write(f"p cnf {nv[0]} {len(cl)}\n")
        for c in cl: f.write(" ".join(map(str,c))+" 0\n")
    out=subprocess.run([CAD,"-q",f"--seed={random.randint(1,10**9)}","--shuffle=true","--shufflerandom=true","--phase="+random.choice(["true","false"]),fn],capture_output=True,text=True).stdout
    if "s SATISFIABLE" not in out: stats['unsat']=stats.get('unsat',0)+1; break
    T=set(int(x) for line in out.splitlines() if line.startswith("v") for x in line[1:].split() if int(x)>0)
    gs=[]
    for j in range(s):
        a=[k for k in range(n+j) if sel[j][0][k] in T][0]; b=[k for k in range(n+j) if sel[j][1][k] in T][0]
        gs.append(('and' if opA[j] in T else 'or',a,b))
    # block this exact circuit
    cl.append([-sel[j][0][gs[j][1]] for j in range(s)]+[-sel[j][1][gs[j][2]] for j in range(s)]+[(-opA[j] if gs[j][0]=='and' else opA[j]) for j in range(s)])
    o=n+s-1
    if not computes(gs,o): stats['wrong']=stats.get('wrong',0)+1; continue
    print(' '.join(('A' if op=='and' else 'O')+f'{a},{b}' for op,a,b in gs), flush=True); continue
    r0=readnum(gs,o); ngs,no=normalize(gs,o)
    if ngs is None: stats['loop']=stats.get('loop',0)+1; continue
    r1=readnum(ngs,no)
    key=f"{r0}->{r1}"; stats[key]=stats.get(key,0)+1
    if r1>=3:
        red=redirect_shrinks(ngs,no); dst=dist_applies(ngs,no)
        k2=f"bad:{'R0' if red else ''}{'+Rdist' if dst else ''}" if (red or dst) else "bad:NONE"
        stats[k2]=stats.get(k2,0)+1
        if not red and not dst and len(bad)<3: bad.append((ngs,no))
os.remove(fn)
pass
pass
