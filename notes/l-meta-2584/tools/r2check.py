# Check lemma R2 on data: circuits satisfying (TF)+(S)+(J1) must be read-2.
import sys
sys.path.insert(0,'.')
from rewrite import Inst, parse
from collections import Counter
n=int(sys.argv[1]); E=[tuple(map(int,e.split('-'))) for e in sys.argv[2].split(',')]
I=Inst(n,E); C=Counter()
singles=[1<<sum(1<<r for r in range(1<<n) if r==(1<<i)).bit_length()-1 for i in range(n)]
def props(gs,o):
    w=I.ev(gs); N=len(gs)
    isand=lambda x: x>=n and gs[x-n][0]=='A'
    below=lambda x: (w[x] & ~I.T)==0
    # cones
    cone=[set() for _ in range(N)]
    for j,(op,a,b) in enumerate(gs):
        for c in (a,b):
            if c>=n: cone[j]|={c}|cone[c-n]
    TF=all(not(isand(i) and below(i)) for j in range(N) if gs[j][0]=='A' for i in cone[j])
    S=all(all(not (w[n+j]>>(1<<i) & 1) for i in range(n)) for j in range(N) if gs[j][0]=='A')
    def orclosure_has_and(x):
        st=[x]; seen=set()
        while st:
            y=st.pop()
            if y in seen: continue
            seen.add(y)
            if y<n: continue
            if gs[y-n][0]=='A': return True
            st+= [gs[y-n][1],gs[y-n][2]]
        return False
    J1=all(not orclosure_has_and(c) for j,(op,a,b) in enumerate(gs) if op=='A' and not below(n+j) for c in (a,b))
    return TF,S,J1
for line in sys.stdin:
    gs=parse(line.strip()); o=n+len(gs)-1
    TF,S,J1=props(gs,o); r=I.read(gs,o)
    C[(TF,S,J1, 'read<=2' if r<=2 else 'read>=3')]+=1
for k,v in sorted(C.items()): print(v,k)
bad=[k for k in C if k[0] and k[1] and k[2] and k[3]=='read>=3']
print("R2 VIOLATIONS:", sum(C[k] for k in bad))
