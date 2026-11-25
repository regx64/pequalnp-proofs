# For every lift-normalized read>=3 circuit, find the redirect move and classify it:
#   kind of deleted gate, and how the replacement wire t relates to it.
import sys
sys.path.insert(0,'.')
from rewrite import Inst, lift_once, readers, delete_gate, parse
from collections import Counter
n=int(sys.argv[1]); E=[tuple(map(int,e.split('-'))) for e in sys.argv[2].split(',')]
I=Inst(n,E); C=Counter(); ex={}
for line in sys.stdin:
    gs=parse(line.strip()); o=n+len(gs)-1
    while True:
        r=lift_once(I,gs,o)
        if r is None: break
        gs,o=r
    if I.read(gs,o)<=2: continue
    w=I.ev(gs); found=None
    for j,(op,a,b) in enumerate(gs):
        x=n+j; rd=[r for r in readers(gs,n,x,o) if r!='OUT']
        for t in range(n+len(gs)):
            if t==x or (rd and t>=min(rd)): continue
            ng,no=delete_gate(gs,n,j,t,o)
            if ng is not None and I.ok(ng,no):
                rel = 'operand' if t in (a,b) else ('input' if t<n else 'other-gate')
                fx, ft = w[x], w[t]
                cmp = 'equal' if fx==ft else ('t<x' if ft & ~fx==0 else ('t>x' if fx & ~ft==0 else 'incomparable'))
                # what reads x
                rops=''.join(sorted(gs[r-n][0] for r in rd)) + ('+OUT' if x==o else '')
                found=(op, rel, cmp, rops); break
        if found: break
    C[found]+=1
    if found not in ex: ex[found]=line.strip()
for k,v in C.most_common(): print(v, k, " e.g.", ex[k])
