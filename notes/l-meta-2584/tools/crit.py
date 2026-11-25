import sys,itertools
n=int(sys.argv[1]); E=[tuple(map(int,e.split('-'))) for e in sys.argv[2].split(',')]
F=lambda r: any(r>>a&1 and r>>b&1 for a,b in E)
mins=[(1<<a)|(1<<b) for a,b in E]
zeros=[r for r in range(1<<n) if not F(r)]
maxz=[r for r in zeros if all(F(r|(1<<i)) for i in range(n) if not r>>i&1)]
print(",".join(map(str,mins+maxz)))
