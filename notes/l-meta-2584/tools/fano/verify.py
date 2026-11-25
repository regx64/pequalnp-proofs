# Independently verify a decoded circuit: AO2 model, exact function on all 2^n inputs, size, and
# (optionally) the WLOG properties C1, C2, C4; also its read number.
import sys, itertools
sys.path.insert(0, '..')
n = int(sys.argv[1]); E = [tuple(map(int, e.split('-'))) for e in sys.argv[2].split(',')]; line = sys.argv[3]
gs = [(t[0], int(t[1:].split(',')[0]), int(t[1:].split(',')[1])) for t in line.split()]
adj = set(E) | {(b, a) for a, b in E}
s = len(gs); o = n + s - 1
assert all(op in 'AO' for op, a, b in gs), "op"
assert all(a < n + j and b < n + j for j, (op, a, b) in enumerate(gs)), "reads back"
R = 1 << n
inp = [sum(1 << r for r in range(R) if r >> i & 1) for i in range(n)]
w = list(inp)
for op, a, b in gs: w.append(w[a] & w[b] if op == 'A' else w[a] | w[b])
T = sum(1 << r for r in range(R) if any(r >> a & 1 and r >> b & 1 for a, b in E))
print("size", s, "| computes F on all", R, "inputs:", w[o] == T)
below = lambda x: (w[x] & ~T) == 0
cone = [set() for _ in range(s)]
for j, (op, a, b) in enumerate(gs):
    for c in (a, b):
        if c >= n: cone[j] |= {c - n} | cone[c - n]
C1 = all(not (gs[i][0] == 'A' and below(n + i)) for j in range(s) if gs[j][0] == 'A' for i in cone[j])
readers = lambda j: [k for k in range(s) if n + j in gs[k][1:]]
C2 = all(len(readers(j)) == 1 and gs[readers(j)[0]][0] == 'O' and below(n + readers(j)[0])
         for j in range(s - 1) if below(n + j))
def orIn(x):
    if x < n: return {x}
    op, a, b = gs[x - n]
    if op == 'A': return set()
    return orIn(a) | orIn(b)
C4 = True
for a in range(s):
    if gs[a][0] == 'A' and below(n + a):
        s0, s1 = orIn(gs[a][1]), orIn(gs[a][2])
        C4 &= not (s0 & s1) and all((u, v) in adj for u in s0 for v in s1) and (len(s0) <= 1 or len(s1) <= 1)
print("C1 TopForm:", C1, "| C2 (L_meta_1498 a):", C2, "| C4 (L_meta_1490 a):", C4)
from readk import analyze
ok, rd = analyze(n, [('and' if op == 'A' else 'or', (a, b)) for op, a, b in gs], o, E)
print("read number:", max(rd.values()), "per edge:", rd)
