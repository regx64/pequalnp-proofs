# For each topmost inner AND h of a block-form circuit (no inner AND above it), set h := 0,
# simplify (constants, copies, dead gates) and report saved = s - |C'| and the lost edges L_h.
# Local inequality tested: saved >= |L_h| + tau(L_h).
import sys, itertools
def tau(Es):
    V = sorted({x for e in Es for x in e})
    for k in range(len(V) + 1):
        for T in itertools.combinations(V, k):
            if all(a in T or b in T for a, b in Es): return k
def run(n, E, line):
    gs = [(g[0], int(g[1:].split(',')[0]), int(g[1:].split(',')[1])) for g in line.split()]
    s = len(gs); R = 1 << n
    inp = [sum(1 << r for r in range(R) if r >> i & 1) for i in range(n)]
    Tf = sum(1 << r for r in range(R) if any(r >> a & 1 and r >> b & 1 for a, b in E))
    w = list(inp)
    for op, a, b in gs: w.append(w[a] & w[b] if op == 'A' else w[a] | w[b])
    below = lambda x: x >= n and (w[x] & ~Tf) == 0
    innerA = [n + j for j in range(s) if gs[j][0] == 'A' and not below(n + j)]
    readers = {x: [n + j for j in range(s) if x in gs[j][1:]] for x in range(n + s)}
    def above(x):                     # gates reachable upward from x
        st, seen = [x], set()
        while st:
            y = st.pop()
            for r in readers[y]:
                if r not in seen: seen.add(r); st.append(r)
        return seen
    res = []
    for h in innerA:
        if any(y in innerA for y in above(h)): continue        # not topmost
        # simplify with h = 0: rep[x] = ('c', 0/1) or ('w', wire)
        rep = {}
        for x in range(n): rep[x] = ('w', x)
        alive = []
        for j, (op, a, b) in enumerate(gs):
            x = n + j
            if x == h: rep[x] = ('c', 0); continue
            ra, rb = rep[a], rep[b]
            if op == 'A':
                if ('c', 0) in (ra, rb): rep[x] = ('c', 0)
                elif ra == ('c', 1): rep[x] = rb
                elif rb == ('c', 1): rep[x] = ra
                elif ra == rb: rep[x] = ra
                else: rep[x] = ('w', x); alive.append((x, op, ra[1], rb[1]))
            else:
                if ('c', 1) in (ra, rb): rep[x] = ('c', 1)
                elif ra == ('c', 0): rep[x] = rb
                elif rb == ('c', 0): rep[x] = ra
                elif ra == rb: rep[x] = ra
                else: rep[x] = ('w', x); alive.append((x, op, ra[1], rb[1]))
        out = rep[n + s - 1]
        # count gates in the cone of the new output
        need = set(); st = [out[1]] if out[0] == 'w' else []
        amap = {x: (op, a, b) for x, op, a, b in alive}
        while st:
            y = st.pop()
            if y in amap and y not in need:
                need.add(y); st += [amap[y][1], amap[y][2]]
        saved = s - len(need)
        # value of the new output on edges
        val = {x: inp[x] for x in range(n)}
        for x, op, a, b in alive: val[x] = val[a] & val[b] if op == 'A' else val[a] | val[b]
        ov = 0 if out == ('c', 0) else (R * [1] and ((1 << R) - 1) if out == ('c', 1) else val[out[1]])
        lost = [(a, b) for a, b in E if not ov >> ((1 << a) | (1 << b)) & 1]
        res.append((h, saved, len(lost), tau(lost), saved - len(lost) - tau(lost)))
    return res
if __name__ == '__main__':
    n = int(sys.argv[1]); E = [tuple(map(int, e.split('-'))) for e in sys.argv[2].split(',')]
    worst = None; cnt = 0
    for line in sys.stdin:
        if not line.startswith("CIRCUIT"): continue
        for h, sv, l, tl, m in run(n, E, line[8:].strip()):
            cnt += 1
            if worst is None or m < worst[0]: worst = (m, line.strip(), h, sv, l, tl)
    print("topmost inner ANDs examined:", cnt, " min(saved - |L| - tau(L)) =", None if worst is None else worst[0])
    if worst: print("  worst:", worst[1:])
