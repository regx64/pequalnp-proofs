# Rewriting system on AND/OR fan-in-2 circuits for an edge function; no move increases size.
#   lift      : OR gate outside the top OR-tree with an operand below F -> delete it, OR that
#               operand onto the output                                   (size kept)
#   redirect  : delete a gate, send its reads to an existing earlier wire  (size - 1)
#   distrib   : AND(OR(s,A), OR(s,B)), both ORs read only there -> OR(s, AND(A,B))  (size - 1)
#   absorb    : g = AND(u, v); an OR o on a private OR-path from v has operand h = AND(u, t)
#               -> o reads t instead of h                                 (size kept)
# usage: python3 rewrite.py n edges   (circuits on stdin, one per line: A0,1 O2,5 ...)
import sys

class Inst:
    def __init__(self, n, E):
        self.n, self.E = n, E
        R = 1 << n
        self.inp = [sum(1 << r for r in range(R) if r >> i & 1) for i in range(n)]
        self.T = sum(1 << r for r in range(R) if any(r >> a & 1 and r >> b & 1 for a, b in E))

    def ev(self, gs):
        w = list(self.inp)
        for op, a, b in gs:
            w.append(w[a] & w[b] if op == 'A' else w[a] | w[b])
        return w

    def ok(self, gs, o):
        w = self.ev(gs)
        return o < len(w) and w[o] == self.T

    def read(self, gs, o, cap=4):
        worst = 0
        for a, b in self.E:
            R = [set() for _ in range(self.n + len(gs))]
            R[a] = {(1, 0)}; R[b] = {(0, 1)}
            for j, (op, p, q) in enumerate(gs):
                R[self.n + j] = R[p] | R[q] if op == 'O' else \
                    {(min(u[0] + v[0], cap), min(u[1] + v[1], cap)) for u in R[p] for v in R[q]}
            worst = max(worst, min((max(v) for v in R[o]), default=99))
        return worst

def readers(gs, n, x, o):
    r = [n + q for q, (op, a, b) in enumerate(gs) if x in (a, b)]
    return r + (['OUT'] if x == o else [])

def delete_gate(gs, n, j, t, o):
    """Delete gate j (wire n+j), sending its reads (and the output) to wire t."""
    x = n + j
    mp = lambda i: (t if i == x else i)
    ng = []
    for q, (op, a, b) in enumerate(gs):
        if q == j: continue
        a2, b2 = mp(a), mp(b)
        a2 -= (a2 > x); b2 -= (b2 > x)
        if max(a2, b2) >= n + len(ng): return None, None
        ng.append((op, a2, b2))
    no = mp(o); no -= (no > x)
    return ng, no

def lift_once(I, gs, o):
    n = I.n; w = I.ev(gs)
    top = set(); st = [o] if o >= n and gs[o - n][0] == 'O' else []
    while st:
        x = st.pop()
        if x in top: continue
        top.add(x); _, a, b = gs[x - n]
        for c in (a, b):
            if c >= n and gs[c - n][0] == 'O': st.append(c)
    for j, (op, a, b) in enumerate(gs):
        x = n + j
        if x in top or x == o or op != 'O': continue
        for c, z in ((a, b), (b, a)):
            if w[c] and (w[c] & ~I.T) == 0:
                ng, no = delete_gate(gs, n, j, z, o)
                if ng is None: continue
                nc = c - (c > x)
                ng.append(('O', min(no, nc), max(no, nc)))
                return ng, n + len(ng) - 1
    return None

def redirect(I, gs, o):
    n = I.n; W = n + len(gs)
    for j in range(len(gs)):
        x = n + j
        rd = [r for r in readers(gs, n, x, o) if r != 'OUT']
        for t in range(W):
            if t == x or (rd and t >= min(rd)): continue
            ng, no = delete_gate(gs, n, j, t, o)
            if ng is not None and I.ok(ng, no): return ng, no
    return None

def distrib(I, gs, o):
    n = I.n
    for j, (op, a, b) in enumerate(gs):
        if op != 'A' or a < n or b < n: continue
        u, v = gs[a - n], gs[b - n]
        if u[0] != 'O' or v[0] != 'O': continue
        if readers(gs, n, a, o) != [n + j] or readers(gs, n, b, o) != [n + j]: continue
        common = set(u[1:]) & set(v[1:])
        if not common: continue
        s = min(common); A = u[1] if u[2] == s else u[2]; B = v[1] if v[2] == s else v[2]
        # rebuild: gate a := AND(A, B), gate b := OR(s, a), gate j := copy of b (redirect reads of j to b)
        ng = list(gs)
        ng[a - n] = ('A', min(A, B), max(A, B))
        if max(A, B) >= a: continue
        ng[b - n] = ('O', min(s, a), max(s, a))
        if max(s, a) >= b: continue
        res = delete_gate(ng, n, j, b, o)
        if res[0] is not None and I.ok(*res): return res
    return None

def absorb(I, gs, o):
    n = I.n
    for j, (op, a, b) in enumerate(gs):
        if op != 'A': continue
        for u, v in ((a, b), (b, a)):
            # private OR-path from v: v read only by g, each further OR read only by its parent
            if v < n or gs[v - n][0] != 'O' or readers(gs, n, v, o) != [n + j]: continue
            st = [v]
            while st:
                x = st.pop(); _, p, q = gs[x - n]
                for h in (p, q):
                    if h >= n and gs[h - n][0] == 'A' and u in gs[h - n][1:]:
                        _, h1, h2 = gs[h - n]
                        t = h2 if h1 == u else h1
                        ng = list(gs)
                        op_, p_, q_ = ng[x - n]
                        p2, q2 = (t, q_) if p_ == h else (p_, t)
                        ng[x - n] = ('O', min(p2, q2), max(p2, q2))
                        if I.ok(ng, o) and ng != gs: return ng, o
                    if h >= n and gs[h - n][0] == 'O' and readers(gs, n, h, o) == [x]:
                        st.append(h)
    return None

def drive(I, gs, o, steps=300):
    seen = set(); trace = []
    for _ in range(steps):
        while True:
            r = lift_once(I, gs, o)
            if r is None: break
            gs, o = r; trace.append('lift')
        key = (tuple(gs), o)
        if key in seen: return 'loop', gs, o, trace
        seen.add(key)
        if I.read(gs, o) <= 2: return 'read2', gs, o, trace
        for name, mv in (('redirect', redirect), ('distrib', distrib), ('absorb', absorb)):
            r = mv(I, gs, o)
            if r is not None:
                gs, o = r; trace.append(name); break
        else:
            return 'stuck', gs, o, trace
    return 'steps', gs, o, trace

def parse(line):
    return [(t[0], int(t[1:].split(',')[0]), int(t[1:].split(',')[1])) for t in line.split()]

if __name__ == '__main__':
    n = int(sys.argv[1]); E = [tuple(map(int, e.split('-'))) for e in sys.argv[2].split(',')]
    I = Inst(n, E)
    from collections import Counter
    out = Counter(); moves = Counter(); stuck = []; total = 0; bad = 0
    for line in sys.stdin:
        line = line.strip()
        if not line: continue
        gs = parse(line); o = n + len(gs) - 1; total += 1
        assert I.ok(gs, o)
        g2, o2 = gs, o
        while True:
            r = lift_once(I, g2, o2)
            if r is None: break
            g2, o2 = r
        if I.read(g2, o2) <= 2: continue
        bad += 1
        res, g3, o3, tr = drive(I, gs, o)
        out[res] += 1
        for m in tr: moves[m] += 1
        if res == 'read2': assert I.ok(g3, o3) and len(g3) <= len(gs)
        if res != 'read2' and len(stuck) < 3: stuck.append((res, line, g3, o3))
    print(f"circuits={total} lift-normalized read>=3: {bad} outcomes={dict(out)} moves={dict(moves)}")
    for res, line, g3, o3 in stuck:
        print("  ", res, "start:", line)
        print("      end:", ' '.join(f'{op}{a},{b}' for op, a, b in g3), "out", o3, "read", I.read(g3, o3))
