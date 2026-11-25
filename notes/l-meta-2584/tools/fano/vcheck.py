# Lemma V terms for a block-form circuit: E_real, E_virt, t0, X' (inner ORs with an empty-orIn
# operand), X (inner ORs that are not real-merging gates in the OR-cone of a side operand of a top
# with a center), mAND (inner ANDs), tau(E_virt); and the slack s - (E + tau - 1).
import sys, itertools
def tau(Es):
    V = sorted({x for e in Es for x in e})
    for k in range(len(V) + 1):
        for T in itertools.combinations(V, k):
            if all(a in T or b in T for a, b in Es): return k
def analyze(n, E, line, TAU):
    gs = [(g[0], int(g[1:].split(',')[0]), int(g[1:].split(',')[1])) for g in line.split()]
    adj = set(E) | {(b, a) for a, b in E}
    R = 1 << n
    inp = [sum(1 << r for r in range(R) if r >> i & 1) for i in range(n)]
    w = list(inp)
    for op, a, b in gs: w.append(w[a] & w[b] if op == 'A' else w[a] | w[b])
    Tf = sum(1 << r for r in range(R) if any(r >> a & 1 and r >> b & 1 for a, b in E))
    assert w[-1] == Tf
    below = lambda x: x >= n and (w[x] & ~Tf) == 0
    s = len(gs)
    tops = [n + j for j in range(s) if gs[j][0] == 'A' and below(n + j)]
    inner = [n + j for j in range(s) if not below(n + j)]
    def orIn(x):
        if x < n: return {x}
        op, a, b = gs[x - n]
        return set() if op == 'A' else orIn(a) | orIn(b)
    def orcone(x):          # inner OR gates reachable from x through OR gates (x included)
        if x < n or gs[x - n][0] == 'A': return set()
        _, a, b = gs[x - n]
        return {x} | orcone(a) | orcone(b)
    Ereal = set(); t0 = 0; centers = {}
    for T in tops:
        _, a, b = gs[T - n]
        A, B = orIn(a), orIn(b)
        if not A or not B: t0 += 1; continue
        for u in A:
            for v in B: Ereal.add((min(u, v), max(u, v)))
        if len(A) == 1: c, side = next(iter(A)), b
        else: c, side = next(iter(B)), a
        centers.setdefault(c, []).append(side)
    counted = set()
    for c, sides in centers.items():
        for sd in sides:
            for g in orcone(sd):
                _, p, q = gs[g - n]
                if orIn(p) and orIn(q): counted.add(g)
    innerOR = [x for x in inner if gs[x - n][0] == 'O']
    mAND = sum(1 for x in inner if gs[x - n][0] == 'A')
    Xp = sum(1 for x in innerOR if not orIn(gs[x - n][1]) or not orIn(gs[x - n][2]))
    X = sum(1 for x in innerOR if x not in counted)
    Ev = [tuple(sorted(e)) for e in E if tuple(sorted(e)) not in Ereal]
    tv = tau(Ev)
    pay = 2 * t0 + X + mAND; payp = 2 * t0 + Xp + mAND; virt = len(Ev) + tv
    return dict(s=s, slack=s - (len(E) + TAU - 1), t=len(tops), t0=t0, mAND=mAND, X=X, Xp=Xp,
                Evirt=len(Ev), tauV=tv, payX=pay - virt, payXp=payp - virt)
if __name__ == '__main__':
    n = int(sys.argv[1]); E = [tuple(map(int, e.split('-'))) for e in sys.argv[2].split(',')]; TAU = int(sys.argv[3])
    for line in sys.stdin:
        if line.startswith("CIRCUIT"): print(analyze(n, E, line[8:].strip(), TAU))
