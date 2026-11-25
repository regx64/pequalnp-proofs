# Block form search (v4: exact orIn, --lemmaV TAU adds the Lemma V cardinality constraint; v3: --extra adds implied rows, --fix FILE pins a circuit): AO2 circuits of exactly s gates with t tops, for an edge function of a 4-cycle-free
# graph, in the normal form that a least TopForm circuit can be brought to.
#
# usage: python3 topsat2.py s t n edges [--timeout SEC] [--proof FILE]
#
# Normal form (each step keeps size, function, IsLeastAO and TopForm, so L_meta_1498 and
# L_meta_1490 apply again to the result):
#   * L_meta_5779: a least circuit can be taken in TopForm.
#   * L_meta_1498 (a) + TopForm: the gates below F form a binary tree of OR gates (orT) whose leaves
#     are the tops (AND gates below F); a top reads no gate below F (its reader would be an AND);
#     a gate not below F reads no gate below F (the reader of a below-F gate is an OR below F).
#     So the order [inner gates (not below F)] [tops] [orT] is topological.
#   * The orT tree over the t tops can be replaced by the chain T1 | T2 | ... | Tt (t-1 gates):
#     same size and function, the tops and every other gate unchanged.
#   * The tops can be listed in strictly increasing order of their (first, second) operands
#     (two equal tops would make one deletable).
#   * Inner gates: two different earlier wires, first < second, every inner gate read by a later
#     inner gate or a top, greedy topological order inside the inner block, and (by definition of
#     the block) every inner gate is true on some maximal zero of F (not below F).
#   * L_meta_1490 (a), for every top: sides (orIn of the operands) disjoint, every cross pair an
#     edge, one side with at most one input. orIn is forced from below (see topsat.py).
# Size: m inner gates + t tops + (t - 1) chain ORs = s, so m = s - 2t + 1.
import sys, itertools, subprocess, os, time

s, t, n = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
E = [tuple(map(int, e.split('-'))) for e in sys.argv[4].split(',')]
tmo = int(sys.argv[sys.argv.index('--timeout') + 1]) if '--timeout' in sys.argv else 0
proof = sys.argv[sys.argv.index('--proof') + 1] if '--proof' in sys.argv else None
m = s - 2 * t + 1
assert m >= 0 and t >= 1
adj = set(E) | {(b, a) for a, b in E}
Fr = lambda r: any(r >> a & 1 and r >> b & 1 for a, b in E)
mins = sorted({(1 << a) | (1 << b) for a, b in E})
maxz = [r for r in range(1 << n) if not Fr(r) and all(Fr(r | (1 << i)) for i in range(n) if not r >> i & 1)]
rows = mins + maxz
EXTRA = '--extra' in sys.argv
if EXTRA:
    sing = [1 << i for i in range(n)]
    nonedge = [(1 << a) | (1 << b) for a in range(n) for b in range(a + 1, n) if (a, b) not in adj]
    rows = rows + sing + nonedge

cl = []; nv = [0]
def new():
    nv[0] += 1; return nv[0]
def exactly_one(vs):
    cl.append(list(vs)); cl.extend([[-a, -b] for a, b in itertools.combinations(vs, 2)])
def at_most_one(vs, guard=()):
    cl.extend([list(guard) + [-a, -b] for a, b in itertools.combinations(vs, 2)])

W = n + m                                        # wires a top may read
# inner gates
sel = [[[new() for k in range(n + j)] for e in range(2)] for j in range(m)]
isA = [new() for j in range(m)]
val = [{r: new() for r in rows} for j in range(m)]
va = [[{r: new() for r in rows} for e in range(2)] for j in range(m)]
def wire(k, r): return ((r >> k) & 1 == 1) if k < n else val[k - n][r]
def link_sources(selv, vav, nw):
    for e in range(2):
        for r in rows:
            v = vav[e][r]
            for k in range(nw):
                w = wire(k, r)
                if isinstance(w, bool): cl.append([-selv[e][k], v if w else -v])
                else: cl.append([-selv[e][k], -w, v]); cl.append([-selv[e][k], w, -v])
for j in range(m):
    for e in range(2): exactly_one(sel[j][e])
    for ka in range(n + j):
        for kb in range(ka + 1): cl.append([-sel[j][0][ka], -sel[j][1][kb]])
    link_sources(sel[j], va[j], n + j)
    for r in rows:
        g, a, b = val[j][r], va[j][0][r], va[j][1][r]
        cl += [[-isA[j], -g, a], [-isA[j], -g, b], [-isA[j], g, -a, -b],
               [isA[j], g, -a], [isA[j], g, -b], [isA[j], -g, a, b]]
    cl.append([val[j][r] for r in maxz])          # inner gate not below F
# tops
tsel = [[[new() for k in range(W)] for e in range(2)] for k in range(t)]
tval = [{r: new() for r in rows} for k in range(t)]
tva = [[{r: new() for r in rows} for e in range(2)] for k in range(t)]
for k in range(t):
    for e in range(2): exactly_one(tsel[k][e])
    for ka in range(W):
        for kb in range(ka + 1): cl.append([-tsel[k][0][ka], -tsel[k][1][kb]])
    link_sources(tsel[k], tva[k], W)
    for r in rows:
        g, a, b = tval[k][r], tva[k][0][r], tva[k][1][r]
        cl += [[-g, a], [-g, b], [g, -a, -b]]
# F = OR of the tops on every row
for r in rows:
    if r in mins: cl.append([tval[k][r] for k in range(t)])
    else: cl.extend([[-tval[k][r]] for k in range(t)])
# inner gates used; greedy order inside the inner block
def reads_inner(j):     # literals saying wire n+j is read by a later inner gate or a top
    lits = [sel[q][e][n + j] for q in range(j + 1, m) for e in range(2)]
    lits += [tsel[k][e][n + j] for k in range(t) for e in range(2)]
    return lits
for j in range(m): cl.append(reads_inner(j))
for j in range(m - 1):
    for k in range(n + j):
        for k2 in range(k):
            cl.append([-sel[j][0][k], -sel[j + 1][0][k2], sel[j + 1][0][n + j], sel[j + 1][1][n + j]])
# tops strictly increasing in (first, second)
for k in range(t - 1):
    for x in range(W):
        for y in range(x): cl.append([-tsel[k][0][x], -tsel[k + 1][0][y]])
        for u in range(W):
            for v in range(u + 1):
                cl.append([-tsel[k][0][x], -tsel[k + 1][0][x], -tsel[k][1][u], -tsel[k + 1][1][v]])
# orIn of inner wires and the sides of the tops, encoded EXACTLY (both directions):
#   I[j][i] <-> gate j is an OR and input i is reachable from it through OR gates only.
I = [[new() for i in range(n)] for j in range(m)]
for j in range(m):
    for i in range(n):
        # reach[e]: operand e of gate j is input i, or a gate q with I[q][i]
        reach = []
        for e in range(2):
            rv = new(); reach.append(rv)
            parts = [sel[j][e][i]]
            for q in range(j):
                pv = new(); parts.append(pv)
                cl += [[-pv, sel[j][e][n + q]], [-pv, I[q][i]], [pv, -sel[j][e][n + q], -I[q][i]]]
            cl.append([-rv] + parts); cl.extend([[rv, -p] for p in parts])
        cl.append([-I[j][i], -isA[j]])
        cl.append([-I[j][i]] + reach)
        for rv in reach: cl.append([I[j][i], isA[j], -rv])
emp = []
for j in range(m):                       # emp[j] <-> orIn of gate j is empty
    ev = new(); emp.append(ev)
    cl.append([ev] + I[j]); cl.extend([[-ev, -I[j][i]] for i in range(n)])
SD = []; ZK = []
for k in range(t):
    Sd = [[new() for i in range(n)] for e in range(2)]
    SD.append(Sd)
    for e in range(2):
        for i in range(n):
            parts = [tsel[k][e][i]]
            for q in range(m):
                pv = new(); parts.append(pv)
                cl += [[-pv, tsel[k][e][n + q]], [-pv, I[q][i]], [pv, -tsel[k][e][n + q], -I[q][i]]]
            cl.append([-Sd[e][i]] + parts); cl.extend([[Sd[e][i], -p] for p in parts])
    for i in range(n): cl.append([-Sd[0][i], -Sd[1][i]])
    for u in range(n):
        for v in range(n):
            if u != v and (u, v) not in adj: cl.append([-Sd[0][u], -Sd[1][v]])
    z = new(); at_most_one(Sd[0], guard=[-z]); at_most_one(Sd[1], guard=[z]); ZK.append(z)
# Lemma V (virtual-edge accounting, proved in the notes):
#   s >= (E + tau - 1) + 2 t0 + X' + mAND - |Evirt| - tau(Evirt)
# with Evirt = edges in no real star A_k x B_k, t0 = tops whose real star is empty, X' = inner OR
# gates with an operand of empty orIn, mAND = inner AND gates.  Using tau(Evirt) <= |Evirt|:
#   2|Evirt| - 2 t0 - X' - mAND >= (E + tau - 1) - s.
if '--lemmaV' in sys.argv:
    TAU = int(sys.argv[sys.argv.index('--lemmaV') + 1])
    D = len(E) + TAU - 1 - s
    real = {}
    for (a, b) in E:
        lits = []
        for k in range(t):
            for (u, v) in ((a, b), (b, a)):
                pv = new(); lits.append(pv)
                cl += [[-pv, SD[k][0][u]], [-pv, SD[k][1][v]], [pv, -SD[k][0][u], -SD[k][1][v]]]
        rv = new(); real[(a, b)] = rv
        cl.append([-rv] + lits); cl.extend([[rv, -p] for p in lits])
    t0 = []
    for k in range(t):              # t0_k <-> side 0 empty or side 1 empty
        e0, e1, tv = new(), new(), new()
        for ev, e in ((e0, 0), (e1, 1)):
            cl.append([ev] + SD[k][e]); cl.extend([[-ev, -SD[k][e][i]] for i in range(n)])
        cl += [[-tv, e0, e1], [tv, -e0], [tv, -e1]]
        t0.append(tv)
    nm = []
    for j in range(m):              # nm_j <-> OR gate with an operand gate of empty orIn
        ops = []
        for e in range(2):
            ov = new(); ops.append(ov)
            parts = []
            for q in range(j):
                pv = new(); parts.append(pv)
                cl += [[-pv, sel[j][e][n + q]], [-pv, emp[q]], [pv, -sel[j][e][n + q], -emp[q]]]
            cl.append([-ov] + parts); cl.extend([[ov, -p] for p in parts])
        nv_ = new(); nm.append(nv_)
        cl += [[-nv_, -isA[j]], [-nv_] + ops] + [[nv_, isA[j], -o] for o in ops]
    if '--exactX' in sys.argv:
        # side_is[k][g]: top k has a center and its side operand is gate g (z_k: center on side 0)
        rd = {}
        for g in range(m):
            for g2 in range(g + 1, m):
                rv = new(); rd[(g2, g)] = rv
                cl += [[-rv, sel[g2][0][n + g], sel[g2][1][n + g]], [rv, -sel[g2][0][n + g]], [rv, -sel[g2][1][n + g]]]
        anyoc = [[] for g in range(m)]
        for k in range(t):
            oc = [None] * m
            for g in reversed(range(m)):
                si = new()      # side_is
                p1, p2 = new(), new()
                cl += [[-p1, ZK[k]], [-p1, tsel[k][1][n + g]], [p1, -ZK[k], -tsel[k][1][n + g]]]
                cl += [[-p2, -ZK[k]], [-p2, tsel[k][0][n + g]], [p2, ZK[k], -tsel[k][0][n + g]]]
                cl += [[-si, -t0[k]], [-si, p1, p2], [si, t0[k], -p1], [si, t0[k], -p2]]
                parts = [si]
                for g2 in range(g + 1, m):
                    pv = new(); parts.append(pv)
                    cl += [[-pv, oc[g2]], [-pv, -isA[g2]], [-pv, rd[(g2, g)]], [pv, -oc[g2], isA[g2], -rd[(g2, g)]]]
                # the OR-cone stops at AND gates: oc[g] <-> g is an OR and (side operand or read by a cone OR)
                rv_ = new()
                cl.append([-rv_] + parts); cl.extend([[rv_, -p] for p in parts])
                ov = new(); oc[g] = ov
                cl += [[-ov, -isA[g]], [-ov, rv_], [ov, isA[g], -rv_]]
                anyoc[g].append(ov)
        Xg = []
        for g in range(m):
            # nonempty orIn of operand e of gate g: operand is an input, or a gate q with not emp[q]
            ne = []
            for e in range(2):
                nev = new(); ne.append(nev)
                parts = [sel[g][e][i] for i in range(n)]
                for q in range(g):
                    pv = new(); parts.append(pv)
                    cl += [[-pv, sel[g][e][n + q]], [-pv, -emp[q]], [pv, -sel[g][e][n + q], emp[q]]]
                cl.append([-nev] + parts); cl.extend([[nev, -p] for p in parts])
            cnt = new()
            cl += [[-cnt, -isA[g]], [-cnt, ne[0]], [-cnt, ne[1]], [-cnt] + anyoc[g]]
            cl += [[cnt, isA[g], -ne[0], -ne[1], -o] for o in anyoc[g]]
            xg = new(); Xg.append(xg)
            cl += [[-xg, -isA[g]], [-xg, -cnt], [xg, isA[g], cnt]]
        nm = Xg
    if '--violV' in sys.argv:
        # search for a V+ violation: |Evirt| >= 2 t0 + X + mAND with Evirt nonempty (then
        # |Evirt| + tau(Evirt) > 2 t0 + X + mAND).  Replaces the Lemma V constraint.
        cl.append([-real[e] for e in real])
        lits = [-real[e] for e in real] + [-x for x in t0] * 2 + [-x for x in nm] + [-isA[j] for j in range(m)]
        K = 2 * t + m + m
        D = -10 ** 9
    # sum of positive literals >= K, with weights by repetition
    if '--violV' not in sys.argv:
        lits = [-real[e] for e in real] * 2 + [-x for x in t0] * 2 + [-x for x in nm] + [-isA[j] for j in range(m)]
        K = D + 2 * t + m + m
    # sequential counter: at most (N - K) of the negations are true
    neg = [-l for l in lits]; N = len(neg); kmax = N - K
    DBG = dict(real=real, t0=t0, nm=nm, K=K, N=N)
    if '--debugV' in sys.argv: kmax = N
    if kmax < 0: cl.append([])
    elif kmax == 0: cl.extend([[-x] for x in neg])
    elif kmax < N:
        R = [[new() for c in range(kmax)] for i in range(N)]      # R[i][c]: >= c+1 of neg[0..i] true
        for i in range(N):
            x = neg[i]
            cl.append([-x, R[i][0]])
            if i > 0:
                for c in range(kmax):
                    cl.append([-R[i - 1][c], R[i][c]])
                    if c > 0: cl.append([-x, -R[i - 1][c - 1], R[i][c]])
                cl.append([-x, -R[i - 1][kmax - 1]])
            # R[i][c] means: at least c+1 of neg[0..i] are true (forced from below)
if '--minand' in sys.argv:            # at least K inner AND gates
    KM = int(sys.argv[sys.argv.index('--minand') + 1])
    ys = [-isA[j] for j in range(m)]       # at most m - KM inner gates are OR
    KO = m - KM
    if KO < 0: cl.append([])
    elif KO == 0: cl.extend([[-y] for y in ys])
    elif KO < len(ys):
        Rq = [[new() for c in range(KO)] for i in range(len(ys))]
        for i, y in enumerate(ys):
            cl.append([-y, Rq[i][0]])
            if i > 0:
                for c in range(KO):
                    cl.append([-Rq[i - 1][c], Rq[i][c]])
                    if c > 0: cl.append([-y, -Rq[i - 1][c - 1], Rq[i][c]])
                cl.append([-y, -Rq[i - 1][KO - 1]])
if '--maxand' in sys.argv:            # at most K inner AND gates (partial search, not a WLOG)
    KA = int(sys.argv[sys.argv.index('--maxand') + 1])
    xs = [isA[j] for j in range(m)]
    if KA == 0: cl.extend([[-x] for x in xs])
    elif KA < len(xs):
        Rq = [[new() for c in range(KA)] for i in range(len(xs))]
        for i, x in enumerate(xs):
            cl.append([-x, Rq[i][0]])
            if i > 0:
                for c in range(KA):
                    cl.append([-Rq[i - 1][c], Rq[i][c]])
                    if c > 0: cl.append([-x, -Rq[i - 1][c - 1], Rq[i][c]])
                cl.append([-x, -Rq[i - 1][KA - 1]])
if '--innerand' in sys.argv:          # at least one inner gate (not below F) is an AND
    cl.append([isA[j] for j in range(m)])
if '--fix' in sys.argv:
    gs = [(g[0], int(g[1:].split(',')[0]), int(g[1:].split(',')[1])) for g in open(sys.argv[sys.argv.index('--fix') + 1]).read().split()]
    assert len(gs) == s
    for j in range(m):
        op, a, b = gs[j]; cl += [[sel[j][0][a]], [sel[j][1][b]], [isA[j] if op == 'A' else -isA[j]]]
    for k in range(t):
        op, a, b = gs[m + k]; assert op == 'A'; cl += [[tsel[k][0][a]], [tsel[k][1][b]]]
fn = f"blk_s{s}_t{t}_{os.getpid()}.cnf"
with open(fn, "w") as f:
    f.write(f"p cnf {nv[0]} {len(cl)}\n")
    for c in cl: f.write(" ".join(map(str, c)) + " 0\n")
cad = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical")
def decode(T):
    gs = []
    for j in range(m):
        a = [k for k in range(n + j) if sel[j][0][k] in T][0]; b = [k for k in range(n + j) if sel[j][1][k] in T][0]
        gs.append(('A' if isA[j] in T else 'O') + f"{a},{b}")
    for k in range(t):
        a = [x for x in range(W) if tsel[k][0][x] in T][0]; b = [x for x in range(W) if tsel[k][1][x] in T][0]
        gs.append(f"A{a},{b}")
    top0 = n + m
    if t >= 2:
        gs.append(f"O{top0},{top0 + 1}")
        for k in range(2, t): gs.append(f"O{n + m + t + k - 2},{top0 + k}")
    return gs
def blocking(T):
    lits = []
    for j in range(m):
        for e in range(2): lits += [-v for v in sel[j][e] if v in T]
        lits.append(-isA[j] if isA[j] in T else isA[j])
    for k in range(t):
        for e in range(2): lits += [-v for v in tsel[k][e] if v in T]
    return lits
NENUM = int(sys.argv[sys.argv.index('--enum') + 1]) if '--enum' in sys.argv else 1
found = 0; t0 = time.time(); verdict = "UNKNOWN"
while True:
    with open(fn, "w") as f:
        f.write(f"p cnf {nv[0]} {len(cl)}\n")
        for c in cl: f.write(" ".join(map(str, c)) + " 0\n")
    cmd = [cad, "-q"] + (["-t", str(tmo)] if tmo else []) + [fn] + ([proof] if proof else [])
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    v = "SAT" if "s SATISFIABLE" in out else ("UNSAT" if "s UNSATISFIABLE" in out else "UNKNOWN")
    if v != "SAT":
        if found == 0: verdict = v
        else: verdict = f"SAT ({found} circuits, enumeration then {v})"
        break
    T = set(int(x) for line in out.splitlines() if line.startswith("v") for x in line[1:].split() if int(x) > 0)
    found += 1; verdict = "SAT"
    if '--debugV' in sys.argv:
        print("real", {e: (DBG['real'][e] in T) for e in DBG['real']}, "t0", [x in T for x in DBG['t0']],
              "X", [x in T for x in DBG['nm']], "isA", [isA[j] in T for j in range(m)], "K", DBG['K'], "N", DBG['N'],
              "sumpos", sum(1 for l in lits if (l > 0 and l in T) or (l < 0 and -l not in T)))
    print("CIRCUIT", " ".join(decode(T)), flush=True)
    if found >= NENUM: break
    cl.append(blocking(T))
dt = time.time() - t0
print(f"block s={s} t={t} m={m} n={n} E={len(E)} rows={len(rows)} vars={nv[0]} clauses={len(cl)}: {verdict} in {dt:.1f}s", flush=True)
if found: os.remove(fn)
else: os.rename(fn, f"blk4_s{s}_t{t}_n{n}.cnf")
