# Block form search: AO2 circuits of exactly s gates with t tops, for an edge function of a 4-cycle-free
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
    if Fr(r): cl.append([tval[k][r] for k in range(t)])
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
# orIn of inner wires (from below) and the sides of the tops
I = [[new() for i in range(n)] for j in range(m)]
for j in range(m):
    for e in range(2):
        for i in range(n):
            cl.append([isA[j], -sel[j][e][i], I[j][i]])
            for q in range(j): cl.append([isA[j], -sel[j][e][n + q], -I[q][i], I[j][i]])
for k in range(t):
    Sd = [[new() for i in range(n)] for e in range(2)]
    for e in range(2):
        for i in range(n):
            cl.append([-tsel[k][e][i], Sd[e][i]])
            for q in range(m): cl.append([-tsel[k][e][n + q], -I[q][i], Sd[e][i]])
    for i in range(n): cl.append([-Sd[0][i], -Sd[1][i]])
    for u in range(n):
        for v in range(n):
            if u != v and (u, v) not in adj: cl.append([-Sd[0][u], -Sd[1][v]])
    z = new(); at_most_one(Sd[0], guard=[-z]); at_most_one(Sd[1], guard=[z])

fn = f"blk_s{s}_t{t}_{os.getpid()}.cnf"
with open(fn, "w") as f:
    f.write(f"p cnf {nv[0]} {len(cl)}\n")
    for c in cl: f.write(" ".join(map(str, c)) + " 0\n")
cad = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical")
cmd = [cad, "-q"] + (["-t", str(tmo)] if tmo else []) + [fn] + ([proof] if proof else [])
t0 = time.time(); out = subprocess.run(cmd, capture_output=True, text=True).stdout; dt = time.time() - t0
verdict = "SAT" if "s SATISFIABLE" in out else ("UNSAT" if "s UNSATISFIABLE" in out else "UNKNOWN")
print(f"block s={s} t={t} m={m} n={n} E={len(E)} rows={len(rows)} vars={nv[0]} clauses={len(cl)}: {verdict} in {dt:.1f}s", flush=True)
if verdict == "SAT":
    T = set(int(x) for line in out.splitlines() if line.startswith("v") for x in line[1:].split() if int(x) > 0)
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
    print("CIRCUIT", " ".join(gs), flush=True)
    os.remove(fn)
else:
    os.rename(fn, f"blk_s{s}_t{t}_n{n}.cnf")
