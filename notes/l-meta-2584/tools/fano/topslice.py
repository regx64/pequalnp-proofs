# Exact-size AO2 circuit search for an edge function, with optional WLOG normal-form constraints.
#
# usage: python3 topsat.py MODE s n edges [--proof FILE] [--timeout SEC]
#   MODE = base | wlog
#
# Circuit model (matches PEqualNP.TopForm.IsAO2 after the simplifications W1-W4 below): s gates,
# each AND or OR, reading two wires of smaller index; wires 0..n-1 are the inputs; gate j is wire
# n+j. Rows: the minterms (edges) and the maximal zeros (maximal independent sets) of F. A monotone
# circuit is right on these rows iff it computes F; a wire is below F iff it is false on every
# maximal zero.
#
# base (both modes), valid for every LEAST circuit up to renumbering:
#   W1 the output is the last gate          (gates after the output could be deleted)
#   W2 every gate but the last is read       (gates outside the output cone could be deleted)
#   W3 the two operands differ, first < second  (AND(i,i)=OR(i,i)=wire i could be deleted;
#                                                 operand order is free)
#   W4 greedy topological order: if gate j+1 does not read wire n+j then
#      first-operand(j+1) >= first-operand(j)
# wlog adds, for a least circuit in TopForm (L_meta_5779), the conclusions of the checked
# L_meta_1498 (a) and L_meta_1490 (first conjunct):
#   C1 TopForm: no AND gate below F lies strictly inside the cone of an AND gate
#   C2 a gate below F other than the output has exactly one reader, an OR gate below F
#   C4 for every AND gate below F (a top): its two sides (orIn of its operands) are disjoint, every
#      cross pair is an edge, and one side has at most one input
# cone and side variables are forced only from below: a real least TopForm circuit satisfies the
# encoding with the true cones and sides; a model with larger ones only meets more constraints.
import sys, itertools, subprocess, os, time

mode, s, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
E = [tuple(map(int, e.split('-'))) for e in sys.argv[4].split(',')]
proof = sys.argv[sys.argv.index('--proof') + 1] if '--proof' in sys.argv else None
tmo = int(sys.argv[sys.argv.index('--timeout') + 1]) if '--timeout' in sys.argv else 0
adj = set(E) | {(b, a) for a, b in E}
Fr = lambda r: any(r >> a & 1 and r >> b & 1 for a, b in E)
mins = sorted({(1 << a) | (1 << b) for a, b in E})
maxz = [r for r in range(1 << n) if not Fr(r) and all(Fr(r | (1 << i)) for i in range(n) if not r >> i & 1)]
if '--slice' in sys.argv:   # 2-slice relaxation: only inputs of weight <= 2
    maxz = [1 << i for i in range(n)] + [(1 << a) | (1 << b) for a in range(n) for b in range(a + 1, n) if (a, b) not in adj]
if '--bislice' in sys.argv:   # bipartite 2-slice (star complexity): only point-line pairs, same-side pairs free
    side = [-1] * n; side[0] = 0; ch = True
    while ch:
        ch = False
        for a, b in E:
            for u, v in ((a, b), (b, a)):
                if side[u] >= 0 and side[v] < 0: side[v] = 1 - side[u]; ch = True
    maxz = [(1 << a) | (1 << b) for a in range(n) for b in range(a + 1, n) if (a, b) not in adj and side[a] != side[b]]
rows = mins + maxz

cl = []; nv = [0]
def new():
    nv[0] += 1; return nv[0]
def exactly_one(vs):
    cl.append(list(vs)); cl.extend([[-a, -b] for a, b in itertools.combinations(vs, 2)])
def at_most_one(vs, guard=()):
    cl.extend([list(guard) + [-a, -b] for a, b in itertools.combinations(vs, 2)])

sel = [[[new() for k in range(n + j)] for e in range(2)] for j in range(s)]
isA = [new() for j in range(s)]               # true: AND, false: OR
val = [{r: new() for r in rows} for j in range(s)]
va = [[{r: new() for r in rows} for e in range(2)] for j in range(s)]
for j in range(s):
    for e in range(2): exactly_one(sel[j][e])
    for ka in range(n + j):                     # W3: first operand < second operand
        for kb in range(ka + 1): cl.append([-sel[j][0][ka], -sel[j][1][kb]])
def wire(k, r): return ((r >> k) & 1 == 1) if k < n else val[k - n][r]
for j in range(s):
    for r in rows:
        for e in range(2):
            v = va[j][e][r]
            for k in range(n + j):
                w = wire(k, r)
                if isinstance(w, bool): cl.append([-sel[j][e][k], v if w else -v])
                else: cl.append([-sel[j][e][k], -w, v]); cl.append([-sel[j][e][k], w, -v])
        g, a, b = val[j][r], va[j][0][r], va[j][1][r]
        cl += [[-isA[j], -g, a], [-isA[j], -g, b], [-isA[j], g, -a, -b],
               [isA[j], g, -a], [isA[j], g, -b], [isA[j], -g, a, b]]
for r in rows: cl.append([val[s - 1][r]] if Fr(r) else [-val[s - 1][r]])          # W1
reads = [[None] * s for _ in range(s)]           # reads[j][k]: gate k reads wire n+j
for j in range(s):
    for k in range(j + 1, s):
        x = new(); reads[j][k] = x
        cl.append([-x, sel[k][0][n + j], sel[k][1][n + j]])
        cl.append([x, -sel[k][0][n + j]]); cl.append([x, -sel[k][1][n + j]])
for j in range(s - 1): cl.append([reads[j][k] for k in range(j + 1, s)])          # W2
for j in range(s - 1):                                                             # W4
    for k in range(n + j):
        for k2 in range(k): cl.append([-sel[j][0][k], -sel[j + 1][0][k2], reads[j][j + 1]])

if mode == 'wlog':
    below = [new() for j in range(s)]            # below[j] <-> false on every maximal zero
    for j in range(s):
        cl.append([below[j]] + [val[j][r] for r in maxz])
        for r in maxz: cl.append([-below[j], -val[j][r]])
    # C1: cone[i][j] forced from below (gate i strictly inside the cone of gate j)
    cone = {}
    for j in range(s):
        for i in range(j):
            cone[(i, j)] = new()
            cl.append([-reads[i][j], cone[(i, j)]])
            for k in range(i + 1, j): cl.append([-cone[(i, k)], -reads[k][j], cone[(i, j)]])
    for j in range(s):
        for i in range(j):
            cl.append([-isA[i], -below[i], -isA[j], -cone[(i, j)]])
    # C2
    for j in range(s - 1):
        at_most_one([reads[j][k] for k in range(j + 1, s)], guard=[-below[j]])
        for k in range(j + 1, s):
            cl.append([-below[j], -reads[j][k], -isA[k]])
            cl.append([-below[j], -reads[j][k], below[k]])
    # C4: orIn sets I[j][i] forced from below; sides S[a][e][i]
    I = [[new() for i in range(n)] for j in range(s)]
    for j in range(s):
        for e in range(2):
            for i in range(n):
                cl.append([isA[j], -sel[j][e][i], I[j][i]])                     # direct input
                for k in range(j):
                    cl.append([isA[j], -sel[j][e][n + k], -I[k][i], I[j][i]])     # OR operand
    S = [[[new() for i in range(n)] for e in range(2)] for a in range(s)]
    for a in range(s):
        for e in range(2):
            for i in range(n):
                cl.append([-sel[a][e][i], S[a][e][i]])
                for k in range(a): cl.append([-sel[a][e][n + k], -I[k][i], S[a][e][i]])
        top = [-isA[a], -below[a]]                 # guard: "a is a top" makes these active
        for i in range(n): cl.append(top + [-S[a][0][i], -S[a][1][i]])
        for u in range(n):
            for v in range(n):
                if u != v and (u, v) not in adj: cl.append(top + [-S[a][0][u], -S[a][1][v]])
        z = new()
        at_most_one(S[a][0], guard=top + [-z]); at_most_one(S[a][1], guard=top + [z])

fn = f"top_{mode}_{s}_{os.getpid()}.cnf"
if "--slice" in sys.argv: mode = mode + "slice"
with open(fn, "w") as f:
    f.write(f"p cnf {nv[0]} {len(cl)}\n")
    for c in cl: f.write(" ".join(map(str, c)) + " 0\n")
cad = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical")
cmd = [cad, "-q"] + ([f"-t", str(tmo)] if tmo else []) + [fn] + ([proof] if proof else [])
t0 = time.time(); res = subprocess.run(cmd, capture_output=True, text=True); dt = time.time() - t0
out = res.stdout
verdict = "SAT" if "s SATISFIABLE" in out else ("UNSAT" if "s UNSATISFIABLE" in out else "UNKNOWN")
print(f"mode={mode} s={s} n={n} E={len(E)} rows={len(rows)} vars={nv[0]} clauses={len(cl)}: {verdict} in {dt:.1f}s", flush=True)
if verdict == "SAT":
    T = set(int(x) for line in out.splitlines() if line.startswith("v") for x in line[1:].split() if int(x) > 0)
    gs = []
    for j in range(s):
        a = [k for k in range(n + j) if sel[j][0][k] in T][0]; b = [k for k in range(n + j) if sel[j][1][k] in T][0]
        gs.append(('A' if isA[j] in T else 'O') + f"{a},{b}")
    print("CIRCUIT", " ".join(gs), flush=True)
if verdict != "UNKNOWN" or not proof:
    pass
os.rename(fn, f"cnf_{mode}_s{s}_n{n}.cnf") if verdict != "SAT" else os.remove(fn)
