# For small 4-cycle-free bipartite graphs: is there a least block-form circuit (size E + tau - 1)
# with an inner AND gate (an AND gate not below F)?  usage: python3 -I innerand.py maxn
import itertools, subprocess, sys
sys.path.insert(0, '..')
maxn = int(sys.argv[1])
def tau(n, E):
    for k in range(n + 1):
        for T in itertools.combinations(range(n), k):
            if all(a in T or b in T for a, b in E): return k
def c4free(n, E):
    adj = [set() for _ in range(n)]
    for a, b in E: adj[a].add(b); adj[b].add(a)
    return all(len(adj[a] & adj[b]) <= 1 for a, b in itertools.combinations(range(n), 2))
def bip(n, E):
    col = [-1] * n; adj = [[] for _ in range(n)]
    for a, b in E: adj[a].append(b); adj[b].append(a)
    for s in range(n):
        if col[s] < 0:
            col[s] = 0; st = [s]
            while st:
                u = st.pop()
                for v in adj[u]:
                    if col[v] < 0: col[v] = 1 - col[u]; st.append(v)
                    elif col[v] == col[u]: return False
    return True
def canon(n, E):
    return min(tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in E)) for p in itertools.permutations(range(n)))
seen = set()
for n in range(3, maxn + 1):
    pairs = list(itertools.combinations(range(n), 2))
    for m in range(n - 1, len(pairs) + 1):
        for E in itertools.combinations(pairs, m):
            deg = [0] * n
            for a, b in E: deg[a] += 1; deg[b] += 1
            if min(deg) == 0 or not bip(n, E) or not c4free(n, E): continue
            # connected only
            comp = {0}; ch = True
            while ch:
                ch = False
                for a, b in E:
                    if (a in comp) != (b in comp): comp |= {a, b}; ch = True
            if len(comp) < n: continue
            c = canon(n, E) if n <= 7 else tuple(E)
            if (n, c) in seen: continue
            seen.add((n, c))
            L = len(E) + tau(n, E) - 1
            es = ",".join(f"{a}-{b}" for a, b in c)
            res = []
            for t in range(1, (L + 1) // 2 + 1):
                out = subprocess.run(["python3", "-I", "topsat3.py", str(L), str(t), str(n), es, "--extra", "--innerand", "--timeout", "120"],
                                     capture_output=True, text=True).stdout
                v = "SAT" if ": SAT" in out else ("UNSAT" if ": UNSAT" in out else "UNKNOWN")
                res.append(f"t{t}:{v}")
                if v == "SAT":
                    res.append(out.split("CIRCUIT ")[1].strip())
            print(n, es, "L=", L, " ".join(res), flush=True)
