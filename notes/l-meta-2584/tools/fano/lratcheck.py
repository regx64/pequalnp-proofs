# Independent LRAT checker (RUP steps only; a RAT step, i.e. a negative hint, is rejected).
# usage: python3 lratcheck.py formula.cnf proof.lrat
# Succeeds only if every added clause is justified by its hints and the empty clause is added.
import sys
def main(cnf, prf):
    clauses = {}
    cid = 0
    with open(cnf) as f:
        buf = []
        for line in f:
            if line.startswith('c') or line.startswith('p'): continue
            for tok in line.split():
                x = int(tok)
                if x == 0:
                    cid += 1; clauses[cid] = tuple(buf); buf = []
                else: buf.append(x)
    norig = cid
    added = 0; empty = False
    with open(prf) as f:
        for ln, line in enumerate(f, 1):
            t = line.split()
            if not t: continue
            i = int(t[0])
            if t[1] == 'd':
                for x in t[2:]:
                    x = int(x)
                    if x == 0: break
                    clauses.pop(x, None)
                continue
            k = 1; lits = []
            while int(t[k]) != 0: lits.append(int(t[k])); k += 1
            k += 1; hints = []
            while int(t[k]) != 0: hints.append(int(t[k])); k += 1
            assert i > norig and i not in clauses, f"line {ln}: bad clause id {i}"
            true = {-l for l in lits}             # literals assumed true
            ok = False
            for h in hints:
                if h < 0: raise SystemExit(f"line {ln}: RAT hint not supported")
                c = clauses.get(h)
                if c is None: raise SystemExit(f"line {ln}: hint {h} missing")
                unassigned = None; nun = 0; sat = False
                for l in c:
                    if l in true: sat = True; break
                    if -l in true: continue
                    nun += 1; unassigned = l
                    if nun > 1: break
                if sat or nun > 1: raise SystemExit(f"line {ln}: hint {h} neither unit nor conflicting")
                if nun == 0: ok = True; break
                true.add(unassigned)
            if not ok: raise SystemExit(f"line {ln}: no conflict after hints")
            clauses[i] = tuple(lits); added += 1
            if not lits: empty = True; break
    print(f"original clauses {norig}, lemmas checked {added}, empty clause derived: {empty}")
    print("VERIFIED UNSAT" if empty else "NOT VERIFIED")
main(sys.argv[1], sys.argv[2])
