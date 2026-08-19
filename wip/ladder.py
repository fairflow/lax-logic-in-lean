"""Test the frame-side reading of F&M Cor 10:
   |Stab(M)| <= m   ==>   M |= chi_m ,
where Stab(M) = {u : forall t, Rm u t -> Rm t u} (the Rm-stable worlds, whose
count is the depth of the constraint C0 that lemma7 assigns to M)."""
from framescan import posets, subrels, upsets, models
import itertools

CIRC, IMP, OR, BOT, ATOM = 'C','I','O','B','A'
def chi(m):
    if m == 0: return (CIRC, (BOT,))
    return (CIRC, (IMP, (CIRC, (ATOM, m)), (OR, (ATOM, m), chi(m-1))))

def force(model, f, memo):
    """returns bitmask of worlds forcing f"""
    if f in memo: return memo[f]
    n, le, rm, fal, vals = model
    if f[0] == BOT:  m = sum(1 << w for w in range(n) if fal[w])
    elif f[0] == ATOM:
        i = f[1] - 1
        m = sum(1 << w for w in range(n) if vals[i][w])
    elif f[0] == OR:  m = force(model, f[1], memo) | force(model, f[2], memo)
    elif f[0] == IMP:
        a, b = force(model, f[1], memo), force(model, f[2], memo)
        m = 0
        for w in range(n):
            if all((not (a >> v) & 1) or ((b >> v) & 1) for v in range(n) if le[w][v]): m |= 1 << w
    else:  # CIRC
        a = force(model, f[1], memo)
        reach = [any(rm[v][u] and (a >> u) & 1 for u in range(n)) for v in range(n)]
        m = 0
        for w in range(n):
            if all(reach[v] for v in range(n) if le[w][v]): m |= 1 << w
    memo[f] = m
    return m

def stab(model):
    n, le, rm, fal, vals = model
    return [u for u in range(n) if all(rm[t][u] for t in range(n) if rm[u][t])]

def run(nmax, m, natoms):
    chim = chi(m)
    bad, tot, inclass = [], 0, 0
    minstab_refuting = None
    for n in range(1, nmax + 1):
        full = (1 << n) - 1
        for model in models(n, natoms):
            tot += 1
            s = len(stab(model))
            val = force(model, chim, {}) == full
            if s <= m:
                inclass += 1
                if not val: bad.append((model, s))
            if not val:
                if minstab_refuting is None or s < minstab_refuting: minstab_refuting = s
    print(f"n<={nmax}, m={m}, atoms={natoms}: {tot} models, {inclass} with |Stab|<={m}")
    print(f"   violations of  |Stab|<={m} => |= chi_{m} :  {len(bad)}")
    print(f"   least |Stab| among models REFUTING chi_{m}: {minstab_refuting}")
    for (mo, s) in bad[:3]:
        n, le, rm, fal, vals = mo
        print(f"   COUNTEREXAMPLE |Stab|={s}: n={n} le={le} rm={rm} fal={fal} V={vals}")

run(3, 1, 1)
run(3, 2, 2)
run(4, 1, 1)

run(4, 2, 2)
