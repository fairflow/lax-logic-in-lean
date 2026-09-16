"""Discovery sweep: find formulas valid on a restricted class of PLL models
but refuted somewhere in the full class.  Untrusted; winners get proved in Lean."""
import itertools, sys

def posets(n):
    idx = [(i,j) for i in range(n) for j in range(n) if i != j]
    for bits in itertools.product([0,1], repeat=len(idx)):
        le = [[1 if i==j else 0 for j in range(n)] for i in range(n)]
        for (b,(i,j)) in zip(bits, idx):
            le[i][j] = b
        ok = True
        for i in range(n):
            for j in range(n):
                if le[i][j] and le[j][i] and i != j: ok = False; break
                if not le[i][j]: continue
                for k in range(n):
                    if le[j][k] and not le[i][k]: ok = False; break
                if not ok: break
            if not ok: break
        if ok: yield le

def subrels(n, le):
    """reflexive transitive rm with rm ⊆ le"""
    idx = [(i,j) for i in range(n) for j in range(n) if i != j and le[i][j]]
    for bits in itertools.product([0,1], repeat=len(idx)):
        rm = [[1 if i==j else 0 for j in range(n)] for i in range(n)]
        for (b,(i,j)) in zip(bits, idx): rm[i][j] = b
        ok = True
        for i in range(n):
            for j in range(n):
                if not rm[i][j]: continue
                for k in range(n):
                    if rm[j][k] and not rm[i][k]: ok = False; break
                if not ok: break
            if not ok: break
        if ok: yield rm

def upsets(n, le):
    for bits in itertools.product([0,1], repeat=n):
        s = list(bits)
        if all((not s[i]) or s[j] for i in range(n) for j in range(n) if le[i][j]):
            yield s

def models(n, natoms):
    for le in posets(n):
        ups = list(upsets(n, le))
        for rm in subrels(n, le):
            for fal in ups:
                vs = [u for u in ups if all((not fal[i]) or u[i] for i in range(n))]
                for vals in itertools.product(vs, repeat=natoms):
                    yield (n, le, rm, fal, list(vals))

# ---------- formulas ----------
ATOM, BOT, AND, OR, IMP, CIRC = 0,1,2,3,4,5
def gen_forms(maxsize, natoms):
    forms, bysize = [], {}
    def add(f):
        forms.append(f); return len(forms)-1
    bysize[1] = [add((ATOM,a,0)) for a in range(natoms)] + [add((BOT,0,0))]
    for s in range(2, maxsize+1):
        cur = []
        for i in bysize[s-1]: cur.append(add((CIRC,i,0)))
        for s1 in range(1, s-1):
            s2 = s-1-s1
            if s2 < 1 or s1 not in bysize or s2 not in bysize: continue
            for i in bysize[s1]:
                for j in bysize[s2]:
                    cur.append(add((AND,i,j))); cur.append(add((OR,i,j))); cur.append(add((IMP,i,j)))
        bysize[s] = cur
    return forms

def evaluate(model, forms):
    n, le, rm, fal, vals = model
    full = (1<<n)-1
    up = [sum(1<<j for j in range(n) if le[i][j]) for i in range(n)]
    out = []
    for (k,i,j) in forms:
        if   k == ATOM: m = sum(1<<w for w in range(n) if vals[i][w])
        elif k == BOT:  m = sum(1<<w for w in range(n) if fal[w])
        elif k == AND:  m = out[i] & out[j]
        elif k == OR:   m = out[i] | out[j]
        elif k == IMP:
            a, b = out[i], out[j]
            m = 0
            for w in range(n):
                if all((not (a>>v)&1) or ((b>>v)&1) for v in range(n) if le[w][v]): m |= 1<<w
        else:  # CIRC
            a = out[i]
            reach = [any(rm[v][u] and (a>>u)&1 for u in range(n)) for v in range(n)]
            m = 0
            for w in range(n):
                if all(reach[v] for v in range(n) if le[w][v]): m |= 1<<w
        out.append(m)
    return out

def cls_id(model):   n,le,rm,fal,vals = model; return all(rm[i][j]==(1 if i==j else 0) for i in range(n) for j in range(n))
def cls_le(model):   n,le,rm,fal,vals = model; return rm == le
def cls_ep(model):
    n,le,rm,fal,vals = model
    mx = [m for m in range(n) if all(u==m for u in range(n) if le[m][u])]
    return all(any(rm[a][m] for m in mx) for a in range(n))

def sweep(nmax, maxsize, natoms):
    forms = gen_forms(maxsize, natoms)
    nf = len(forms)
    refuted_any = [False]*nf
    refuted_in  = {'id':[False]*nf, 'le':[False]*nf, 'ep':[False]*nf}
    tot = 0
    for n in range(1, nmax+1):
        full = (1<<n)-1
        for model in models(n, natoms):
            tot += 1
            out = evaluate(model, forms)
            tags = [t for t,f in (('id',cls_id),('le',cls_le),('ep',cls_ep)) if f(model)]
            for k in range(nf):
                if out[k] != full:
                    refuted_any[k] = True
                    for t in tags: refuted_in[t][k] = True
    print(f"models scanned: {tot};  formulas: {nf}")
    for t in ('id','le','ep'):
        wins = [k for k in range(nf) if refuted_any[k] and not refuted_in[t][k]]
        print(f"\nclass {t}: {len(wins)} separator candidate(s)")
        for k in wins[:6]:
            print("   ", show(forms, k))
    return forms, refuted_any, refuted_in

def show(forms, k):
    kk,i,j = forms[k]
    if kk==ATOM: return "pq"[i]
    if kk==BOT:  return "⊥"
    if kk==CIRC: return "◯"+show(forms,i)
    a,b = show(forms,i), show(forms,j)
    return "("+a+{AND:"∧",OR:"∨",IMP:"⊃"}[kk]+b+")"

if __name__ == "__main__":
    sweep(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
