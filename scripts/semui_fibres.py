#!/usr/bin/env python3
"""Exact decision of the PLL amalgamation lemma on finite poset models.

    python3 scripts/semui_fibres.py validate      # 18 known quantifier values
    python3 scripts/semui_fibres.py chains        # alternating chains
    python3 scripts/semui_fibres.py ladders       # Rieger–Nishimura ladders
    python3 scripts/semui_fibres.py types         # are two kinds of type enough?
    python3 scripts/semui_fibres.py realisations  # is the fibre a logical invariant?
    python3 scripts/semui_fibres.py all

This is the refutation-stage tool for `PLLND.SemUI.amalgamation`
(`LaxLogic/PLL/SemUI/SemUILayered.lean`) and the design check for the proof in
`LaxLogic/PLL/SemUI/SemUILayeredAmalg.lean`.  It is evidence, not proof: nothing
here is kernel-checked.  Write-up: `docs/semui-amalgamation-2026-10-14.md`.

WHAT IS COMPUTED.  For a finite model M, a variable p and a subformula-closed
X, the *fibre* of a world m is

    fib(m) = { V ⊆ X | some p-variant (N, C : PBisim p M N, n) with C.Z m n
                        has  V = {φ ∈ X | N ⊩_n φ} }.

It is the V-projection of the greatest set A ⊆ Types × W_M, with a type a pair
(V, P), P ⊆ {ξ | ◯ξ ∈ X} \\ V ("blocked": no Rm-successor forces ξ), closed
under

  (b)  ⊥ ∈ V ⇔ m ∈ F;   a ∈ V ⇔ m ∈ V(a)   for the atoms a ≠ p of X
  (g)  V locally consistent (⊥ ∈ V ⇒ V = X; ∧, ∨ exact; ⊃ closed under MP)
  (f)  P ∩ V = ∅
  (ai) ∀ m' ∈ Ri(m) ∃ (V',P') at m':  V ⊆ V'
  (am) ∀ m' ∈ Rm(m) ∃ (V',P') at m':  V ⊆ V', P ⊆ P'
  (c)  ◯ξ ∈ V ⇒ ∃ m' ∈ Rm(m), (V',P') at m':  V ⊆ V', P ⊆ P', ξ ∈ V'
  (d)  ◯ξ ∉ V ⇒ ∃ m' ∈ Ri(m), (V',P') at m':  V ⊆ V', ξ ∈ P'
  (e)  φ⊃ψ ∉ V ⇒ ∃ m' ∈ Ri(m), (V',P') at m':  V ⊆ V', φ ∈ V', ψ ∉ V'

Soundness (realisable ⊆ A): the true (V, P) of a variant point satisfies every
clause, by the four zigzags of PBisim, heredity, and reflexivity/transitivity
of Rm.  Completeness (A ⊆ realisable): take N := A with componentwise
relations ((V,P,m) Ri (V',P',m') iff m Ri m' ∧ V ⊆ V'; Rm adds P ⊆ P'), F and
the atoms ≠ p read from m, p read from V; the projection is a PBisim off p and
N ⊩ φ ⇔ φ ∈ V for φ ∈ X by induction on φ.

THE TEST.  `amalgamation` for (K,k₀), (M,m₀) linked by a strong layered
bisimulation off p at level L says tp_K(k₀) ∈ fib_M(m₀).  A p-variant of K is
still linked to M at the same level, so the lemma at level L is equivalent to

    linked at level ≥ L   ⇒   fib_K(k₀) = fib_M(m₀).

For a model M the tool reports  L* = 1 + max{ level(a,b) | fib(a) ≠ fib(b) },
the least level at which the lemma holds on the pairs of worlds of M.  The
lemma as stated needs L* ≤ 2ν+1.  Worlds that are fully bisimilar must have
equal fibres; a pair violating that is reported as a tool bug.
"""
import sys
from itertools import product

# ---------------------------------------------------------------- formulas
def At(a): return ('p', a)
BOT = ('bot',)
def And(a, b): return ('and', a, b)
def Or(a, b): return ('or', a, b)
def Imp(a, b): return ('imp', a, b)
def Box(a): return ('box', a)
def Neg(a): return Imp(a, BOT)
TOP = Imp(BOT, BOT)

def show(f):
    t = f[0]
    if t == 'p': return f[1]
    if t == 'bot': return '⊥'
    if t == 'and': return f'({show(f[1])}∧{show(f[2])})'
    if t == 'or': return f'({show(f[1])}∨{show(f[2])})'
    if t == 'imp':
        return f'¬{show(f[1])}' if f[2] == BOT else f'({show(f[1])}⊃{show(f[2])})'
    return f'◯{show(f[1])}'

def sub(f):
    s = {f}
    if f[0] in ('and', 'or', 'imp'): s |= sub(f[1]) | sub(f[2])
    elif f[0] == 'box': s |= sub(f[1])
    return s

def closure(*fs):
    s = {BOT}
    for f in fs: s |= sub(f)
    return frozenset(s)

def nu(X): return sum(1 for f in X if f[0] in ('p', 'imp', 'box'))

def atoms(f):
    if f[0] == 'p': return {f[1]}
    if f[0] == 'bot': return set()
    if f[0] == 'box': return atoms(f[1])
    return atoms(f[1]) | atoms(f[2])

# ---------------------------------------------------------------- models
class Model:
    """Finite constraint model on worlds 0..n-1.  Ri, Rm are closed under
    reflexivity and transitivity, Rm ⊆ Ri is enforced, F and the valuations
    are closed upward and the valuations made full on F."""
    def __init__(self, n, Ri, Rm, F, V, name=''):
        self.n, self.name = n, name
        Rm = self._tc(set(Rm) | {(w, w) for w in range(n)})
        Ri = self._tc(set(Ri) | Rm)
        self.Ri, self.Rm = Ri, Rm
        up = lambda S: frozenset(b for (a, b) in Ri if a in S)
        self.F = up(set(F))
        self.V = {a: up(set(s)) | self.F for a, s in V.items()}
        self.succ_i = [[v for v in range(n) if (w, v) in Ri] for w in range(n)]
        self.succ_m = [[v for v in range(n) if (w, v) in Rm] for w in range(n)]
        assert all(a == b or (b, a) not in Ri for (a, b) in Ri), 'not a poset'
        self._fc = {}

    @staticmethod
    def _tc(R):
        ch = True
        while ch:
            ch = False
            for (a, b) in list(R):
                for (c, d) in list(R):
                    if b == c and (a, d) not in R: R.add((a, d)); ch = True
        return R

    def val(self, a, w): return w in self.V.get(a, self.F)

    def force(self, w, f):
        key = (w, f)
        if key not in self._fc:
            t = f[0]
            if t == 'p': r = self.val(f[1], w)
            elif t == 'bot': r = w in self.F
            elif t == 'and': r = self.force(w, f[1]) and self.force(w, f[2])
            elif t == 'or': r = self.force(w, f[1]) or self.force(w, f[2])
            elif t == 'imp':
                r = all(not self.force(v, f[1]) or self.force(v, f[2]) for v in self.succ_i[w])
            else:
                r = all(any(self.force(u, f[1]) for u in self.succ_m[v]) for v in self.succ_i[w])
            self._fc[key] = r
        return self._fc[key]

UNBOUNDED = 80

def level_matrix(K, M, p):
    """lev[(k,m)] = the largest L with k Z_L m for the greatest strong
    `LayeredBisim (· ≠ p) K M` (-1 if not even Z_0; UNBOUNDED if bisimilar)."""
    ats = (set(K.V) | set(M.V)) - {p}
    Z = {(k, m) for k in range(K.n) for m in range(M.n)
         if (k in K.F) == (m in M.F) and all(K.val(a, k) == M.val(a, m) for a in ats)}
    lev = {(k, m): (0 if (k, m) in Z else -1) for k in range(K.n) for m in range(M.n)}
    for L in range(1, UNBOUNDED + 1):
        Z2 = {(k, m) for (k, m) in Z if
              all(any((v, v2) in Z for v2 in M.succ_i[m]) for v in K.succ_i[k]) and
              all(any((v, v2) in Z for v in K.succ_i[k]) for v2 in M.succ_i[m]) and
              all(any((u, u2) in Z for u2 in M.succ_m[m]) for u in K.succ_m[k]) and
              all(any((u, u2) in Z for u in K.succ_m[k]) for u2 in M.succ_m[m])}
        if Z2 == Z:
            for pr in Z: lev[pr] = UNBOUNDED
            return lev
        for pr in Z2: lev[pr] = L
        Z = Z2
    return lev

# ---------------------------------------------------------------- the fixpoint
class Fib:
    """The greatest fixpoint, computed top-down over a poset: the fibre of m
    depends only on the cone above m."""
    two_kinds = False     # restrict types to P = ∅ and P = (boxed bodies) \ V

    def __init__(self, X, p):
        self.X = sorted(X, key=lambda f: (len(repr(f)), repr(f)))
        ix = self.ix = {f: i for i, f in enumerate(self.X)}
        self.p, self.full, self.bot = p, (1 << len(self.X)) - 1, 1 << ix[BOT]
        tri = lambda k: [(1 << ix[f], 1 << ix[f[1]], 1 << ix[f[2]]) for f in self.X if f[0] == k]
        self.imps, self.ands, self.ors = tri('imp'), tri('and'), tri('or')
        self.boxes = [(1 << ix[f], 1 << ix[f[1]]) for f in self.X if f[0] == 'box']
        self.pdom = 0
        for (_, b) in self.boxes: self.pdom |= b
        self.tracked = [(a, 1 << ix[At(a)]) for a in sorted({a for f in X for a in atoms(f)})
                        if a != p and At(a) in ix]
        self.types = self._types()

    def _local_ok(self, V):
        if V & self.bot and V != self.full: return False
        for (f, a, b) in self.ands:
            if bool(V & f) != (bool(V & a) and bool(V & b)): return False
        for (f, a, b) in self.ors:
            if bool(V & f) != (bool(V & a) or bool(V & b)): return False
        for (f, a, b) in self.imps:
            if V & f and V & a and not V & b: return False
            if V & b and not V & f: return False      # a consequence of (e)
        for (f, b) in self.boxes:
            if V & b and not V & f: return False      # a consequence of (d), (f)
        return True

    def _types(self):
        out = []
        pbits = [1 << i for i in range(len(self.X)) if self.pdom >> i & 1]
        for V in range(self.full + 1):
            if not self._local_ok(V): continue
            if self.two_kinds:
                out.append((V, 0))
                if self.pdom & ~V: out.append((V, self.pdom & ~V))
                continue
            free = [b for b in pbits if not V & b]
            for bits in product((0, 1), repeat=len(free)):
                out.append((V, sum(b for b, on in zip(free, bits) if on)))
        return out

    def mask(self, fs): return sum(1 << self.ix[f] for f in fs)
    def unmask(self, V): return [self.X[i] for i in range(len(self.X)) if V >> i & 1]
    def showV(self, V): return '{' + ', '.join(show(f) for f in self.unmask(V)) + '}'

    def own_type(self, M, w):
        V = self.mask(f for f in self.X if M.force(w, f))
        Pm = 0
        for (_, b) in self.boxes:
            xi = self.X[b.bit_length() - 1]
            if not any(M.force(u, xi) for u in M.succ_m[w]): Pm |= b
        return (V, Pm)

    def compute(self, M):
        order = sorted(range(M.n), key=lambda w: len(M.succ_i[w]))     # tops first
        fib = [None] * M.n
        for m in order:
            si = [x for x in M.succ_i[m] if x != m]
            sm = [x for x in M.succ_m[m] if x != m]
            up_i = [t for x in si for t in fib[x]]
            up_m = [t for x in sm for t in fib[x]]
            cand = []
            for (V, Pm) in self.types:
                if bool(V & self.bot) != (m in M.F): continue
                if any(bool(V & b) != M.val(a, m) for (a, b) in self.tracked): continue
                if not all(any(V & ~V2 == 0 for (V2, _) in fib[x]) for x in si): continue
                if not all(any(V & ~V2 == 0 and Pm & ~P2 == 0 for (V2, P2) in fib[x]) for x in sm):
                    continue
                cand.append((V, Pm))
            changed = True
            while changed:
                changed, keep = False, []
                for (V, Pm) in cand:
                    ok = True
                    for (f, b) in self.boxes:
                        if V & f:
                            if not (any(V & ~V2 == 0 and Pm & ~P2 == 0 and V2 & b for (V2, P2) in cand)
                                    or any(V & ~V2 == 0 and Pm & ~P2 == 0 and V2 & b for (V2, P2) in up_m)):
                                ok = False; break
                        elif not (any(V & ~V2 == 0 and P2 & b for (V2, P2) in cand)
                                  or any(V & ~V2 == 0 and P2 & b for (V2, P2) in up_i)):
                            ok = False; break
                    if ok:
                        for (f, a, b) in self.imps:
                            if not V & f and not (
                                    any(V & ~V2 == 0 and V2 & a and not V2 & b for (V2, _) in cand)
                                    or any(V & ~V2 == 0 and V2 & a and not V2 & b for (V2, _) in up_i)):
                                ok = False; break
                    if ok: keep.append((V, Pm))
                    else: changed = True
                cand = keep
            fib[m] = cand
        if not self.two_kinds:      # the tool's own gate: a world realises its own type
            assert all(self.own_type(M, w) in set(fib[w]) for w in range(M.n)), \
                "a world's own type is missing from the fixpoint: tool bug"
        return [frozenset(V for (V, _) in f) for f in fib]

class Fib2(Fib):
    two_kinds = True

# ---------------------------------------------------------------- model families
p, q = 'p', 'q'
pp, qq = At(p), At(q)

def word_chain(word):
    """Chain w_0 < … < w_{n-1}; the letter at j gives w_j an Rm-successor:
    'q' a rigid q-top, 'f' a fallible top, '-' nothing (w_j is rigid)."""
    n = len(word); Ri = {(j, j + 1) for j in range(n - 1)}; Rm = set(); F = set(); Vq = set()
    nxt = n
    for j, c in enumerate(word):
        if c == '-': continue
        Ri.add((j, nxt)); Rm.add((j, nxt))
        (Vq if c == 'q' else F).add(nxt)
        nxt += 1
    return Model(nxt, Ri, Rm, F, {q: Vq}, word if len(word) < 12 else word[:8] + '…')

def ladder_edges(n):
    """The Rieger–Nishimura ladder: tops w0, w1; w2 < w0; w_k < w_{k-2}, w_{k-3}."""
    Ri = {(2, 0)}
    for k in range(3, n + 1): Ri |= {(k, k - 2), (k, k - 3)}
    return Ri

def rn(n, rm='id', ftop=None):
    """Ladder over q (true at w0) with an Rm pattern: 'id' rigid (the IPC case),
    'full' Rm = Ri, 'left' w_k Rm w_{k-2}, 'right' w_k Rm w_{k-3}, 'even' Rm = Ri
    out of even-indexed worlds, 'toq' w_k Rm w_0 whenever w_k ≤ w_0.
    ftop ∈ {None, 0, 1} adds a fallible world Rm-above w_ftop."""
    base = Model(n + 1, ladder_edges(n), set(), set(), {q: {0}})
    Rm = {'id': set(), 'full': set(base.Ri),
          'left': {(k, k - 2) for k in range(2, n + 1)},
          'right': {(k, k - 3) for k in range(3, n + 1)},
          'even': {(a, b) for (a, b) in base.Ri if a % 2 == 0},
          'toq': {(a, 0) for a in range(n + 1) if (a, 0) in base.Ri}}[rm]
    N, F, Ri = n + 1, set(), set(base.Ri)
    if ftop is not None:
        Ri.add((ftop, N)); Rm.add((ftop, N)); F.add(N); N += 1
    return Model(N, Ri, Rm, F, {q: {0}}, f'RN{n}/{rm}/f{ftop}')

def realise(n, S, mode):
    """Ladder with a prescribed set S of rigid non-fallible worlds; each other
    world gets Rm-edges by `mode`: 'S' to every S-world above it, 'one' to the
    least-index one, 'f' to a private fallible world, 'mix' ('f' on even,
    'one' on odd indices), 'all' to everything above it.  All realisations of
    one S force the same formulas pointwise (see `realisations`)."""
    base = Model(n + 1, ladder_edges(n), set(), set(), {q: {0}})
    Ri, Rm, F, N = set(base.Ri), set(), set(), n + 1
    for w in range(n + 1):
        if w in S: continue
        above = [s for s in sorted(S) if (w, s) in base.Ri]
        use = ('f' if w % 2 == 0 else 'one') if mode == 'mix' else mode
        if use == 'f' or not above:
            Ri.add((w, N)); Rm.add((w, N)); F.add(N); N += 1
        elif use == 'S': Rm |= {(w, s) for s in above}
        elif use == 'one': Rm.add((w, above[0]))
        else: Rm |= {(w, v) for v in range(n + 1) if (w, v) in base.Ri and v != w}
    M = Model(N, Ri, Rm, F, {q: {0}}, f'S={sorted(S)}/{mode}')
    assert {w for w in range(n + 1) if M.succ_m[w] == [w]} == set(S)
    return M

ONE_VAR = [Imp(Box(pp), pp), Box(Imp(Box(pp), pp)), Imp(Imp(Box(pp), pp), Box(BOT)),
           Or(Box(pp), Neg(Box(pp))), Imp(Neg(Neg(Box(pp))), Box(pp)),
           Or(Box(Neg(pp)), Box(Neg(Neg(pp)))), Imp(Neg(Box(pp)), Box(Neg(pp))),
           Box(Or(pp, Neg(pp))), Box(Imp(Neg(Box(pp)), pp))]
TWO_VAR = [Imp(Box(Imp(qq, pp)), Box(pp)), Imp(Imp(Box(pp), qq), Box(Or(pp, qq))),
           Imp(Box(Or(pp, qq)), Or(Box(pp), Box(qq))), Imp(Box(Imp(pp, qq)), Box(qq)),
           Imp(Neg(Box(pp)), Box(Imp(pp, qq))), Imp(Box(Imp(Box(pp), qq)), Box(qq)),
           Imp(Box(pp), Box(qq)), Imp(Imp(Box(qq), pp), Box(pp))]
LADDER = [Or(Imp(pp, qq), Imp(Neg(pp), qq)), Imp(Imp(Imp(pp, qq), pp), pp),
          Imp(Imp(Neg(Neg(pp)), pp), Or(qq, Neg(qq))),          # ◯-free: the IPC baseline
          Imp(Box(pp), pp), Imp(Imp(Box(pp), pp), qq), Imp(Box(Imp(qq, pp)), Box(pp)),
          Imp(Imp(Box(pp), qq), Box(Or(pp, qq))), Imp(Box(Or(pp, qq)), Or(Box(pp), Box(qq))),
          Or(Imp(Box(pp), qq), Imp(Neg(Box(pp)), qq)), Imp(Box(Imp(Imp(pp, qq), pp)), Box(pp))]

# ---------------------------------------------------------------- the commands
def lstar(X, M):
    """(L*, the pair attaining it).  Raises if bisimilar worlds differ."""
    fb = Fib(X, p).compute(M)
    lev = level_matrix(M, M, p)
    worst, wit = -1, None
    for a in range(M.n):
        for b in range(a + 1, M.n):
            if fb[a] != fb[b]:
                assert lev[(a, b)] < UNBOUNDED, 'bisimilar worlds with different fibres: tool bug'
                if lev[(a, b)] > worst: worst, wit = lev[(a, b)], (a, b)
    return worst + 1, wit

def report(title, cells, models):
    print(f'## {title}')
    worst = {}
    for M in models:
        for f in cells:
            X = closure(f)
            L, _ = lstar(X, M)
            worst[f] = max(worst.get(f, 0), L)
    bad = 0
    for f in cells:
        need = 2 * nu(closure(f)) + 1
        flag = 'ok' if worst[f] <= need else 'VIOLATION'
        bad += flag != 'ok'
        print(f'  {show(f):30s} ν={nu(closure(f))}  2ν+1={need:2d}  worst L*={worst[f]:2d}  {flag}')
    print(f'  {len(cells)} closures × {len(models)} models; violations of the 2ν+1 bound: {bad}')
    return bad

def cmd_validate():
    """The fixpoint against quantifier values that are theorems of the library
    (`SemUI.lean`, `SemUIBox.lean`, the one-◯ two-variable sweep) or were
    derived by hand: ∃p.φ holds at m iff φ ∈ some V ∈ fib(m); ∀p.φ holds at m
    iff φ ∈ every V ∈ fib(m') for every m' ≥ m."""
    def chain(n, top_f=False, rm_full=False, qset=()):
        Ri = {(i, j) for i in range(n) for j in range(i, n)}
        return Model(n, Ri, Ri if rm_full else set(), {n - 1} if top_f else set(), {q: set(qset)})
    battery = [Model(1, set(), set(), set(), {q: set()}), Model(1, set(), set(), {0}, {q: set()}),
               chain(2, True), chain(2, True, True), chain(2), chain(2, False, True),
               chain(3, True), chain(3, True, True), chain(3, False, True, {2}), chain(3, True, False, {1}),
               Model(3, {(0, 1), (0, 2)}, {(0, 2)}, {2}, {q: set()}),
               Model(3, {(0, 1), (0, 2)}, {(0, 2)}, set(), {q: {1}}),
               Model(3, {(0, 1), (0, 2)}, {(0, 1)}, {2}, {q: {1}}),
               Model(4, {(0, 1), (0, 2), (1, 3), (2, 3)}, {(0, 1), (1, 3)}, {3}, {q: {2}}),
               Model(4, {(0, 1), (0, 2), (1, 3), (2, 3)}, {(0, 2), (2, 3)}, set(), {q: {1}})]
    alls = [(Box(pp), Box(BOT)), (Imp(Box(pp), pp), BOT), (Box(Imp(Box(pp), pp)), Box(BOT)),
            (Or(pp, Neg(pp)), BOT), (Imp(Neg(Neg(pp)), pp), BOT),
            (Imp(Imp(Imp(pp, Box(BOT)), pp), pp), Box(BOT)), (Box(Or(pp, qq)), Box(qq)),
            (Box(Imp(qq, pp)), Box(Neg(qq))), (Or(Box(pp), qq), Or(Box(BOT), qq)),
            (Imp(qq, Box(pp)), Imp(qq, Box(BOT))), (Imp(Box(qq), pp), Neg(Box(qq))),
            (qq, qq), (Box(BOT), Box(BOT))]
    exs = [(And(pp, Neg(pp)), BOT), (Box(pp), TOP), (Neg(pp), TOP),
           (Imp(Imp(Box(pp), pp), Box(BOT)), Neg(Neg(Box(BOT)))),
           (And(Box(pp), Box(Neg(pp))), Box(BOT))]
    bad = cells = 0
    for kind, table in (('∀', alls), ('∃', exs)):
        for phi, val in table:
            for M in battery:
                fb = Fib(closure(phi), p); fib = fb.compute(M); bit = 1 << fb.ix[phi]
                for m in range(M.n):
                    cells += 1
                    got = (all(V & bit for m2 in M.succ_i[m] for V in fib[m2]) if kind == '∀'
                           else any(V & bit for V in fib[m]))
                    if got != M.force(m, val):
                        bad += 1; print(f'  MISMATCH {kind}p.{show(phi)} = {show(val)}')
    print(f'## validate\n  {len(alls) + len(exs)} known values × {len(battery)} models: '
          f'{cells} world-cells, {bad} mismatches')
    return bad

def cmd_chains():
    bad = report('alternating chains, fallible witnesses (logically flat, bisimulationally deep)',
                 ONE_VAR, [word_chain('f-' * 13)])
    bad += report('alternating chains, q-witnesses (the shape of the old obstruction)',
                  TWO_VAR, [word_chain(w) for w in ('q-' * 13, '-q' * 13, 'qf' * 13, 'q-f-' * 7)])
    return bad

def cmd_ladders():
    models = [rn(20, rm, ft) for rm in ('id', 'full', 'left', 'right', 'even', 'toq')
              for ft in (None, 0, 1)]
    return report('Rieger–Nishimura ladders over q, six Rm patterns × three fallibility options',
                  LADDER, models)

def cmd_types():
    """The proof uses only two kinds of amalgam world.  Check that restricting
    the fixpoint to P = ∅ and P = (boxed bodies) \\ V changes no fibre."""
    models = [word_chain(w) for w in ('q-' * 8, '-q' * 8, 'qf' * 8, 'q-f-' * 4, 'f-' * 8)]
    models += [rn(12, rm, ft) for rm in ('id', 'full', 'left', 'right', 'even', 'toq')
               for ft in (None, 0, 1)]
    cells = sorted(set(ONE_VAR + TWO_VAR + LADDER), key=repr)
    tot = diff = 0
    for f in cells:
        X = closure(f); a, b = Fib(X, p), Fib2(X, p)
        for M in models:
            fa, fb = a.compute(M), b.compute(M)
            tot += M.n; diff += sum(1 for w in range(M.n) if fa[w] != fb[w])
    print(f'## types\n  {len(cells)} closures × {len(models)} models: {tot} world-cells, '
          f'{diff} where restricting to two kinds of type changes the fibre')
    return diff

def cmd_realisations():
    """Models on one poset with one set S of rigid non-fallible worlds force the
    same formulas pointwise, whatever their Rm-edges (w ⊩ ◯ξ iff every rigid
    non-fallible world above w forces ξ).  A fibre that depended on the
    realisation would make `SemExDefinable` false as formalised."""
    cells = [Imp(Box(pp), pp), Box(Imp(Box(pp), pp)), Imp(Imp(Box(pp), pp), Box(BOT)),
             Or(Box(pp), Neg(Box(pp))), Imp(Neg(Box(pp)), Box(Neg(pp))),
             Imp(Box(Imp(qq, pp)), Box(pp)), Imp(Imp(Box(pp), qq), Box(Or(pp, qq))),
             Imp(Box(Or(pp, qq)), Or(Box(pp), Box(qq))),
             Or(Imp(Box(pp), qq), Imp(Neg(Box(pp)), qq)), And(Box(pp), Box(Imp(pp, qq)))]
    probes = [Box(BOT), Neg(Box(BOT)), Box(qq), Neg(Box(qq)), Box(Neg(Box(qq))), Imp(Box(qq), qq),
              Box(Or(qq, Neg(Box(BOT)))), Neg(Neg(Box(qq)))]
    n, modes = 10, ['S', 'one', 'f', 'mix', 'all']
    tot = bad = 0
    for S in ({0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 4, 5}, {0, 1, 2, 3, 6}, {0, 1, 7}):
        Ms = [realise(n, S, md) for md in modes]
        for w in range(n + 1):
            for f in probes:
                assert len({M.force(w, f) for M in Ms}) == 1, 'realisations disagree p-free'
        for f in cells:
            fibs = [Fib(closure(f), p).compute(M) for M in Ms]
            for w in range(n + 1):
                tot += 1; bad += len({fi[w] for fi in fibs}) > 1
    # negative control: different rigid sets must give different fibres somewhere
    A, B = realise(n, {0, 1}, 'S'), realise(n, {0, 1, 2}, 'S')
    ctl = sum(1 for f in cells for w in range(n + 1)
              if Fib(closure(f), p).compute(A)[w] != Fib(closure(f), p).compute(B)[w])
    print(f'## realisations\n  {tot} (rigid set, closure, world) cells × {len(modes)} realisations: '
          f'{bad} with a realisation-dependent fibre')
    print(f'  negative control (rigid sets {{0,1}} against {{0,1,2}}): {ctl} cells differ (must be > 0)')
    return bad + (ctl == 0)

CMDS = {'validate': cmd_validate, 'chains': cmd_chains, 'ladders': cmd_ladders,
        'types': cmd_types, 'realisations': cmd_realisations}

if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which != 'all' and which not in CMDS:
        sys.exit(__doc__)
    fails = sum(CMDS[c]() for c in (CMDS if which == 'all' else [which]))
    sys.exit(1 if fails else 0)
