/-!
# Believers on small Heyting algebras, enumerated in the kernel (§3b-5)

Clean-axiom counterpart of the `native_decide` counts that `Examples.lean`
carried until 2026-11-01, and the worked believer menagerie the Belief paper's
§3b-5 asked for.  A believer is a nucleus `j` — inflationary, idempotent,
meet-preserving.  Here five finite Heyting algebras are built as bare
inductive types with their lattice operations as match tables, believers are
represented as tuples of values (one per element), and every count and every
exhibit is computed by the kernel (`rfl` or `decide`) — no `native_decide`,
and no Mathlib vocabulary in any statement, so the audits stay clean (the
statement-vocabulary point of the paper's §9).

The algebras: the three- and four-element chains `C3`, `C4`; the four-element
Boolean algebra `B22`; and the two five-element non-linear Heyting algebras —
`K5t` (the four-element Boolean algebra with a new top adjoined:
`bot < a, b < m < top` with `m = a ⊔ b`) and `K5b` (the same square with a new
bottom adjoined: `bot < m < a, b < top` with `m = a ⊓ b`).

For each algebra the operation tables are verified against the laws (`le` is
reflexive, `inf` commutes, `sup` is the join, `himp` satisfies residuation:
the laws are fixed and a failing table would be a wrong table), the believers
are counted, and each believer is classified as closed (`c_v = · ⊔ v`,
dogmatic), open (`u_v = v ⇨ ·`, hypothetical), both, or neither.  Findings,
each kernel-checked below:

* `C3`: 4 believers; 3 closed, 3 open, 2 both, none neither.
* `C4`: 8 believers; 4 closed, 4 open, 2 both — and **2 neither**: already on
  the four-element chain there are believers that are neither dogmatic nor
  hypothetical (`c4Neither`, `c4Neither'`).
* `B22`: 4 believers = the 4 elements (the Boolean collapse, `N(B) ≅ B`), and
  every believer is simultaneously closed and open — hypothetical belief is
  invisible on a Boolean algebra (§3b-1, §3b-2).
* `K5t`, `K5b`: 8 believers each; 5 closed, 5 open, 2 both, none neither; the
  double-negation believer coincides with the open believer at `m` on both.
-/

namespace BeliefLax.Clean

/- The five-element enumerations walk lists of 3125 tuples; the elaborator's
defeq check recurses along the list, so it needs a deeper stack than the
default 512.  The kernel has no such limit and re-checks everything. -/
set_option maxRecDepth 8192

/-! ## The three-element chain `C3`: `b < m < t` -/

namespace C3

inductive X : Type where
  | b | m | t
deriving DecidableEq, Repr

open X

def allX : List X := [b, m, t]

def inf : X → X → X
  | .b, _ => b | _, .b => b
  | .m, .m => m | .m, .t => m | .t, .m => m
  | .t, .t => t

def sup : X → X → X
  | .t, _ => t | _, .t => t
  | .m, _ => m | _, .m => m
  | .b, .b => b

def himp : X → X → X
  | .b, _ => t
  | .m, .b => b | .m, .m => t | .m, .t => t
  | .t, y => y

def le (x y : X) : Bool := decide (inf x y = x)

theorem le_refl : ∀ x, le x x = true := by intro x; cases x <;> rfl
theorem inf_comm : ∀ x y, inf x y = inf y x := by
  intro x y; cases x <;> cases y <;> rfl
theorem sup_is_join : ∀ x y z, le (sup x y) z = (le x z && le y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
theorem residuation : ∀ x y z, le x (himp y z) = le (inf x y) z := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

/-- A believer as a tuple: the values at `b`, `m`, `t`. -/
abbrev T := X × X × X

def ap : T → X → X
  | (jb, _, _), .b => jb
  | (_, jm, _), .m => jm
  | (_, _, jt), .t => jt

def allT : List T :=
  allX.flatMap fun jb => allX.flatMap fun jm => allX.map fun jt => (jb, jm, jt)

/-- `j` is a nucleus (believer): inflationary, idempotent, meet-preserving. -/
def isNucleus (t : T) : Bool :=
  allX.all (fun x => le x (ap t x))
  && allX.all (fun x => decide (ap t (ap t x) = ap t x))
  && allX.all (fun x => allX.all fun y =>
      decide (ap t (inf x y) = inf (ap t x) (ap t y)))

def nuclei : List T := allT.filter isNucleus

/-- Closed (dogmatic): `j = · ⊔ v` for some `v`. -/
def isClosed (t : T) : Bool :=
  allX.any fun v => allX.all fun x => decide (ap t x = sup x v)

/-- Open (hypothetical): `j = v ⇨ ·` for some `v`. -/
def isOpen (t : T) : Bool :=
  allX.any fun v => allX.all fun x => decide (ap t x = himp v x)

theorem mem_allX : ∀ x : X, x ∈ allX := by intro x; cases x <;> decide

/-- What the Boolean check says: the three nucleus laws, pointwise. -/
theorem isNucleus_iff (t : T) : isNucleus t = true ↔
    (∀ x, le x (ap t x) = true) ∧ (∀ x, ap t (ap t x) = ap t x) ∧
    (∀ x y, ap t (inf x y) = inf (ap t x) (ap t y)) := by
  simp only [isNucleus, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ =>
      ⟨fun x => h1 x (mem_allX x), fun x => h2 x (mem_allX x),
       fun x y => h3 x (mem_allX x) y (mem_allX y)⟩,
    fun ⟨h1, h2, h3⟩ =>
      ⟨⟨fun x _ => h1 x, fun x _ => h2 x⟩, fun x _ y _ => h3 x y⟩⟩

/-- The three-element chain has exactly **four** believers (the clean twin of
`chain3_card`, whose Mathlib statement vocabulary carries choice). -/
theorem nuclei_card : nuclei.length = 4 := rfl

theorem closed_card : (nuclei.filter isClosed).length = 3 := rfl
theorem open_card : (nuclei.filter isOpen).length = 3 := rfl
theorem both_card :
    (nuclei.filter fun t => isClosed t && isOpen t).length = 2 := rfl
theorem neither_card :
    (nuclei.filter fun t => !(isClosed t || isOpen t)).length = 0 := rfl

end C3

/-! ## The four-element chain `C4`: `b < p < q < t` -/

namespace C4

inductive X : Type where
  | b | p | q | t
deriving DecidableEq, Repr

open X

def allX : List X := [b, p, q, t]

def inf : X → X → X
  | .b, _ => b | _, .b => b
  | .p, _ => p | _, .p => p
  | .q, .q => q | .q, .t => q | .t, .q => q
  | .t, .t => t

def sup : X → X → X
  | .t, _ => t | _, .t => t
  | .q, _ => q | _, .q => q
  | .p, _ => p | _, .p => p
  | .b, .b => b

def himp : X → X → X
  | .b, _ => t
  | .p, .b => b | .p, _ => t
  | .q, .b => b | .q, .p => p | .q, _ => t
  | .t, y => y

def le (x y : X) : Bool := decide (inf x y = x)

theorem le_refl : ∀ x, le x x = true := by intro x; cases x <;> rfl
theorem inf_comm : ∀ x y, inf x y = inf y x := by
  intro x y; cases x <;> cases y <;> rfl
theorem sup_is_join : ∀ x y z, le (sup x y) z = (le x z && le y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
theorem residuation : ∀ x y z, le x (himp y z) = le (inf x y) z := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

abbrev T := X × X × X × X

def ap : T → X → X
  | (jb, _, _, _), .b => jb
  | (_, jp, _, _), .p => jp
  | (_, _, jq, _), .q => jq
  | (_, _, _, jt), .t => jt

def allT : List T :=
  allX.flatMap fun jb => allX.flatMap fun jp => allX.flatMap fun jq =>
    allX.map fun jt => (jb, jp, jq, jt)

def isNucleus (t : T) : Bool :=
  allX.all (fun x => le x (ap t x))
  && allX.all (fun x => decide (ap t (ap t x) = ap t x))
  && allX.all (fun x => allX.all fun y =>
      decide (ap t (inf x y) = inf (ap t x) (ap t y)))

def nuclei : List T := allT.filter isNucleus

def isClosed (t : T) : Bool :=
  allX.any fun v => allX.all fun x => decide (ap t x = sup x v)

def isOpen (t : T) : Bool :=
  allX.any fun v => allX.all fun x => decide (ap t x = himp v x)

theorem mem_allX : ∀ x : X, x ∈ allX := by intro x; cases x <;> decide

theorem isNucleus_iff (t : T) : isNucleus t = true ↔
    (∀ x, le x (ap t x) = true) ∧ (∀ x, ap t (ap t x) = ap t x) ∧
    (∀ x y, ap t (inf x y) = inf (ap t x) (ap t y)) := by
  simp only [isNucleus, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ =>
      ⟨fun x => h1 x (mem_allX x), fun x => h2 x (mem_allX x),
       fun x y => h3 x (mem_allX x) y (mem_allX y)⟩,
    fun ⟨h1, h2, h3⟩ =>
      ⟨⟨fun x _ => h1 x, fun x _ => h2 x⟩, fun x _ y _ => h3 x y⟩⟩

/-- Fixed points `{p, t}`: neither dogmatic nor hypothetical. -/
def c4Neither : T := (p, p, t, t)

/-- Fixed points `{b, q, t}`: the other believer that is neither. -/
def c4Neither' : T := (b, q, q, t)

/-- The four-element chain has exactly **eight** believers
(the clean replacement of the former `native_decide` count `chain4_card`). -/
theorem nuclei_card : nuclei.length = 8 := rfl

theorem closed_card : (nuclei.filter isClosed).length = 4 := rfl
theorem open_card : (nuclei.filter isOpen).length = 4 := rfl
theorem both_card :
    (nuclei.filter fun t => isClosed t && isOpen t).length = 2 := rfl

/-- Already on the four-element chain, **two** believers are neither
dogmatic nor hypothetical. -/
theorem neither_card :
    (nuclei.filter fun t => !(isClosed t || isOpen t)).length = 2 := rfl

/-- The two believers that are neither, exactly. -/
theorem neither_exact :
    (nuclei.filter fun t => !(isClosed t || isOpen t))
      = [c4Neither', c4Neither] := rfl

theorem c4Neither_isNucleus : isNucleus c4Neither = true := rfl
theorem c4Neither_not_closed : isClosed c4Neither = false := rfl
theorem c4Neither_not_open : isOpen c4Neither = false := rfl

end C4

/-! ## The four-element Boolean algebra `B22`: `bot < l, r < top` -/

namespace B22

inductive X : Type where
  | bot | l | r | top
deriving DecidableEq, Repr

open X

def allX : List X := [bot, l, r, top]

def inf : X → X → X
  | .bot, _ => bot | _, .bot => bot
  | .top, y => y | x, .top => x
  | .l, .l => l | .l, .r => bot
  | .r, .l => bot | .r, .r => r

def sup : X → X → X
  | .top, _ => top | _, .top => top
  | .bot, y => y | x, .bot => x
  | .l, .l => l | .l, .r => top
  | .r, .l => top | .r, .r => r

def himp : X → X → X
  | .bot, _ => top
  | .top, y => y
  | .l, .bot => r | .l, .l => top | .l, .r => r | .l, .top => top
  | .r, .bot => l | .r, .l => l | .r, .r => top | .r, .top => top

def le (x y : X) : Bool := decide (inf x y = x)

theorem le_refl : ∀ x, le x x = true := by intro x; cases x <;> rfl
theorem inf_comm : ∀ x y, inf x y = inf y x := by
  intro x y; cases x <;> cases y <;> rfl
theorem sup_is_join : ∀ x y z, le (sup x y) z = (le x z && le y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
theorem residuation : ∀ x y z, le x (himp y z) = le (inf x y) z := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

abbrev T := X × X × X × X

def ap : T → X → X
  | (jb, _, _, _), .bot => jb
  | (_, jl, _, _), .l => jl
  | (_, _, jr, _), .r => jr
  | (_, _, _, jt), .top => jt

def allT : List T :=
  allX.flatMap fun jb => allX.flatMap fun jl => allX.flatMap fun jr =>
    allX.map fun jt => (jb, jl, jr, jt)

def isNucleus (t : T) : Bool :=
  allX.all (fun x => le x (ap t x))
  && allX.all (fun x => decide (ap t (ap t x) = ap t x))
  && allX.all (fun x => allX.all fun y =>
      decide (ap t (inf x y) = inf (ap t x) (ap t y)))

def nuclei : List T := allT.filter isNucleus

def isClosed (t : T) : Bool :=
  allX.any fun v => allX.all fun x => decide (ap t x = sup x v)

def isOpen (t : T) : Bool :=
  allX.any fun v => allX.all fun x => decide (ap t x = himp v x)

theorem mem_allX : ∀ x : X, x ∈ allX := by intro x; cases x <;> decide

theorem isNucleus_iff (t : T) : isNucleus t = true ↔
    (∀ x, le x (ap t x) = true) ∧ (∀ x, ap t (ap t x) = ap t x) ∧
    (∀ x y, ap t (inf x y) = inf (ap t x) (ap t y)) := by
  simp only [isNucleus, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ =>
      ⟨fun x => h1 x (mem_allX x), fun x => h2 x (mem_allX x),
       fun x y => h3 x (mem_allX x) y (mem_allX y)⟩,
    fun ⟨h1, h2, h3⟩ =>
      ⟨⟨fun x _ => h1 x, fun x _ => h2 x⟩, fun x _ y _ => h3 x y⟩⟩

/-- The four-element Boolean algebra has exactly **four** believers — its four
elements, a computed instance of the collapse `N(B) ≅ B` (§3b-1; the clean
replacement of the former `native_decide` count `boolean22_card`). -/
theorem nuclei_card : nuclei.length = 4 := rfl

/-- On the Boolean algebra every believer is dogmatic **and** hypothetical at
once: the closed and open families coincide (§3b-2, computed). -/
theorem all_closed_and_open :
    (nuclei.all fun t => isClosed t && isOpen t) = true := rfl

end B22

/-! ## The five-element kite `K5t`: `bot < a, b < m < top`, `m = a ⊔ b` -/

namespace K5t

inductive X : Type where
  | bot | a | b | m | top
deriving DecidableEq, Repr

open X

def allX : List X := [bot, a, b, m, top]

def inf : X → X → X
  | .bot, _ => bot | _, .bot => bot
  | .top, y => y | x, .top => x
  | .a, .a => a | .a, .b => bot | .a, .m => a
  | .b, .a => bot | .b, .b => b | .b, .m => b
  | .m, .a => a | .m, .b => b | .m, .m => m

def sup : X → X → X
  | .top, _ => top | _, .top => top
  | .bot, y => y | x, .bot => x
  | .a, .a => a | .a, .b => m | .a, .m => m
  | .b, .a => m | .b, .b => b | .b, .m => m
  | .m, _ => m

def himp : X → X → X
  | .bot, _ => top
  | .a, .bot => b | .a, .a => top | .a, .b => b | .a, .m => top | .a, .top => top
  | .b, .bot => a | .b, .a => a | .b, .b => top | .b, .m => top | .b, .top => top
  | .m, .bot => bot | .m, .a => a | .m, .b => b | .m, .m => top | .m, .top => top
  | .top, y => y

def le (x y : X) : Bool := decide (inf x y = x)

theorem le_refl : ∀ x, le x x = true := by intro x; cases x <;> rfl
theorem inf_comm : ∀ x y, inf x y = inf y x := by
  intro x y; cases x <;> cases y <;> rfl
theorem sup_is_join : ∀ x y z, le (sup x y) z = (le x z && le y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
theorem residuation : ∀ x y z, le x (himp y z) = le (inf x y) z := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

/-- A believer as a tuple: values at `bot`, `a`, `b`, `m`, `top`. -/
abbrev T := X × X × X × X × X

def ap : T → X → X
  | (j0, _, _, _, _), .bot => j0
  | (_, j1, _, _, _), .a => j1
  | (_, _, j2, _, _), .b => j2
  | (_, _, _, j3, _), .m => j3
  | (_, _, _, _, j4), .top => j4

def allT : List T :=
  allX.flatMap fun j0 => allX.flatMap fun j1 => allX.flatMap fun j2 =>
    allX.flatMap fun j3 => allX.map fun j4 => (j0, j1, j2, j3, j4)

def isNucleus (t : T) : Bool :=
  allX.all (fun x => le x (ap t x))
  && allX.all (fun x => decide (ap t (ap t x) = ap t x))
  && allX.all (fun x => allX.all fun y =>
      decide (ap t (inf x y) = inf (ap t x) (ap t y)))

def nuclei : List T := allT.filter isNucleus

def isClosed (t : T) : Bool :=
  allX.any fun v => allX.all fun x => decide (ap t x = sup x v)

def isOpen (t : T) : Bool :=
  allX.any fun v => allX.all fun x => decide (ap t x = himp v x)

theorem mem_allX : ∀ x : X, x ∈ allX := by intro x; cases x <;> decide

theorem isNucleus_iff (t : T) : isNucleus t = true ↔
    (∀ x, le x (ap t x) = true) ∧ (∀ x, ap t (ap t x) = ap t x) ∧
    (∀ x y, ap t (inf x y) = inf (ap t x) (ap t y)) := by
  simp only [isNucleus, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ =>
      ⟨fun x => h1 x (mem_allX x), fun x => h2 x (mem_allX x),
       fun x y => h3 x (mem_allX x) y (mem_allX y)⟩,
    fun ⟨h1, h2, h3⟩ =>
      ⟨⟨fun x _ => h1 x, fun x _ => h2 x⟩, fun x _ y _ => h3 x y⟩⟩

/-- The total sceptic: the identity. -/
def sceptic : T := (bot, a, b, m, top)
/-- The totally credulous believer: constant `top`. -/
def credulous : T := (top, top, top, top, top)
/-- Dogmatic (closed) at `a`: `· ⊔ a`. -/
def closedA : T := (a, a, m, m, top)
/-- Dogmatic (closed) at `b`. -/
def closedB : T := (b, m, b, m, top)
/-- Dogmatic (closed) at `m`. -/
def closedM : T := (m, m, m, m, top)
/-- Hypothetical (open) at `a`: `a ⇨ ·`. -/
def openA : T := (b, top, b, top, top)
/-- Hypothetical (open) at `b`. -/
def openB : T := (a, a, top, top, top)
/-- Hypothetical (open) at `m`. -/
def openM : T := (bot, a, b, top, top)

/-- The double-negation believer `x ↦ ((x ⇨ ⊥) ⇨ ⊥)`, computed pointwise. -/
def notnotFun (x : X) : X := himp (himp x bot) bot
def notnot : T :=
  (notnotFun bot, notnotFun a, notnotFun b, notnotFun m, notnotFun top)

/-- The upward kite has exactly **eight** believers. -/
theorem nuclei_card : nuclei.length = 8 := rfl

theorem closed_card : (nuclei.filter isClosed).length = 5 := rfl
theorem open_card : (nuclei.filter isOpen).length = 5 := rfl
theorem both_card :
    (nuclei.filter fun t => isClosed t && isOpen t).length = 2 := rfl
theorem neither_card :
    (nuclei.filter fun t => !(isClosed t || isOpen t)).length = 0 := rfl

/-- On the upward kite every believer is dogmatic or hypothetical. -/
theorem all_closed_or_open :
    (nuclei.all fun t => isClosed t || isOpen t) = true := rfl

set_option maxRecDepth 32768 in
/-- The complete menagerie: the eight believers are exactly the named ones. -/
theorem nuclei_exact :
    nuclei = [sceptic, openM, closedA, openB, closedB, openA,
              closedM, credulous] := rfl

theorem sceptic_isNucleus : isNucleus sceptic = true := rfl
theorem credulous_isNucleus : isNucleus credulous = true := rfl
theorem closedA_isNucleus : isNucleus closedA = true := rfl
theorem closedB_isNucleus : isNucleus closedB = true := rfl
theorem closedM_isNucleus : isNucleus closedM = true := rfl
theorem openA_isNucleus : isNucleus openA = true := rfl
theorem openB_isNucleus : isNucleus openB = true := rfl
theorem openM_isNucleus : isNucleus openM = true := rfl

/-- On the upward kite the double-negation believer is the open believer
at `m` — hypothetical belief in disguise. -/
theorem notnot_eq_openM : notnot = openM := rfl

theorem openA_ne_closedA : openA ≠ closedA := by decide
theorem openM_ne_closedM : openM ≠ closedM := by decide

end K5t

/-! ## The five-element kite `K5b`: `bot < m < a, b < top`, `m = a ⊓ b` -/

namespace K5b

inductive X : Type where
  | bot | m | a | b | top
deriving DecidableEq, Repr

open X

def allX : List X := [bot, m, a, b, top]

def inf : X → X → X
  | .bot, _ => bot | _, .bot => bot
  | .top, y => y | x, .top => x
  | .m, _ => m | _, .m => m
  | .a, .a => a | .a, .b => m
  | .b, .a => m | .b, .b => b

def sup : X → X → X
  | .top, _ => top | _, .top => top
  | .bot, y => y | x, .bot => x
  | .m, y => y | x, .m => x
  | .a, .a => a | .a, .b => top
  | .b, .a => top | .b, .b => b

def himp : X → X → X
  | .bot, _ => top
  | .m, .bot => bot | .m, _ => top
  | .a, .bot => bot | .a, .m => b | .a, .a => top | .a, .b => b | .a, .top => top
  | .b, .bot => bot | .b, .m => a | .b, .a => a | .b, .b => top | .b, .top => top
  | .top, y => y

def le (x y : X) : Bool := decide (inf x y = x)

theorem le_refl : ∀ x, le x x = true := by intro x; cases x <;> rfl
theorem inf_comm : ∀ x y, inf x y = inf y x := by
  intro x y; cases x <;> cases y <;> rfl
theorem sup_is_join : ∀ x y z, le (sup x y) z = (le x z && le y z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
theorem residuation : ∀ x y z, le x (himp y z) = le (inf x y) z := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl

/-- A believer as a tuple: values at `bot`, `m`, `a`, `b`, `top`. -/
abbrev T := X × X × X × X × X

def ap : T → X → X
  | (j0, _, _, _, _), .bot => j0
  | (_, j1, _, _, _), .m => j1
  | (_, _, j2, _, _), .a => j2
  | (_, _, _, j3, _), .b => j3
  | (_, _, _, _, j4), .top => j4

def allT : List T :=
  allX.flatMap fun j0 => allX.flatMap fun j1 => allX.flatMap fun j2 =>
    allX.flatMap fun j3 => allX.map fun j4 => (j0, j1, j2, j3, j4)

def isNucleus (t : T) : Bool :=
  allX.all (fun x => le x (ap t x))
  && allX.all (fun x => decide (ap t (ap t x) = ap t x))
  && allX.all (fun x => allX.all fun y =>
      decide (ap t (inf x y) = inf (ap t x) (ap t y)))

def nuclei : List T := allT.filter isNucleus

def isClosed (t : T) : Bool :=
  allX.any fun v => allX.all fun x => decide (ap t x = sup x v)

def isOpen (t : T) : Bool :=
  allX.any fun v => allX.all fun x => decide (ap t x = himp v x)

theorem mem_allX : ∀ x : X, x ∈ allX := by intro x; cases x <;> decide

theorem isNucleus_iff (t : T) : isNucleus t = true ↔
    (∀ x, le x (ap t x) = true) ∧ (∀ x, ap t (ap t x) = ap t x) ∧
    (∀ x y, ap t (inf x y) = inf (ap t x) (ap t y)) := by
  simp only [isNucleus, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ =>
      ⟨fun x => h1 x (mem_allX x), fun x => h2 x (mem_allX x),
       fun x y => h3 x (mem_allX x) y (mem_allX y)⟩,
    fun ⟨h1, h2, h3⟩ =>
      ⟨⟨fun x _ => h1 x, fun x _ => h2 x⟩, fun x _ y _ => h3 x y⟩⟩

/-- The total sceptic: the identity. -/
def sceptic : T := (bot, m, a, b, top)
/-- The totally credulous believer: constant `top`. -/
def credulous : T := (top, top, top, top, top)
/-- Dogmatic (closed) at `a`: `· ⊔ a`. -/
def closedA : T := (a, a, a, top, top)
/-- Dogmatic (closed) at `b`. -/
def closedB : T := (b, b, top, b, top)
/-- Dogmatic (closed) at `m`. -/
def closedM : T := (m, m, a, b, top)
/-- Hypothetical (open) at `a`: `a ⇨ ·`. -/
def openA : T := (bot, b, top, b, top)
/-- Hypothetical (open) at `b`. -/
def openB : T := (bot, a, a, top, top)
/-- Hypothetical (open) at `m`. -/
def openM : T := (bot, top, top, top, top)

/-- The double-negation believer `x ↦ ((x ⇨ ⊥) ⇨ ⊥)`, computed pointwise. -/
def notnotFun (x : X) : X := himp (himp x bot) bot
def notnot : T :=
  (notnotFun bot, notnotFun m, notnotFun a, notnotFun b, notnotFun top)

/-- The downward kite has exactly **eight** believers. -/
theorem nuclei_card : nuclei.length = 8 := rfl

theorem closed_card : (nuclei.filter isClosed).length = 5 := rfl
theorem open_card : (nuclei.filter isOpen).length = 5 := rfl
theorem both_card :
    (nuclei.filter fun t => isClosed t && isOpen t).length = 2 := rfl
theorem neither_card :
    (nuclei.filter fun t => !(isClosed t || isOpen t)).length = 0 := rfl

/-- On the downward kite every believer is dogmatic or hypothetical. -/
theorem all_closed_or_open :
    (nuclei.all fun t => isClosed t || isOpen t) = true := rfl

set_option maxRecDepth 32768 in
/-- The complete menagerie: the eight believers are exactly the named ones. -/
theorem nuclei_exact :
    nuclei = [sceptic, openB, openA, openM, closedM, closedA,
              closedB, credulous] := rfl

theorem sceptic_isNucleus : isNucleus sceptic = true := rfl
theorem credulous_isNucleus : isNucleus credulous = true := rfl
theorem closedA_isNucleus : isNucleus closedA = true := rfl
theorem closedB_isNucleus : isNucleus closedB = true := rfl
theorem closedM_isNucleus : isNucleus closedM = true := rfl
theorem openA_isNucleus : isNucleus openA = true := rfl
theorem openB_isNucleus : isNucleus openB = true := rfl
theorem openM_isNucleus : isNucleus openM = true := rfl

/-- On the downward kite too, the double-negation believer is the open
believer at `m`. -/
theorem notnot_eq_openM : notnot = openM := rfl

theorem openA_ne_closedA : openA ≠ closedA := by decide
theorem openM_ne_closedM : openM ≠ closedM := by decide

end K5b

/-! ### Axiom pins — measured by `#print axioms`, frozen by `#guard_msgs` -/

/-- info: 'BeliefLax.Clean.C3.le_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms C3.le_refl

/-- info: 'BeliefLax.Clean.C3.inf_comm' does not depend on any axioms -/
#guard_msgs in
#print axioms C3.inf_comm

/-- info: 'BeliefLax.Clean.C3.sup_is_join' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C3.sup_is_join

/-- info: 'BeliefLax.Clean.C3.residuation' does not depend on any axioms -/
#guard_msgs in
#print axioms C3.residuation

/-- info: 'BeliefLax.Clean.C3.mem_allX' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C3.mem_allX

/-- info: 'BeliefLax.Clean.C3.isNucleus_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms C3.isNucleus_iff

/-- info: 'BeliefLax.Clean.C3.nuclei_card' does not depend on any axioms -/
#guard_msgs in
#print axioms C3.nuclei_card

/-- info: 'BeliefLax.Clean.C3.closed_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C3.closed_card

/-- info: 'BeliefLax.Clean.C3.open_card' does not depend on any axioms -/
#guard_msgs in
#print axioms C3.open_card

/-- info: 'BeliefLax.Clean.C3.both_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C3.both_card

/-- info: 'BeliefLax.Clean.C3.neither_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C3.neither_card

/-- info: 'BeliefLax.Clean.C4.le_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.le_refl

/-- info: 'BeliefLax.Clean.C4.inf_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.inf_comm

/-- info: 'BeliefLax.Clean.C4.sup_is_join' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.sup_is_join

/-- info: 'BeliefLax.Clean.C4.residuation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.residuation

/-- info: 'BeliefLax.Clean.C4.mem_allX' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.mem_allX

/-- info: 'BeliefLax.Clean.C4.isNucleus_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms C4.isNucleus_iff

/-- info: 'BeliefLax.Clean.C4.nuclei_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.nuclei_card

/-- info: 'BeliefLax.Clean.C4.closed_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.closed_card

/-- info: 'BeliefLax.Clean.C4.open_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.open_card

/-- info: 'BeliefLax.Clean.C4.both_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.both_card

/-- info: 'BeliefLax.Clean.C4.neither_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.neither_card

/-- info: 'BeliefLax.Clean.C4.neither_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.neither_exact

/-- info: 'BeliefLax.Clean.C4.c4Neither_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.c4Neither_isNucleus

/-- info: 'BeliefLax.Clean.C4.c4Neither_not_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.c4Neither_not_closed

/-- info: 'BeliefLax.Clean.C4.c4Neither_not_open' depends on axioms: [propext] -/
#guard_msgs in
#print axioms C4.c4Neither_not_open

/-- info: 'BeliefLax.Clean.B22.le_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms B22.le_refl

/-- info: 'BeliefLax.Clean.B22.inf_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms B22.inf_comm

/-- info: 'BeliefLax.Clean.B22.sup_is_join' depends on axioms: [propext] -/
#guard_msgs in
#print axioms B22.sup_is_join

/-- info: 'BeliefLax.Clean.B22.residuation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms B22.residuation

/-- info: 'BeliefLax.Clean.B22.mem_allX' depends on axioms: [propext] -/
#guard_msgs in
#print axioms B22.mem_allX

/-- info: 'BeliefLax.Clean.B22.isNucleus_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms B22.isNucleus_iff

/-- info: 'BeliefLax.Clean.B22.nuclei_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms B22.nuclei_card

/-- info: 'BeliefLax.Clean.B22.all_closed_and_open' depends on axioms: [propext] -/
#guard_msgs in
#print axioms B22.all_closed_and_open

/-- info: 'BeliefLax.Clean.K5t.le_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.le_refl

/-- info: 'BeliefLax.Clean.K5t.inf_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.inf_comm

/-- info: 'BeliefLax.Clean.K5t.sup_is_join' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.sup_is_join

/-- info: 'BeliefLax.Clean.K5t.residuation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.residuation

/-- info: 'BeliefLax.Clean.K5t.mem_allX' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.mem_allX

/-- info: 'BeliefLax.Clean.K5t.isNucleus_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms K5t.isNucleus_iff

/-- info: 'BeliefLax.Clean.K5t.nuclei_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.nuclei_card

/-- info: 'BeliefLax.Clean.K5t.closed_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.closed_card

/-- info: 'BeliefLax.Clean.K5t.open_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.open_card

/-- info: 'BeliefLax.Clean.K5t.both_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.both_card

/-- info: 'BeliefLax.Clean.K5t.neither_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.neither_card

/-- info: 'BeliefLax.Clean.K5t.all_closed_or_open' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.all_closed_or_open

/-- info: 'BeliefLax.Clean.K5t.nuclei_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.nuclei_exact

/-- info: 'BeliefLax.Clean.K5t.sceptic_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.sceptic_isNucleus

/-- info: 'BeliefLax.Clean.K5t.credulous_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.credulous_isNucleus

/-- info: 'BeliefLax.Clean.K5t.closedA_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.closedA_isNucleus

/-- info: 'BeliefLax.Clean.K5t.closedB_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.closedB_isNucleus

/-- info: 'BeliefLax.Clean.K5t.closedM_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.closedM_isNucleus

/-- info: 'BeliefLax.Clean.K5t.openA_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.openA_isNucleus

/-- info: 'BeliefLax.Clean.K5t.openB_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.openB_isNucleus

/-- info: 'BeliefLax.Clean.K5t.openM_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5t.openM_isNucleus

/-- info: 'BeliefLax.Clean.K5t.notnot_eq_openM' does not depend on any axioms -/
#guard_msgs in
#print axioms K5t.notnot_eq_openM

/-- info: 'BeliefLax.Clean.K5t.openA_ne_closedA' does not depend on any axioms -/
#guard_msgs in
#print axioms K5t.openA_ne_closedA

/-- info: 'BeliefLax.Clean.K5t.openM_ne_closedM' does not depend on any axioms -/
#guard_msgs in
#print axioms K5t.openM_ne_closedM

/-- info: 'BeliefLax.Clean.K5b.le_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.le_refl

/-- info: 'BeliefLax.Clean.K5b.inf_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.inf_comm

/-- info: 'BeliefLax.Clean.K5b.sup_is_join' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.sup_is_join

/-- info: 'BeliefLax.Clean.K5b.residuation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.residuation

/-- info: 'BeliefLax.Clean.K5b.mem_allX' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.mem_allX

/-- info: 'BeliefLax.Clean.K5b.isNucleus_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms K5b.isNucleus_iff

/-- info: 'BeliefLax.Clean.K5b.nuclei_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.nuclei_card

/-- info: 'BeliefLax.Clean.K5b.closed_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.closed_card

/-- info: 'BeliefLax.Clean.K5b.open_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.open_card

/-- info: 'BeliefLax.Clean.K5b.both_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.both_card

/-- info: 'BeliefLax.Clean.K5b.neither_card' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.neither_card

/-- info: 'BeliefLax.Clean.K5b.all_closed_or_open' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.all_closed_or_open

/-- info: 'BeliefLax.Clean.K5b.nuclei_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.nuclei_exact

/-- info: 'BeliefLax.Clean.K5b.sceptic_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.sceptic_isNucleus

/-- info: 'BeliefLax.Clean.K5b.credulous_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.credulous_isNucleus

/-- info: 'BeliefLax.Clean.K5b.closedA_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.closedA_isNucleus

/-- info: 'BeliefLax.Clean.K5b.closedB_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.closedB_isNucleus

/-- info: 'BeliefLax.Clean.K5b.closedM_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.closedM_isNucleus

/-- info: 'BeliefLax.Clean.K5b.openA_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.openA_isNucleus

/-- info: 'BeliefLax.Clean.K5b.openB_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.openB_isNucleus

/-- info: 'BeliefLax.Clean.K5b.openM_isNucleus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.openM_isNucleus

/-- info: 'BeliefLax.Clean.K5b.notnot_eq_openM' depends on axioms: [propext] -/
#guard_msgs in
#print axioms K5b.notnot_eq_openM

/-- info: 'BeliefLax.Clean.K5b.openA_ne_closedA' does not depend on any axioms -/
#guard_msgs in
#print axioms K5b.openA_ne_closedA

/-- info: 'BeliefLax.Clean.K5b.openM_ne_closedM' does not depend on any axioms -/
#guard_msgs in
#print axioms K5b.openM_ne_closedM

end BeliefLax.Clean
