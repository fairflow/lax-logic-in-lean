/-
# The designed cells for B1 and B2 (join-family arity bounds)

`docs/a2-arity.md` §5.  The join conclusion contexts are pure list
functions of the family (`FRJ/Calculus.lean`, `FRJ/CalculusV.lean`,
`FRJ/RefAt.lean`), so a designed cell is an explicit family, and the
kernel decides it.  Every claim below is `decide`d against the
repository's own functions; nothing is `#eval`-only.

    B1.  In a join family, a premise whose goal another premise shares is
         redundant: the conclusion of the family is subsumed (context
         inclusion, same tag and goal) by the conclusion of the
         sub-family dropping it, and the sub-family satisfies the side
         conditions.

    B2 (as first sketched, REFUTED here).  A promise family can be cut
         to a hitting set for ⋃Ξ^◯ alone.

    B2'. A promise family can be cut to a hitting set for the modal
         formulas of ⋃Ξ^◯ and of ⋂Θ^◯ that the full family witnesses;
         so its arity is at most the number of distinct modal formulas
         of Ĝ.

Cells: B1-a (barren `⋈^At`, both duplicates droppable, kept chain
exercised through `RefAt.imp`), B1-a-control (dropping the premise with
the UNIQUE goal loses a kept implication -- the check is watched
failing), B1-b (promise `⋈^At`, same family under a promise family),
B2-refute (the naive hitting set loses `◯m₂`), B2' (the corrected one
keeps it).  Side-condition legality of each sub-family is decided
alongside.
-/
import FRJ.CalculusV
import FRJ.RefAt

open FRJ Form

namespace B1B2

/-! ## Families from lists -/

def famOf (l : List (List Form)) (n : Nat) : Fin (n + 1) → List Form :=
  fun j => l.getD j.val []

def rhsOf (l : List Form) (n : Nat) : Fin (n + 1) → Form :=
  fun j => l.getD j.val .bot

def tagsOf (l : List Tag) (n : Nat) : Fin (n + 1) → Tag :=
  fun j => l.getD j.val .barren

def subB (l m : List Form) : Bool := l.all (fun x => decide (x ∈ m))

/-! ## The side conditions of the joins, as Booleans -/

/-- (J1): `Ξᵢ ⊆ Ξⱼ ++ Θⱼ` for `i ≠ j`. -/
def j1B {n : Nat} (Ξs Θs : Fin (n + 1) → List Form) : Bool :=
  (List.finRange (n + 1)).all fun i => (List.finRange (n + 1)).all fun j =>
    i == j || subB (Ξs i) (Ξs j ++ Θs j)

/-- (J2): every implication of `⋃Ξ^⊃` has its antecedent in `Υ`. -/
def j2B {n : Nat} (Ξs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) : Bool :=
  (unionAll fun j => impPart (Ξs j)).all fun x =>
    match x with
    | .imp A _ => decide (A ∈ upsilon rhs)
    | _ => true

/-- (J3): no `◯` in a stable zone (barren joins). -/
def j3B {n : Nat} (Ξs : Fin (n + 1) → List Form) : Bool :=
  (unionAll fun j => circPart (Ξs j)).isEmpty

/-- `F` prime and not a stable atom. -/
def fOkB {n : Nat} (Ξs : Fin (n + 1) → List Form) (F : Form) : Bool :=
  F.isPrime && !(decide (F ∈ unionAll fun j => atPart (Ξs j)))

/-- (J5'): every `◯Y` of `⋃Ξ^◯` has a promise world with `Y ∈ Cl(Δᵢ)`. -/
def j5B {n k : Nat} (Ξs : Fin (n + 1) → List Form)
    (Δs : Fin (k + 1) → List Form) : Bool :=
  (unionAll fun j => circPart (Ξs j)).all fun x =>
    match x with
    | .circ Y => (List.finRange (k + 1)).any fun i => cloB (Δs i) Y
    | _ => true

/-- (J6): every stable formula lies in every `Cl(Δᵢ)`. -/
def j6B {n k : Nat} (Ξs : Fin (n + 1) → List Form)
    (Δs : Fin (k + 1) → List Form) : Bool :=
  (List.finRange (k + 1)).all fun i => (List.finRange (n + 1)).all fun j =>
    (Ξs j).all fun X => cloB (Δs i) X

/-- The barren `⋈^At` conclusion context (`FRJWr.joinAt`). -/
def ctxAt {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form) : List Form :=
  joinCtxAtVBase Ξs Θs F ++
    keptOf (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs)

/-! ## Atoms and formulas -/

def a₁ : Form := .atom "a1"
def a₂ : Form := .atom "a2"
def a₃ : Form := .atom "a3"
def b : Form := .atom "b"
def d : Form := .atom "d"
def f : Form := .atom "f"
def c₁ : Form := .atom "c1"
def c₂ : Form := .atom "c2"
def y : Form := .atom "y"
def v : Form := .atom "v"
def w : Form := .atom "w"
def e : Form := .atom "e"
def m₁ : Form := .atom "m1"
def m₂ : Form := .atom "m2"
def dd : Form := .atom "D"

/-! ## B1-a: barren `⋈^At`, goals c₁, c₁, c₂

    P0 :  [a₁]           ; [a₂, a₃, b, d, c₁⊃y, c₁⊃v, c₂⊃w, (d⊃c₁)⊃e]  → c₁
    P1 :  [a₂, d, c₁⊃v]  ; [a₁, a₃, b, c₂⊃w, c₁⊃y, (d⊃c₁)⊃e]           → c₁
    P2 :  []             ; [a₁, a₂, a₃, b, d, c₁⊃y, c₂⊃w, c₁⊃v, (d⊃c₁)⊃e] → c₂

`c₂ ⊃ w` reaches the conclusion only through the kept zone (antecedent
`c₂ ∈ Υ`), so it is the formula that dropping P2 must lose;
`(d ⊃ c₁) ⊃ e` is kept through `RefAt.imp` (`d ∈ Cl(ctx)`, `c₁ ∈ Υ`),
exercising the chain. -/

def chain : Form := .imp (.imp d c₁) e

def Ξ0 : List Form := [a₁]
def Θ0 : List Form := [a₂, a₃, b, d, .imp c₁ y, .imp c₁ v, .imp c₂ w, chain]
def Ξ1 : List Form := [a₂, d, .imp c₁ v]
def Θ1 : List Form := [a₁, a₃, b, .imp c₂ w, .imp c₁ y, chain]
def Ξ2 : List Form := []
def Θ2 : List Form := [a₁, a₂, a₃, b, d, .imp c₁ y, .imp c₂ w, .imp c₁ v, chain]

def ΞsF := famOf [Ξ0, Ξ1, Ξ2] 2
def ΘsF := famOf [Θ0, Θ1, Θ2] 2
def rhsF := rhsOf [c₁, c₁, c₂] 2

-- the full family is legal
example : j1B ΞsF ΘsF = true := by decide
example : j2B ΞsF rhsF = true := by decide
example : j3B ΞsF = true := by decide
example : fOkB ΞsF f = true := by decide

/-- The full conclusion context, for the record. -/
def ctxFull : List Form := ctxAt ΞsF ΘsF rhsF f

-- sub-family without P1 (a duplicate of goal c₁)
def Ξs01 := famOf [Ξ0, Ξ2] 1
def Θs01 := famOf [Θ0, Θ2] 1
def rhs01 := rhsOf [c₁, c₂] 1

example : j1B Ξs01 Θs01 = true := by decide
example : j2B Ξs01 rhs01 = true := by decide
example : j3B Ξs01 = true := by decide
example : fOkB Ξs01 f = true := by decide

/-- **B1-a, drop P1**: the sub-family's conclusion subsumes the family's. -/
theorem b1a_drop1 : subB ctxFull (ctxAt Ξs01 Θs01 rhs01 f) = true := by decide

-- sub-family without P0 (the other duplicate)
def Ξs12 := famOf [Ξ1, Ξ2] 1
def Θs12 := famOf [Θ1, Θ2] 1
def rhs12 := rhsOf [c₁, c₂] 1

example : j1B Ξs12 Θs12 = true := by decide
example : j2B Ξs12 rhs12 = true := by decide

/-- **B1-a, drop P0**. -/
theorem b1a_drop0 : subB ctxFull (ctxAt Ξs12 Θs12 rhs12 f) = true := by decide

-- CONTROL: drop P2, the only premise with goal c₂.  The sub-family is
-- illegal ((J2) fails: nothing, since c₂ ⊃ w sits in the Θ's, not the
-- Ξ's -- so (J2) still holds) but its Υ lost c₂, so the kept zone
-- loses c₂ ⊃ w and subsumption FAILS.  The check is watched failing.
def Ξs01c := famOf [Ξ0, Ξ1] 1
def Θs01c := famOf [Θ0, Θ1] 1
def rhs01c := rhsOf [c₁, c₁] 1

example : j1B Ξs01c Θs01c = true := by decide
example : j2B Ξs01c rhs01c = true := by decide

/-- **B1-a control**: dropping the unique-goal premise does NOT subsume. -/
theorem b1a_control : subB ctxFull (ctxAt Ξs01c Θs01c rhs01c f) = false := by decide

/-- …and the formula it loses is exactly `c₂ ⊃ w`. -/
theorem b1a_control_witness :
    (ctxFull.filter (fun x => !decide (x ∈ ctxAt Ξs01c Θs01c rhs01c f))) = [.imp c₂ w] := by
  decide

/-! ## B1-b: the promise `⋈^At` on the same irregular family

Promise family: one world `Δ₀ = [a₁, a₂, d, c₁⊃v, m₁]`, tag barren,
pledge `D`; (J6) needs every stable formula in `Cl(Δ₀)`.  The modal
part is exercised with `◯m₁` in every Θ. -/

def Θ0m : List Form := Θ0 ++ [.circ m₁]
def Θ1m : List Form := Θ1 ++ [.circ m₁]
def Θ2m : List Form := Θ2 ++ [.circ m₁]
def ΘsFm := famOf [Θ0m, Θ1m, Θ2m] 2
def Δ0 : List Form := [a₁, a₂, d, .imp c₁ v, m₁]
def Δs1 := famOf [Δ0] 0

example : j1B ΞsF ΘsFm = true := by decide
example : j6B ΞsF Δs1 = true := by decide
example : j5B ΞsF Δs1 = true := by decide

def ctxPFull : List Form := joinCtxAtP ΞsF ΘsFm rhsF f Δs1

def Θs01m := famOf [Θ0m, Θ2m] 1
def Θs12m := famOf [Θ1m, Θ2m] 1

/-- **B1-b, drop P1** (promise join). -/
theorem b1b_drop1 : subB ctxPFull (joinCtxAtP Ξs01 Θs01m rhs01 f Δs1) = true := by decide

/-- **B1-b, drop P0**. -/
theorem b1b_drop0 : subB ctxPFull (joinCtxAtP Ξs12 Θs12m rhs12 f Δs1) = true := by decide

/-- The promise conclusion keeps `◯m₁` (the modal part is live). -/
example : (Form.circ m₁) ∈ ctxPFull := by decide

/-! ## B2: promise-family arity

Irregular premise `P : [◯m₁] ; [◯m₂, a₁] → c₁`; promise family
`Δ₀ = [m₁, m₂, ◯m₂]`, `Δ₁ = [m₁, ◯m₂]`, both barren with pledge `D`.
Full conclusion keeps `◯m₂`: `restrictC` finds the witness `Δ₀`
(`m₂ ∈ Cl(Δ₀)`) and `restrictP` accepts it since `◯m₂` is literally in
both worlds.  The naive hitting set for `⋃Ξ^◯ = {◯m₁}` may pick `{Δ₁}`
alone (`m₁ ∈ Δ₁`); then `restrictC` has no witness for `◯m₂`. -/

def ΞP := famOf [[.circ m₁]] 0
def ΘP := famOf [[.circ m₂, a₁]] 0
def rhsP := rhsOf [c₁] 0
def Δ0b : List Form := [m₁, m₂, .circ m₂]
def Δ1b : List Form := [m₁, .circ m₂]
def ΔsBoth := famOf [Δ0b, Δ1b] 1
def ΔsOnly1 := famOf [Δ1b] 0
def ΔsOnly0 := famOf [Δ0b] 0

-- legality of the full promise family and of both singletons
example : j5B ΞP ΔsBoth = true := by decide
example : j6B ΞP ΔsBoth = true := by decide
example : j5B ΞP ΔsOnly1 = true := by decide
example : j6B ΞP ΔsOnly1 = true := by decide
example : j5B ΞP ΔsOnly0 = true := by decide
example : j6B ΞP ΔsOnly0 = true := by decide

def ctxB2Full : List Form := joinCtxAtP ΞP ΘP rhsP f ΔsBoth

example : (Form.circ m₂) ∈ ctxB2Full := by decide

/-- **B2 (naive) REFUTED**: the hitting set `{Δ₁}` for `⋃Ξ^◯` loses `◯m₂`. -/
theorem b2_naive_refuted : subB ctxB2Full (joinCtxAtP ΞP ΘP rhsP f ΔsOnly1) = false := by
  decide

theorem b2_naive_witness :
    (ctxB2Full.filter (fun x => !decide (x ∈ joinCtxAtP ΞP ΘP rhsP f ΔsOnly1))) =
      [.circ m₂] := by
  decide

/-- **B2'**: the hitting set `{Δ₀}` for `⋃Ξ^◯ ∪ (⋂Θ^◯ witnessed)` subsumes. -/
theorem b2_corrected : subB ctxB2Full (joinCtxAtP ΞP ΘP rhsP f ΔsOnly0) = true := by decide

/-! ## B1 under the RefAt-RELAXED (J2) of the barren `⋈^◯` (2026-09-02, night)

`DBClosed.joinCirc` (and `FRJWr.joinCirc`) guard a stable implication
`A ⊃ B` not by `A ∈ Υ` but by `RefAt true Υ (base ++ kept) A`, so a
dropped premise's stable implication may owe its licence to a KEPT link,
which the sub-family must first re-derive.  A 2-cycle (x owes L, L owes
x) would refute B1 here -- but it cannot be written: `Cl` sees an
implication only through its consequent, so every dependency descends
in formula size, and the transfer goes through by induction on size.
This cell is the shape that induction must handle: `xa`'s antecedent is
refuted only via the kept link `L`, whose own antecedent is refuted via
the atom `g` and `⊥`.

    P_a : [xa] ; [g, L]      → c        xa := ((w ⊃ L) ⊃ c) ⊃ da
    P_b : []   ; [g, L, xa]  → c        L  := (g ⊃ ⊥) ⊃ f

Strict (J2) FAILS for the family (`(w ⊃ L) ⊃ c ∉ Υ`), the relaxed one
holds; dropping either duplicate subsumes. -/

def g : Form := .atom "g"
def wv : Form := .atom "w"
def da : Form := .atom "da"
def fv : Form := .atom "f"
def cc : Form := .atom "c"
def Lk : Form := .imp (.imp g .bot) fv
def xa : Form := .imp (.imp (.imp wv Lk) cc) da

def ΞR := famOf [[xa], []] 1
def ΘR := famOf [[g, Lk], [g, Lk, xa]] 1
def rhsR := rhsOf [cc, cc] 1

/-- The barren `⋈^◯` conclusion context (`FRJWr.joinCirc`). -/
def ctxOr {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) : List Form :=
  joinCtxOrVBase Ξs Θs ++
    keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)

/-- The relaxed (J2) of `joinCirc`, as a Boolean. -/
def j2RelaxedB {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) : Bool :=
  (unionAll fun j => impPart (Ξs j)).all fun x =>
    match x with
    | .imp A _ => refAtB true (upsilon rhs) (ctxOr Ξs Θs rhs) A
    | _ => true

example : j1B ΞR ΘR = true := by decide
example : j3B ΞR = true := by decide
/-- The family is a genuinely relaxed instance: strict (J2) fails … -/
example : j2B ΞR rhsR = false := by decide
/-- … and the relaxed (J2) holds. -/
example : j2RelaxedB ΞR ΘR rhsR = true := by decide

def ctxRFull : List Form := ctxOr ΞR ΘR rhsR

example : xa ∈ ctxRFull := by decide
example : Lk ∈ ctxRFull := by decide

/-- **B1 under relaxed (J2), drop `P_a`**: the sub-family re-derives `L`,
then `xa`, through its kept chain. -/
theorem b1_relaxed_dropA :
    subB ctxRFull (ctxOr (famOf [[]] 0) (famOf [[g, Lk, xa]] 0) (rhsOf [cc] 0)) = true := by
  decide

/-- **B1 under relaxed (J2), drop `P_b`.** -/
theorem b1_relaxed_dropB :
    subB ctxRFull (ctxOr (famOf [[xa]] 0) (famOf [[g, Lk]] 0) (rhsOf [cc] 0)) = true := by
  decide

/-- info: 'B1B2.b1_relaxed_dropA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms b1_relaxed_dropA

/-! ## Pins (kernel-decided cells: `[propext]`, no choice)

These six lost `Quot.sound` at some point before 2026-09-04 and the pins
were never reconciled; the file is outside `lake build`'s default
targets, so nothing exercised them.  Corrected downward, which is the
permitted direction of the ratchet. -/

/-- info: 'B1B2.b1a_drop1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms b1a_drop1

/-- info: 'B1B2.b1a_control' depends on axioms: [propext] -/
#guard_msgs in
#print axioms b1a_control

/-- info: 'B1B2.b1b_drop1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms b1b_drop1

/-- info: 'B1B2.b2_naive_refuted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms b2_naive_refuted

/-- info: 'B1B2.b2_corrected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms b2_corrected

end B1B2
