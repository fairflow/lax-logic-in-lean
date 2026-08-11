/-
θ-family extraction (the refutation prong, 2026-08-11).

Step 1: print the even fuel chain A_2, A_4, A_6 of `interpF` at the
GZ-candidate station

  S = [◯p ⊃ r, ◯q],  goal G = ↑↓◯p,  eliminated variable p

as readable PLL formulas.  Raw `interpF` values are choked with the units
`⊤ = ⊥ ⊃ ⊥` and `⊥` that `nAndAll`/`nOrAll` fold in, so a normaliser runs
first.  Every rewrite it performs is an intuitionistic equivalence:

  ⊤∧A ⟛ A,  A∧⊤ ⟛ A,  ⊥∨A ⟛ A,  A∨⊥ ⟛ A,  A∧A ⟛ A,  A∨A ⟛ A,
  ⊥∧A ⟛ ⊥,  ⊤∨A ⟛ ⊤,  ⊥⊃A ⟛ ⊤,  A⊃⊤ ⟛ ⊤,  ⊤⊃A ⟛ A,  A⊃A ⟛ ⊤,  ◯⊤ ⟛ ⊤

plus (second pass, `mpPass`) conjunction-level modus ponens

  X ∧ (X ⊃ Y) ⟛ X ∧ Y

which is an equivalence in both directions.  Nothing here is trusted: the
θ-family that comes out is re-verified against the raw A_f by
`prove?Bounded` in both directions (wip/ljfo_theta_run.lean).
-/
import LaxLogic.LJFOFuel
import LaxLogic.PLLSearch
import wip.ljfo_attack

open LJFO LJFOAttack PLLND

namespace Theta

/-! ## The candidate cell -/

/-- The A-chain (∀p mode) at the GZ-candidate station. -/
def chainA (S : List Neg) (Q' : Pos) (f : Nat) : Neg :=
  interpF pv f [] S (some (.up (.down (.circ Q'))))

/-- The E-chain (∃p mode) at the same station. -/
def chainE (S : List Neg) (f : Nat) : Neg := interpF pv f [] S none

/-- `S = [◯p ⊃ r, ◯q]`. -/
def stationS : List Neg := [hyp, boxQ]

/-- `A_f` as a PLL formula. -/
def A (f : Nat) : PLLFormula := negF (chainA stationS aP f)

/-- `E_f` as a PLL formula. -/
def E (f : Nat) : PLLFormula := negF (chainE stationS f)

/-! ## Syntactic normalisation -/

def fTop : PLLFormula := .ifThen .falsePLL .falsePLL

def isTop (f : PLLFormula) : Bool := f == fTop
def isBot (f : PLLFormula) : Bool := f == PLLFormula.falsePLL

def conjs : PLLFormula → List PLLFormula
  | .and a b => conjs a ++ conjs b
  | f => [f]

def disjs : PLLFormula → List PLLFormula
  | .or a b => disjs a ++ disjs b
  | f => [f]

def mkAnd : List PLLFormula → PLLFormula
  | [] => fTop
  | [x] => x
  | x :: xs => .and x (mkAnd xs)

def mkOr : List PLLFormula → PLLFormula
  | [] => PLLFormula.falsePLL
  | [x] => x
  | x :: xs => .or x (mkOr xs)

/-- Unit-and-duplicate normalisation.  All rewrites are intuitionistic
equivalences (see the header). -/
def norm : PLLFormula → PLLFormula
  | .prop a => .prop a
  | .falsePLL => .falsePLL
  | .and a b =>
      let l := ((conjs (norm a)) ++ (conjs (norm b))).filter (fun x => !isTop x)
      let l := l.eraseDups
      if l.any isBot then .falsePLL else mkAnd l
  | .or a b =>
      let l := ((disjs (norm a)) ++ (disjs (norm b))).filter (fun x => !isBot x)
      let l := l.eraseDups
      if l.any isTop then fTop else mkOr l
  | .ifThen a b =>
      let na := norm a
      let nb := norm b
      if isBot na then fTop
      else if isTop nb then fTop
      else if isTop na then nb
      else if na == nb then fTop
      else .ifThen na nb
  | .somehow a =>
      let na := norm a
      if isTop na then fTop else .somehow na

/-- Conjunction-level modus ponens: in a conjunct list, replace `X ⊃ Y` by
`Y` whenever `X` is itself a conjunct of the same list.  `X ∧ (X ⊃ Y) ⟛
X ∧ Y`, so this is an equivalence. -/
def mpStep : PLLFormula → PLLFormula
  | .prop a => .prop a
  | .falsePLL => .falsePLL
  | .or a b => .or (mpStep a) (mpStep b)
  | .somehow a => .somehow (mpStep a)
  | .ifThen a b => .ifThen (mpStep a) (mpStep b)
  | .and a b =>
      let l := (conjs (mpStep a) ++ conjs (mpStep b))
      let l' := l.map (fun x =>
        match x with
        | .ifThen p q => if l.contains p then q else x
        | _ => x)
      mkAnd l'

/-- `norm`, then alternate `mpStep`/`norm` to a fixpoint (fuel-capped). -/
def simp : Nat → PLLFormula → PLLFormula
  | 0, f => f
  | n+1, f =>
      let g := norm (mpStep (norm f))
      if g == f then f else simp n g

def simpF (f : PLLFormula) : PLLFormula := simp 12 (norm f)

/-! ## PLL-aware simplification (untrusted; the result is engine-verified)

The extra laws used, all `⟛` in PLL:

* `◯A ∧ ◯B ⟛ ◯(A ∧ B)`      (unit + strength)
* `◯⊥ ⊢ ◯C`   for every `C`   (functoriality on `⊥ ⊢ C`)
* `A ⊢ ◯A`                    (unit)
* `X ∨ (X ∧ Y) ⟛ X`,  `X ∧ (X ∨ Y) ⟛ X`   (absorption)
* `X ∧ (A ⊃ (Y ∧ X)) ⟛ X ∧ (A ⊃ Y)`        (context pruning)

Nothing here is trusted: the simplified formula is checked against the raw
`interpF` value in both directions by `prove?Bounded`. -/

def isCirc : PLLFormula → Bool
  | .somehow _ => true
  | _ => false

def circBody : PLLFormula → Option PLLFormula
  | .somehow a => some a
  | _ => none

/-- Drop from the conjunct-list of `b` anything already present in `outer`. -/
def prune (outer : List PLLFormula) (b : PLLFormula) : PLLFormula :=
  mkAnd ((conjs b).filter (fun x => !outer.contains x))

def andPass (l0 : List PLLFormula) : PLLFormula :=
  let l := (l0.filter (fun x => !isTop x)).eraseDups
  if l.any isBot then .falsePLL else
  -- context pruning + conjunction-level modus ponens
  let l := l.map (fun x =>
    match x with
    | .ifThen a b => if l.contains a then b else .ifThen a (prune l b)
    | _ => x)
  let l := (l.filter (fun x => !isTop x)).eraseDups
  -- absorption: drop a disjunction one of whose disjuncts is already present
  let l := l.filter (fun x =>
    match x with
    | .or _ _ => !((disjs x).any (fun d => l.contains d))
    | _ => true)
  -- ◯-merge
  let cs := l.filterMap circBody
  if cs.length ≥ 2 then
    let rest := l.filter (fun x => !isCirc x)
    mkAnd (rest ++ [PLLFormula.somehow (mkAnd (cs.flatMap conjs).eraseDups)])
  else mkAnd l

def orPass (l0 : List PLLFormula) : PLLFormula :=
  let l := (l0.filter (fun x => !isBot x)).eraseDups
  if l.any isTop then fTop else
  -- absorption: drop a conjunction one of whose conjuncts is already present
  let l := l.filter (fun x =>
    match x with
    | .and _ _ => !((conjs x).any (fun c => l.contains c))
    | _ => true)
  -- unit: X ∨ ◯X ⟛ ◯X
  let l := l.filter (fun x => !l.contains (PLLFormula.somehow x))
  -- ◯⊥ is below every ◯-headed disjunct
  let l :=
    if l.any (fun x => isCirc x && x != PLLFormula.somehow .falsePLL)
    then l.filter (fun x => x != PLLFormula.somehow .falsePLL) else l
  mkOr l

/-- One PLL-aware rewriting sweep, bottom-up. -/
def pllStep : PLLFormula → PLLFormula
  | .prop a => .prop a
  | .falsePLL => .falsePLL
  | .and a b => andPass (conjs (pllStep a) ++ conjs (pllStep b))
  | .or a b => orPass (disjs (pllStep a) ++ disjs (pllStep b))
  | .ifThen a b =>
      let na := pllStep a
      let nb := pllStep b
      if isBot na then fTop
      else if isTop nb then fTop
      else if isTop na then nb
      else if na == nb then fTop
      else .ifThen na nb
  | .somehow a =>
      let na := pllStep a
      if isTop na then fTop else .somehow na

def pllFix : Nat → PLLFormula → PLLFormula
  | 0, f => f
  | n+1, f =>
      let g := norm (pllStep (norm f))
      if g == f then f else pllFix n g

/-- The PLL-aware normal form. -/
def pnf (f : PLLFormula) : PLLFormula := pllFix 24 (simpF f)

/-! ## Sizes and layout -/

def sz : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and a b => sz a + sz b + 1
  | .or a b => sz a + sz b + 1
  | .ifThen a b => sz a + sz b + 1
  | .somehow a => sz a + 1

def indentS (n : Nat) : String := String.mk (List.replicate n ' ')

/-- Indented layout: anything of size ≤ `thr` prints on one line; larger
nodes break, with `∧`/`∨`/`⊃`/`◯` markers at the head of each part. -/
partial def lay (thr : Nat) (f : PLLFormula) (ind : Nat) : List String :=
  if sz f ≤ thr then [indentS ind ++ PLLFormula.toString f]
  else match f with
  | .and _ _ =>
      let l := conjs f
      (indentS ind ++ "AND") ::
        l.flatMap (fun x => lay thr x (ind + 2))
  | .or _ _ =>
      let l := disjs f
      (indentS ind ++ "OR") ::
        l.flatMap (fun x => lay thr x (ind + 2))
  | .ifThen a b =>
      (indentS ind ++ "IMP") :: (lay thr a (ind + 2) ++
        (indentS (ind + 2) ++ "⊃") :: lay thr b (ind + 2))
  | .somehow a => (indentS ind ++ "◯") :: lay thr a (ind + 2)
  | _ => [indentS ind ++ PLLFormula.toString f]

def show1 (name : String) (f : PLLFormula) : IO Unit := do
  let g := simpF f
  IO.println s!"---- {name}: raw {sz f} nodes, simplified {sz g} nodes"
  IO.println (PLLFormula.toString g)
  IO.println ""
  IO.println s!"---- {name}, laid out:"
  for l in lay 30 g 0 do IO.println l
  IO.println ""
  (← IO.getStdout).flush


/-! ## The conjectured closed family θ_k

Read off the PLL-normal forms of the chain (wip/ljfo_theta_print.lean).
Writing `⊥` for falsity and `◯` for the lax modality, put

    π  :=  (q ∧ r) ⊃ ◯⊥
    ρ  :=  ◯((q ∧ r) ⊃ ◯⊥)          ( = ◯π )
    σ  :=  q ∧ (◯⊥ ⊃ r)

Then the conjecture is

    θ_1      =  ◯⊥
    θ_2      =  ◯(◯⊥ ∨ (q ⊃ ◯⊥))
    θ_{k+1}  =  ◯( (θ_k ∧ ρ) ∨ (σ ⊃ ◯⊥) )        (k ≥ 2)

and `θ_k ⟛ A_{2k}`.  The boxed-body form `θ'_k = ◯ψ_k`,

    ψ_1      =  ⊥
    ψ_2      =  q ⊃ ◯⊥
    ψ_{k+1}  =  ◯(ψ_k ∧ π) ∨ (σ ⊃ ◯⊥)

is the same family after `◯A ∧ ◯B ⟛ ◯(A ∧ B)` and `◯⊥ ⊢ q ⊃ ◯⊥`. -/

def fq : PLLFormula := .prop "q"
def fr : PLLFormula := .prop "r"
def cbot : PLLFormula := .somehow .falsePLL
def piF : PLLFormula := .ifThen (.and fq fr) cbot
def rhoF : PLLFormula := .somehow piF
def sigF : PLLFormula := .and fq (.ifThen cbot fr)

/-- The θ-family, disjunctive form. -/
def theta : Nat → PLLFormula
  | 0 => .falsePLL
  | 1 => cbot
  | 2 => .somehow (.or cbot (.ifThen fq cbot))
  | k+1 => .somehow (.or (.and (theta k) rhoF) (.ifThen sigF cbot))

/-- The bodies of the boxed form. -/
def psi : Nat → PLLFormula
  | 0 => .falsePLL
  | 1 => .falsePLL
  | 2 => .ifThen fq cbot
  | k+1 => .or (.somehow (.and (psi k) piF)) (.ifThen sigF cbot)

/-- The θ-family, boxed-body form. -/
def theta' (k : Nat) : PLLFormula := .somehow (psi k)

end Theta
