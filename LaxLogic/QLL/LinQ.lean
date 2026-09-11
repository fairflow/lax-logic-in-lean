/-
# `LaxLogic.QLL.LinQ` — linear arithmetic over ℚ, with certificates

Step C1 of `docs/qll-clp-review.md` §4.  A constraint domain for CLP(Q), in the
certifying-algorithm style: the solver (Fourier–Motzkin, `fm`) is untrusted
and its answers are checked by two small functions proved sound.

* `checkWitness cs σ = true → ∀ c ∈ cs, c.holds σ`
* `checkFarkas (ls.zip cs) = true → ¬ ∃ σ, ∀ c ∈ cs, c.holds σ`: a nonnegative
  combination of the constraints (any sign on equations) whose variable part
  vanishes and whose constant contradicts it (the easy half of Farkas' lemma).

Constraint atoms are ordinary atoms `leq(a, b)`, `lt`, `geq`, `gt`, `eq` over
terms built from numerals (nullary function symbols named by a rational, e.g.
`35` or `7/2`), `add`, `sub`, `neg` and `mul` by a constant; names (`fvar`) are
the variables.  `consOf` reads a conjunction of such atoms as a list of linear
constraints.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LaxLogic.QLL.Syntax

namespace LaxLogic.QLL.LinQ

open LaxLogic.QLL

/-- `≤ 0`, `< 0`, `= 0`. -/
inductive Kind | le | lt | eq
  deriving DecidableEq, Repr, Inhabited

/-- `Σ aₓ·x + k`, the terms not necessarily normalised. -/
structure Lin where
  terms : List (String × ℚ)
  const : ℚ
  deriving Repr, Inhabited

/-- `Σ aₓ·σ(x)`. -/
def sumTerms (σ : String → ℚ) : List (String × ℚ) → ℚ
  | [] => 0
  | (x, a) :: l => a * σ x + sumTerms σ l

def Lin.eval (σ : String → ℚ) (e : Lin) : ℚ := sumTerms σ e.terms + e.const

def Lin.add (e f : Lin) : Lin := ⟨e.terms ++ f.terms, e.const + f.const⟩
def Lin.smul (a : ℚ) (e : Lin) : Lin := ⟨e.terms.map (fun p => (p.1, a * p.2)), a * e.const⟩
def Lin.var (x : String) : Lin := ⟨[(x, 1)], 0⟩
def Lin.cst (q : ℚ) : Lin := ⟨[], q⟩
def Lin.sub (e f : Lin) : Lin := e.add (f.smul (-1))

theorem sumTerms_append (σ : String → ℚ) :
    ∀ l m : List (String × ℚ), sumTerms σ (l ++ m) = sumTerms σ l + sumTerms σ m
  | [], m => by simp [sumTerms]
  | (x, a) :: l, m => by simp only [List.cons_append, sumTerms, sumTerms_append σ l m]; ring

theorem sumTerms_smul (σ : String → ℚ) (c : ℚ) :
    ∀ l : List (String × ℚ), sumTerms σ (l.map (fun p => (p.1, c * p.2))) = c * sumTerms σ l
  | [] => by simp [sumTerms]
  | (x, a) :: l => by simp only [List.map_cons, sumTerms, sumTerms_smul σ c l]; ring

theorem Lin.eval_add (σ : String → ℚ) (e f : Lin) : (e.add f).eval σ = e.eval σ + f.eval σ := by
  simp only [Lin.eval, Lin.add, sumTerms_append]; ring

theorem Lin.eval_smul (σ : String → ℚ) (a : ℚ) (e : Lin) : (e.smul a).eval σ = a * e.eval σ := by
  simp only [Lin.eval, Lin.smul, sumTerms_smul]; ring

/-- A linear constraint `e ⋈ 0`. -/
structure LinCon where
  e : Lin
  k : Kind
  deriving Repr, Inhabited

def LinCon.holds (σ : String → ℚ) (c : LinCon) : Prop :=
  match c.k with
  | .le => c.e.eval σ ≤ 0
  | .lt => c.e.eval σ < 0
  | .eq => c.e.eval σ = 0

def LinCon.holdsB (σ : String → ℚ) (c : LinCon) : Bool :=
  match c.k with
  | .le => decide (c.e.eval σ ≤ 0)
  | .lt => decide (c.e.eval σ < 0)
  | .eq => decide (c.e.eval σ = 0)

theorem LinCon.holdsB_iff (σ : String → ℚ) (c : LinCon) : c.holdsB σ = true ↔ c.holds σ := by
  unfold holdsB holds; cases c.k <;> simp

/-! ## Certificates -/

/-- An assignment given as a finite table, `0` elsewhere. -/
def asg (w : List (String × ℚ)) : String → ℚ := fun x => (w.lookup x).getD 0

def checkWitness (cs : List LinCon) (σ : String → ℚ) : Bool := cs.all (·.holdsB σ)

theorem checkWitness_sound {cs : List LinCon} {σ : String → ℚ} (h : checkWitness cs σ = true) :
    ∀ c ∈ cs, c.holds σ :=
  fun c hc => (LinCon.holdsB_iff σ c).1 (List.all_eq_true.1 h c hc)

/-- Add `a·x` into a coefficient table. -/
def addCoeff (x : String) (a : ℚ) : List (String × ℚ) → List (String × ℚ)
  | [] => [(x, a)]
  | (y, b) :: l => if x = y then (y, a + b) :: l else (y, b) :: addCoeff x a l

theorem sumTerms_addCoeff (σ : String → ℚ) (x : String) (a : ℚ) :
    ∀ l, sumTerms σ (addCoeff x a l) = a * σ x + sumTerms σ l
  | [] => by simp [addCoeff, sumTerms]
  | (y, b) :: l => by
      unfold addCoeff
      split
      · rename_i h; subst h; simp only [sumTerms]; ring
      · simp only [sumTerms, sumTerms_addCoeff σ x a l]; ring

/-- One coefficient per variable. -/
def norm (l : List (String × ℚ)) : List (String × ℚ) :=
  l.foldr (fun p acc => addCoeff p.1 p.2 acc) []

theorem sumTerms_norm (σ : String → ℚ) : ∀ l, sumTerms σ (norm l) = sumTerms σ l
  | [] => rfl
  | (x, a) :: l => by
      show sumTerms σ (addCoeff x a (norm l)) = _
      rw [sumTerms_addCoeff, sumTerms_norm σ l]; rfl

theorem sumTerms_zero (σ : String → ℚ) :
    ∀ l : List (String × ℚ), l.all (fun p => p.2 == 0) = true → sumTerms σ l = 0
  | [], _ => rfl
  | (x, a) :: l, h => by
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      simp only [sumTerms, h.1, zero_mul, zero_add, sumTerms_zero σ l h.2]

/-- `Σ λᵢ·eᵢ`. -/
def comb : List (ℚ × LinCon) → Lin
  | [] => ⟨[], 0⟩
  | (a, c) :: l => (c.e.smul a).add (comb l)

/-- Inequalities take nonnegative multipliers; equations any. -/
def okMult (p : ℚ × LinCon) : Bool :=
  match p.2.k with
  | .eq => true
  | _ => decide (0 ≤ p.1)

/-- A strict inequality used with a positive multiplier. -/
def strictUse (p : ℚ × LinCon) : Bool := p.2.k == .lt && decide (0 < p.1)

theorem comb_nonpos (σ : String → ℚ) : ∀ l : List (ℚ × LinCon),
    (∀ p ∈ l, p.2.holds σ) → l.all okMult = true →
      (comb l).eval σ ≤ 0 ∧ (l.any strictUse = true → (comb l).eval σ < 0)
  | [], _, _ => by simp [comb, Lin.eval, sumTerms]
  | (a, c) :: l, hσ, hok => by
      simp only [List.all_cons, Bool.and_eq_true] at hok
      obtain ⟨hc, hl⟩ := hok
      have hh := hσ (a, c) (List.mem_cons.2 (Or.inl rfl))
      obtain ⟨ih₁, ih₂⟩ := comb_nonpos σ l (fun p hp => hσ p (List.mem_cons.2 (Or.inr hp))) hl
      have hev : (comb ((a, c) :: l)).eval σ = a * c.e.eval σ + (comb l).eval σ := by
        simp only [comb, Lin.eval_add, Lin.eval_smul]
      rw [hev]
      unfold okMult at hc
      unfold LinCon.holds at hh
      cases hk : c.k with
      | le =>
          rw [hk] at hc hh
          simp only [decide_eq_true_eq] at hc
          have : a * c.e.eval σ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hh
          refine ⟨by linarith, fun hs => ?_⟩
          simp only [List.any_cons, Bool.or_eq_true, strictUse, hk, Bool.and_eq_true,
            beq_iff_eq, reduceCtorEq, false_and, false_or] at hs
          linarith [ih₂ hs]
      | lt =>
          rw [hk] at hc hh
          simp only [decide_eq_true_eq] at hc
          have : a * c.e.eval σ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hh.le
          refine ⟨by linarith, fun hs => ?_⟩
          simp only [List.any_cons, Bool.or_eq_true, strictUse, hk, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq, true_and] at hs
          rcases hs with hs | hs
          · have : a * c.e.eval σ < 0 := mul_neg_of_pos_of_neg hs hh
            linarith
          · linarith [ih₂ hs]
      | eq =>
          rw [hk] at hh
          rw [hh, mul_zero, zero_add]
          refine ⟨ih₁, fun hs => ?_⟩
          simp only [List.any_cons, Bool.or_eq_true, strictUse, hk, Bool.and_eq_true,
            beq_iff_eq, reduceCtorEq, false_and, false_or] at hs
          exact ih₂ hs

/-- The Farkas check. -/
def checkFarkas (l : List (ℚ × LinCon)) : Bool :=
  l.all okMult && (norm (comb l).terms).all (fun p => p.2 == 0) &&
    (decide (0 < (comb l).const) || (decide (0 ≤ (comb l).const) && l.any strictUse))

theorem checkFarkas_sound {l : List (ℚ × LinCon)} (h : checkFarkas l = true) :
    ¬ ∃ σ, ∀ p ∈ l, p.2.holds σ := by
  rintro ⟨σ, hσ⟩
  simp only [checkFarkas, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hok, hz⟩, hk⟩ := h
  have hev : (comb l).eval σ = (comb l).const := by
    unfold Lin.eval; rw [← sumTerms_norm σ, sumTerms_zero σ _ hz, zero_add]
  obtain ⟨h1, h2⟩ := comb_nonpos σ l hσ hok
  rcases hk with hk | ⟨hk, hs⟩
  · linarith
  · have := h2 hs; linarith

/-- A Farkas certificate for a list of constraints: one multiplier each. -/
theorem checkFarkas_unsat {cs : List LinCon} {ls : List ℚ} (h : checkFarkas (ls.zip cs) = true) :
    ¬ ∃ σ, ∀ c ∈ cs, c.holds σ := by
  rintro ⟨σ, hσ⟩
  exact checkFarkas_sound h ⟨σ, fun p hp => hσ p.2 (List.of_mem_zip hp).2⟩

/-! ## Reading constraint atoms -/

def parseRat? (s : String) : Option ℚ :=
  match s.splitOn "/" with
  | [a] => a.toInt?.map (fun n : Int => (n : ℚ))
  | [a, b] =>
      match a.toInt?, b.toNat? with
      | some n, some d => if d = 0 then none else some ((n : ℚ) / d)
      | _, _ => none
  | _ => none

/-- A term as a linear expression, if it is one. -/
def linOf : Tm → Option Lin
  | .bvar _ => none
  | .fvar x => some (Lin.var x)
  | .fn "add" [a, b] => do let x ← linOf a; let y ← linOf b; pure (x.add y)
  | .fn "sub" [a, b] => do let x ← linOf a; let y ← linOf b; pure (x.sub y)
  | .fn "neg" [a] => (linOf a).map (Lin.smul (-1))
  | .fn "mul" [a, b] => do
      let x ← linOf a; let y ← linOf b
      if x.terms.isEmpty then pure (y.smul x.const)
      else if y.terms.isEmpty then pure (x.smul y.const) else none
  | .fn f [] => (parseRat? f).map Lin.cst
  | .fn _ _ => none

/-- The constraint predicates. -/
def isLinC (B : String) : Bool :=
  B == "leq" || B == "lt" || B == "geq" || B == "gt" || B == "eq"

def atomCon (B : String) (ts : List Tm) : Option LinCon :=
  match B, ts with
  | "leq", [a, b] => do let x ← linOf a; let y ← linOf b; pure ⟨x.sub y, .le⟩
  | "lt",  [a, b] => do let x ← linOf a; let y ← linOf b; pure ⟨x.sub y, .lt⟩
  | "geq", [a, b] => do let x ← linOf a; let y ← linOf b; pure ⟨y.sub x, .le⟩
  | "gt",  [a, b] => do let x ← linOf a; let y ← linOf b; pure ⟨y.sub x, .lt⟩
  | "eq",  [a, b] => do let x ← linOf a; let y ← linOf b; pure ⟨x.sub y, .eq⟩
  | _, _ => none

/-- A conjunction of constraint atoms, as linear constraints. -/
def consOf : Form → Option (List LinCon)
  | .top => some []
  | .pred B ts => (atomCon B ts).map ([·])
  | .and A B => do let x ← consOf A; let y ← consOf B; pure (x ++ y)
  | _ => none

/-- `σ` satisfies the constraint formula `A`. -/
def CSat (σ : String → ℚ) (A : Form) : Prop := ∃ cs, consOf A = some cs ∧ ∀ c ∈ cs, c.holds σ

/-! ## Fourier–Motzkin, untrusted -/

structure Row where
  terms : List (String × ℚ)
  const : ℚ
  strict : Bool
  mult : List ℚ
  deriving Inhabited

def coeffOf (x : String) (l : List (String × ℚ)) : ℚ := (l.lookup x).getD 0

def rowComb (a : ℚ) (r : Row) (b : ℚ) (s : Row) : Row :=
  { terms := (norm (r.terms.map (fun p => (p.1, a * p.2)) ++
        s.terms.map (fun p => (p.1, b * p.2)))).filter (fun p => p.2 != 0)
    const := a * r.const + b * s.const
    strict := r.strict || s.strict
    mult := List.zipWith (· + ·) (r.mult.map (a * ·)) (s.mult.map (b * ·)) }

def unitVec (n i : Nat) (a : ℚ) : List ℚ := (List.range n).map (fun j => if j = i then a else 0)

def initRows (cs : List LinCon) : List Row :=
  let n := cs.length
  (cs.zipIdx).flatMap fun (c, i) =>
    let t := (norm c.e.terms).filter (fun p => p.2 != 0)
    match c.k with
    | .le => [⟨t, c.e.const, false, unitVec n i 1⟩]
    | .lt => [⟨t, c.e.const, true, unitVec n i 1⟩]
    | .eq => [⟨t, c.e.const, false, unitVec n i 1⟩,
              ⟨t.map (fun p => (p.1, -p.2)), -c.e.const, false, unitVec n i (-1)⟩]

def elimVar (x : String) (rows : List Row) : List Row × List Row :=
  let pos := rows.filter (fun r => decide (0 < coeffOf x r.terms))
  let neg := rows.filter (fun r => decide (coeffOf x r.terms < 0))
  let zero := rows.filter (fun r => coeffOf x r.terms == 0)
  let new := pos.flatMap fun P => neg.map fun N =>
    rowComb (-(coeffOf x N.terms)) P (coeffOf x P.terms) N
  (zero ++ new, pos ++ neg)

def rowsVars (rows : List Row) : List String :=
  rows.foldl (fun acc r => r.terms.foldl (fun acc p => if acc.contains p.1 then acc else p.1 :: acc) acc) []

/-- The value of a row with `x := 0`, other variables from `σ`. -/
def restVal (σ : String → ℚ) (x : String) (r : Row) : ℚ :=
  (r.terms.filter (fun p => p.1 != x)).foldl (fun acc p => acc + p.2 * σ p.1) r.const

def chooseVal (σ : String → ℚ) (x : String) (rows : List Row) : ℚ :=
  let bounds := rows.map fun r =>
    let a := coeffOf x r.terms
    let v := -(restVal σ x r) / a
    (decide (0 < a), v, r.strict)
  let lows := bounds.filter (fun b => !b.1)
  let ups := bounds.filter (fun b => b.1)
  let lo : Option (ℚ × Bool) := lows.foldl (fun acc b =>
    match acc with
    | none => some (b.2.1, b.2.2)
    | some (v, s) => if b.2.1 > v then some (b.2.1, b.2.2) else if b.2.1 = v then some (v, s || b.2.2) else acc) none
  let hi : Option (ℚ × Bool) := ups.foldl (fun acc b =>
    match acc with
    | none => some (b.2.1, b.2.2)
    | some (v, s) => if b.2.1 < v then some (b.2.1, b.2.2) else if b.2.1 = v then some (v, s || b.2.2) else acc) none
  match lo, hi with
  | none, none => 0
  | some (l, s), none => if s then l + 1 else l
  | none, some (u, s) => if s then u - 1 else u
  | some (l, _), some (u, _) => if l < u then (l + u) / 2 else l

inductive Verdict
  | sat (w : List (String × ℚ))
  | unsat (mult : List ℚ)
  | unknown
  deriving Repr, Inhabited

/-- Fourier–Motzkin elimination.  Untrusted; `solve` checks what it returns. -/
def fm (cs : List LinCon) (cap : Nat := 50000) : Verdict := Id.run do
  let mut rows := initRows cs
  let mut stages : List (String × List Row) := []
  let mut vars := rowsVars rows
  while !vars.isEmpty do
    -- the variable with the fewest new rows
    let best := vars.foldl (fun (acc : Option (String × Nat)) x =>
      let p := (rows.filter (fun r => decide (0 < coeffOf x r.terms))).length
      let n := (rows.filter (fun r => decide (coeffOf x r.terms < 0))).length
      match acc with
      | none => some (x, p * n)
      | some (_, k) => if p * n < k then some (x, p * n) else acc) none
    match best with
    | none => vars := []
    | some (x, _) =>
        let (rest, used) := elimVar x rows
        if rest.length > cap then return .unknown
        stages := (x, used) :: stages
        rows := rest
        vars := vars.filter (· != x)
  for r in rows do
    if (!r.strict && decide (0 < r.const)) || (r.strict && decide (0 ≤ r.const)) then
      return .unsat r.mult
  let mut w : List (String × ℚ) := []
  for (x, used) in stages do
    let v := chooseVal (asg w) x used
    w := (x, v) :: w
  return .sat w

/-- A certified verdict: `fm`, checked. -/
def solve (cs : List LinCon) : Verdict :=
  match fm cs with
  | .sat w => if checkWitness cs (asg w) then .sat w else .unknown
  | .unsat m => if checkFarkas (m.zip cs) then .unsat m else .unknown
  | .unknown => .unknown

theorem solve_sat {cs : List LinCon} {w : List (String × ℚ)} (h : solve cs = .sat w) :
    ∀ c ∈ cs, c.holds (asg w) := by
  unfold solve at h
  split at h
  · split at h
    · rename_i hw; cases h; exact checkWitness_sound hw
    · cases h
  · split at h <;> cases h
  · cases h

theorem solve_unsat {cs : List LinCon} {m : List ℚ} (h : solve cs = .unsat m) :
    ¬ ∃ σ, ∀ c ∈ cs, c.holds σ := by
  unfold solve at h
  split at h
  · split at h <;> cases h
  · split at h
    · rename_i hf; cases h; exact checkFarkas_unsat hf
    · cases h
  · cases h


/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.LinQ.checkWitness_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkWitness_sound

/-- info: 'LaxLogic.QLL.LinQ.checkFarkas_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkFarkas_sound

/-- info: 'LaxLogic.QLL.LinQ.checkFarkas_unsat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkFarkas_unsat

/-- info: 'LaxLogic.QLL.LinQ.solve_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms solve_sat

/-- info: 'LaxLogic.QLL.LinQ.solve_unsat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms solve_unsat

end LaxLogic.QLL.LinQ
