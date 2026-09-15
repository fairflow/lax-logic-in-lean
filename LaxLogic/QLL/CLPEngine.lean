/-
# `LaxLogic.QLL.CLPEngine` — an SLD engine whose answers are certified

Step E of `docs/qll-clp-review.md` §4.  Resolution per Table 2, leftmost
selection, depth-first with backtracking, in continuation-passing style
(`solveK`) so alternatives are explored lazily.  Clause heads are `P(x₁,…,xₘ)`
(Definition 5.1), so resolution is matching, never unification: all term
structure is carried by constraints.  The engine builds the proof tree as it
goes, the forest of Theorem 9.4 read off its own control stack.

With `eager` set, every new constraint is tested for satisfiability with the
certified linear solver (`LinQ.solve`), which prunes failing branches: CLP's
incremental solving, here the latent constraint of the partial proof.

**What is certified.**  For an answer `a`:

    answer_sound :  a.typed = true  →  Θ.forms ⊢ a.constraint ⊃ G
    answer_sat   :  a.verdict = .sat w  →  CSat (asg w) a.constraint

where `a.typed` is the run-time check `checkC` (proved sound) of the tree the
engine returns, and the verdict comes from `LinQ.solve`, whose answers are
checked certificates.  For timing systems `settle` also certifies the least
value of a variable, from both sides: a witness attaining it, and a Farkas
refutation of anything smaller (`lowerBoundCert_sound`).
-/
import LaxLogic.QLL.CLPOper
import LaxLogic.QLL.LinQ
import Std.Data.HashMap

namespace LaxLogic.QLL.Engine

open LaxLogic.QLL LaxLogic.QLL.LinQ

/-! ## Building programs -/

/-- Decide whether a formula is a Σ-formula. -/
def isSigmaB : Form → Bool
  | .top => true
  | .pred _ _ => true
  | .and A B | .or A B => isSigmaB A && isSigmaB B
  | .exists_ A => isSigmaB A
  | _ => false

/-- `isSigmaB` is sound. -/
theorem isSigmaB_sound : ∀ A, isSigmaB A = true → IsSigma A
  | .top, _ => .top
  | .pred P ts, _ => .pred P ts
  | .and A B, h => by
      simp only [isSigmaB, Bool.and_eq_true] at h
      exact .and (isSigmaB_sound A h.1) (isSigmaB_sound B h.2)
  | .or A B, h => by
      simp only [isSigmaB, Bool.and_eq_true] at h
      exact .or (isSigmaB_sound A h.1) (isSigmaB_sound B h.2)
  | .exists_ A, h => .ex (isSigmaB_sound A h)
  | .bot, h | .imp _ _, h | .circ _ _, h | .forall_ _, h => absurd h (by simp [isSigmaB])

/-- A non-modal clause `∀x₁…xₘ. body ⊃ head(x₁,…,xₘ)`. -/
def mkClause (arity : Nat) (head : String) (body : Form)
    (h : isSigmaB body = true := by rfl) : Clause :=
  ⟨arity, body, isSigmaB_sound body h, head, false, .ex⟩

/-- The same, with the Σ-check done when the clause is built (for generated
programs).  A body that is not a Σ-formula becomes an unprovable one. -/
def mkClauseD (arity : Nat) (head : String) (body : Form) : Clause :=
  if h : isSigmaB body = true then ⟨arity, body, isSigmaB_sound body h, head, false, .ex⟩
  else ⟨arity, .pred "⊥" [], .pred "⊥" [], head, false, .ex⟩

/-! ## The search -/

/-- The search state: the constraint store and a counter for fresh variables. -/
structure St where
  store : List Form
  fresh : Nat
  deriving Inhabited

/-- Not refuted by the certified solver (nonlinear stores are not refuted). -/
def satOK (store : List Form) : Bool :=
  match consOf (conjs store) with
  | some cs => match solve cs with
    | .unsat _ => false
    | _ => true
  | none => true

/-- The clauses of `Θ` that can resolve an atom `B(t̃)`: non-modal, head `B`, arity `|t̃|`.
Built once per run, so resolution does not scan the program. -/
def Program.index (Θ : Program) : Std.HashMap String (List (Clause × Nat)) :=
  Θ.zipIdx.foldr (fun cw m => if cw.1.modal then m else
    m.insert cw.1.head (cw :: m.getD cw.1.head [])) {}

/-- The first success among alternatives: backtracking. -/
def firstOf {α β : Type} : List α → (α → Option β) → Option β
  | [], _ => none
  | a :: l, f => match f a with
    | some b => some b
    | none => firstOf l f

/-- Depth-first resolution in continuation-passing style; `n` bounds the depth. -/
def solveK {R : Type} (ix : String → List (Clause × Nat)) (isC : String → Bool) (eager : Bool) :
    Nat → Form → St → (CProof → St → Option R) → Option R
  | 0, _, _, _ => none
  | n + 1, g, st, k =>
    match g with
    | .top => k .top st
    | .pred B ts =>
        if isC B then
          let st' : St := { st with store := .pred B ts :: st.store }
          if !eager || satOK st'.store then k (.cstr B ts) st' else none
        else
          firstOf (ix B) fun cw =>
            if cw.1.arity == ts.length then
              solveK ix isC eager n (Form.instAll ts cw.1.body) st
                (fun p st' => k (.clause cw.2 ts p) st')
            else none
    | .and A B =>
        solveK ix isC eager n A st fun p st₁ =>
          solveK ix isC eager n B st₁ fun q st₂ => k (.andI p q) st₂
    | .or A B =>
        match solveK ix isC eager n A st (fun p s => k (.orL p) s) with
        | some r => some r
        | none => solveK ix isC eager n B st (fun p s => k (.orR p) s)
    | .exists_ A =>
        let u := Tm.fvar s!"_v{st.fresh}"
        solveK ix isC eager n (A.openAt 0 u) { st with fresh := st.fresh + 1 }
          fun p s => k (.exI u p) s
    | _ => none

/-- All proofs (strict), for small programs with several answers. -/
def proveAll (Θ : Program) (isC : String → Bool) (eager : Bool) :
    Nat → Form → St → List (CProof × St)
  | 0, _, _ => []
  | n + 1, g, st =>
    match g with
    | .top => [(.top, st)]
    | .pred B ts =>
        if isC B then
          let st' : St := { st with store := .pred B ts :: st.store }
          if !eager || satOK st'.store then [(.cstr B ts, st')] else []
        else
          Θ.zipIdx.flatMap fun cw =>
            if !cw.1.modal && cw.1.head == B && cw.1.arity == ts.length then
              (proveAll Θ isC eager n (Form.instAll ts cw.1.body) st).map
                fun r => (.clause cw.2 ts r.1, r.2)
            else []
    | .and A B =>
        (proveAll Θ isC eager n A st).flatMap fun r₁ =>
          (proveAll Θ isC eager n B r₁.2).map fun r₂ => (.andI r₁.1 r₂.1, r₂.2)
    | .or A B =>
        (proveAll Θ isC eager n A st).map (fun r => (.orL r.1, r.2)) ++
        (proveAll Θ isC eager n B st).map (fun r => (.orR r.1, r.2))
    | .exists_ A =>
        let u := Tm.fvar s!"_v{st.fresh}"
        (proveAll Θ isC eager n (A.openAt 0 u) { st with fresh := st.fresh + 1 }).map
          fun r => (.exI u r.1, r.2)
    | _ => []

/-- Run the search from the empty store with a given clause index. -/
def runWith (ix : String → List (Clause × Nat)) (isC : String → Bool) (eager : Bool)
    (fuel : Nat) (G : Form) : Option (CProof × St) :=
  solveK ix isC eager fuel G ⟨[], 0⟩ fun p st => some (p, st)

/-- The run-time engine: clauses indexed by head in a hash map. -/
def run (Θ : Program) (isC : String → Bool) (eager : Bool) (fuel : Nat) (G : Form) :
    Option (CProof × St) :=
  let ix := Program.index Θ
  runWith (fun B => ix.getD B []) isC eager fuel G

/-- The same search with a list index, which the kernel can evaluate (string
hashing is opaque to it). -/
def Program.indexL (Θ : Program) (B : String) : List (Clause × Nat) :=
  Θ.zipIdx.filter fun cw => !cw.1.modal && cw.1.head == B

/-- The engine with a list index, which the kernel can evaluate. -/
def runL (Θ : Program) (isC : String → Bool) (eager : Bool) (fuel : Nat) (G : Form) :
    Option (CProof × St) :=
  runWith (Program.indexL Θ) isC eager fuel G

/-! ## Certified answers -/

/-- An answer: its proof tree, its total constraint, and whether `checkC` accepted the tree. -/
structure Answer where
  proof : CProof
  constraint : Form
  typed : Bool

/-- The certified solver's verdict on the answer constraint. -/
def Answer.verdict (a : Answer) : Verdict :=
  match consOf a.constraint with
  | some cs => solve cs
  | none => .unknown

/-- Package a proof tree as an answer. -/
def mkAnswer (Θ : Program) (isC : String → Bool) (G : Form) (p : CProof) : Answer :=
  ⟨p, p.total, checkC isC Θ G p⟩

/-- Run the engine and package the first answer. -/
def answer (Θ : Program) (isC : String → Bool) (eager : Bool) (fuel : Nat) (G : Form) :
    Option Answer :=
  (run Θ isC eager fuel G).map fun r => mkAnswer Θ isC G r.1

/-- An accepted tree's total constraint entails the query. -/
theorem mkAnswer_sound {Θ : Program} {isC : String → Bool} {G : Form} {p : CProof}
    (ht : (mkAnswer Θ isC G p).typed = true) :
    Prv Θ.forms (.imp (mkAnswer Θ isC G p).constraint G) :=
  (checkC_sound isC Θ p G ht).prv_total

/-- **Answer soundness**: `Θ ⊢ a.constraint ⊃ G` for an answer whose tree was accepted. -/
theorem answer_sound {Θ : Program} {isC : String → Bool} {eager : Bool} {fuel : Nat} {G : Form}
    {a : Answer} (h : answer Θ isC eager fuel G = some a) (ht : a.typed = true) :
    Prv Θ.forms (.imp a.constraint G) := by
  unfold answer at h
  cases hr : run Θ isC eager fuel G with
  | none => rw [hr] at h; cases h
  | some r =>
      rw [hr] at h; cases h
      exact mkAnswer_sound ht

/-- A satisfiable verdict gives an assignment satisfying the answer constraint. -/
theorem Answer.verdict_sat {a : Answer} {w : List (String × ℚ)} (h : a.verdict = .sat w) :
    CSat (asg w) a.constraint := by
  unfold Answer.verdict at h
  split at h
  · rename_i cs hcs
    exact ⟨cs, hcs, solve_sat h⟩
  · cases h

/-- Constraints read off a formula that `CSat` makes true. -/
theorem CSat.holds {σ : String → ℚ} {A : Form} (h : CSat σ A) :
    ∀ c ∈ (consOf A).getD [], c.holds σ := by
  obtain ⟨cs, hcs, hσ⟩ := h
  rw [hcs]; exact hσ

/-! ## Entailment, certified by refutation -/

/-- `cs ⊨ e ≤ 0`: the solver refutes `cs ∧ −e < 0`, with a checked Farkas certificate. -/
def entailsLe (cs : List LinCon) (e : Lin) : Bool :=
  match solve (cs ++ [(⟨e.smul (-1), .lt⟩ : LinCon)]) with
  | .unsat _ => true
  | _ => false

/-- Checked entailment is sound: every solution of `cs` has `e ≤ 0`. -/
theorem entailsLe_sound {cs : List LinCon} {e : Lin} (h : entailsLe cs e = true) :
    ∀ σ, (∀ c ∈ cs, c.holds σ) → e.eval σ ≤ 0 := by
  intro σ hσ
  unfold entailsLe at h
  split at h
  · rename_i m hm
    rcases lt_or_ge 0 (e.eval σ) with hlt | hle
    · refine absurd ⟨σ, fun c hc => ?_⟩ (solve_unsat hm)
      rcases List.mem_append.1 hc with hc | hc
      · exact hσ c hc
      · simp only [List.mem_singleton] at hc
        subst hc
        show (e.smul (-1)).eval σ < 0
        rw [Lin.eval_smul]; linarith
    · exact hle
  · cases h

/-- `cs ⊨ e = 0`, both halves certified. -/
def entailsEq (cs : List LinCon) (e : Lin) : Bool :=
  entailsLe cs e && entailsLe cs (e.smul (-1))

/-- Checked entailment of an equation is sound. -/
theorem entailsEq_sound {cs : List LinCon} {e : Lin} (h : entailsEq cs e = true) :
    ∀ σ, (∀ c ∈ cs, c.holds σ) → e.eval σ = 0 := by
  intro σ hσ
  simp only [entailsEq, Bool.and_eq_true] at h
  have h1 := entailsLe_sound h.1 σ hσ
  have h2 := entailsLe_sound h.2 σ hσ
  rw [Lin.eval_smul] at h2
  linarith

/-! ## Timing: the least value of a variable, certified from both sides -/

/-- `y + d − x ≤ 0` (source `y`) or `d − x ≤ 0` (no source): `x ≥ y + d`. -/
def asDiff (c : LinCon) : Option (String × Option String × ℚ) :=
  if c.k != .le then none else
  match (norm c.e.terms).filter (fun p => p.2 != 0) with
  | [(x, a)] => if a == -1 then some (x, none, c.e.const) else none
  | [(x, a), (y, b)] =>
      if a == -1 && b == 1 then some (x, some y, c.e.const)
      else if a == 1 && b == -1 then some (y, some x, c.e.const) else none
  | _ => none

/-- Longest paths through the difference constraints (Bellman–Ford relaxation). -/
def earliest (cs : List LinCon) (rounds : Nat := 100000) :
    Std.HashMap String ℚ × Std.HashMap String Nat := Id.run do
  let ds := cs.zipIdx.filterMap fun ci => (asDiff ci.1).map fun d => (d, ci.2)
  let mut v : Std.HashMap String ℚ := {}
  let mut pred : Std.HashMap String Nat := {}
  let mut changed := true
  let mut r := 0
  while changed && r < rounds do
    changed := false
    r := r + 1
    for e in ds do
      let ((x, y?, d), i) := e
      let base : ℚ := match y? with
        | none => 0
        | some y => v.getD y 0
      let cand := base + d
      match v.get? x with
      | some old =>
          if cand > old then
            v := v.insert x cand; pred := pred.insert x i; changed := true
      | none => v := v.insert x cand; pred := pred.insert x i; changed := true
  return (v, pred)

/-- The chain of constraints that attains the value of `z`. -/
def critical (cs : List LinCon) (pred : Std.HashMap String Nat) : String → Nat → List Nat
  | _, 0 => []
  | x, n + 1 =>
      match pred.get? x with
      | none => []
      | some i =>
          match cs[i]?.bind asDiff with
          | some (_, some y, _) => i :: critical cs pred y n
          | _ => [i]

/-- `z ≥ z*` follows from `cs`: `ms` refutes `cs ∧ z < z*`. -/
def lowerBoundCert (cs : List LinCon) (z : String) (zstar : ℚ) (ms : List ℚ) : Bool :=
  checkFarkas ((ms ++ [1]).zip (cs ++ [(⟨⟨[(z, 1)], -zstar⟩, .lt⟩ : LinCon)]))

/-- A checked lower-bound certificate: every solution has `z* ≤ z`. -/
theorem lowerBoundCert_sound {cs : List LinCon} {z : String} {zstar : ℚ} {ms : List ℚ}
    (h : lowerBoundCert cs z zstar ms = true) (hlen : ms.length = cs.length) :
    ∀ σ, (∀ c ∈ cs, c.holds σ) → zstar ≤ σ z := by
  intro σ hσ
  rcases lt_or_ge (σ z) zstar with hlt | hge
  · exfalso
    refine checkFarkas_sound h ⟨σ, fun p hp => ?_⟩
    rw [List.zip_append (by simp [hlen])] at hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hσ p.2 (List.of_mem_zip hp).2
    · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
      subst hp
      show sumTerms σ [(z, 1)] + -zstar < 0
      simp only [sumTerms]
      linarith
  · exact hge

/-- The coefficient of `z` in a list of terms. -/
def zc (z : String) : List (String × ℚ) → ℚ
  | [] => 0
  | (x, a) :: l => (if x = z then a else 0) + zc z l

/-- `σ` with `z` raised to `r`. -/
def raise (σ : String → ℚ) (z : String) (r : ℚ) : String → ℚ := fun y => if y = z then r else σ y

/-- Raising `z` to `r` changes a linear form by its `z`-coefficient times `r − σ(z)`. -/
theorem sumTerms_raise (σ : String → ℚ) (z : String) (r : ℚ) :
    ∀ l, sumTerms (raise σ z r) l = sumTerms σ l + zc z l * (r - σ z)
  | [] => by simp [sumTerms, zc]
  | (x, a) :: l => by
      simp only [sumTerms, zc, sumTerms_raise σ z r l, raise]
      by_cases h : x = z
      · subst h; simp only [if_true]; ring
      · simp only [h, if_false]; ring

/-- Every constraint is an inequality in which `z` has a non-positive coefficient,
so raising `z` preserves it: a settled signal stays settled. -/
def upClosed (cs : List LinCon) (z : String) : Bool :=
  cs.all fun c => c.k != .eq && decide (zc z c.e.terms ≤ 0)

/-- Raising a variable with non-positive coefficients in every inequality preserves solutions. -/
theorem upClosed_sound {cs : List LinCon} {z : String} (h : upClosed cs z = true)
    {σ : String → ℚ} {r : ℚ} (hr : σ z ≤ r) (hσ : ∀ c ∈ cs, c.holds σ) :
    ∀ c ∈ cs, c.holds (raise σ z r) := by
  intro c hc
  have hc' := List.all_eq_true.1 h c hc
  have hcs := hσ c hc
  obtain ⟨e, k⟩ := c
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc'
  have key : e.eval (raise σ z r) = e.eval σ + zc z e.terms * (r - σ z) := by
    simp only [Lin.eval, sumTerms_raise]; ring
  have hneg : zc z e.terms * (r - σ z) ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hr) (neg_nonneg.2 hc'.2)]
  cases k with
  | le => simp only [LinCon.holds] at hcs ⊢; rw [key]; linarith
  | lt => simp only [LinCon.holds] at hcs ⊢; rw [key]; linarith
  | eq => exact absurd rfl hc'.1

/-- Satisfaction of a formula read as constraints, from satisfaction of its constraint list. -/
theorem CSat.of_holds {σ : String → ℚ} {A : Form} (hs : (consOf A).isSome = true)
    (h : ∀ c ∈ (consOf A).getD [], c.holds σ) : CSat σ A := by
  cases hc : consOf A with
  | none => rw [hc] at hs; cases hs
  | some cs => exact ⟨cs, hc, by rw [hc] at h; exact h⟩

/-- The least value of a variable, with a witness attaining it and multipliers refuting less. -/
structure Settle where
  zstar : ℚ
  witness : List (String × ℚ)
  mult : List ℚ
  witnessOK : Bool
  lowerOK : Bool

/-- Longest paths through the difference constraints, with both certificates. -/
def settle (cs : List LinCon) (z : String) : Settle :=
  let (v, pred) := earliest cs
  let zstar := v.getD z 0
  let w := v.toList
  let path := critical cs pred z (cs.length + 1)
  let ms := (List.range cs.length).map fun i => if path.contains i then (1 : ℚ) else 0
  ⟨zstar, w, ms, checkWitness cs (asg w) && decide (asg w z = zstar),
    lowerBoundCert cs z zstar ms && ms.length == cs.length⟩

/-! ## Printing -/

/-- Print a term. -/
partial def showTm : Tm → String
  | .bvar i => s!"#{i}"
  | .fvar x => x
  | .fn f [] => f
  | .fn f ts => f ++ "(" ++ ", ".intercalate (ts.map showTm) ++ ")"

/-- The atoms of a conjunction, `true` dropped. -/
def atomsOf : Form → List Form
  | .top => []
  | .and A B => atomsOf A ++ atomsOf B
  | A => [A]

/-- Print a formula. -/
partial def showForm : Form → String
  | .top => "true"
  | .bot => "false"
  | .pred P [] => P
  | .pred P ts => P ++ "(" ++ ", ".intercalate (ts.map showTm) ++ ")"
  | .and A B => "(" ++ showForm A ++ " ∧ " ++ showForm B ++ ")"
  | .or A B => "(" ++ showForm A ++ " ∨ " ++ showForm B ++ ")"
  | .imp A B => "(" ++ showForm A ++ " ⊃ " ++ showForm B ++ ")"
  | .circ _ A => "◯" ++ showForm A
  | .forall_ A => "∀." ++ showForm A
  | .exists_ A => "∃." ++ showForm A

/-- Print an answer. -/
def showAnswer (a : Answer) : String :=
  let c := " ∧ ".intercalate ((atomsOf a.constraint).map showForm)
  let v := match a.verdict with
    | .sat w => s!"solvable, witness {w}"
    | .unsat _ => "unsolvable (Farkas certificate)"
    | .unknown => "not decided"
  s!"answer constraint: {if c.isEmpty then "true" else c}\n  proof tree checked: {a.typed}\n  constraint: {v}"

/-- The size of a proof tree. -/
def psize : CProof → Nat
  | .top | .cstr _ _ => 1
  | .andI p q => psize p + psize q + 1
  | .orL p | .orR p | .exI _ p | .clause _ _ p => psize p + 1


/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.Engine.isSigmaB_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms isSigmaB_sound

/-- info: 'LaxLogic.QLL.Engine.mkAnswer_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mkAnswer_sound

/-- info: 'LaxLogic.QLL.Engine.answer_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms answer_sound

/-- info: 'LaxLogic.QLL.Engine.Answer.verdict_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Answer.verdict_sat

/-- info: 'LaxLogic.QLL.Engine.CSat.holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSat.holds

/-- info: 'LaxLogic.QLL.Engine.entailsLe_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms entailsLe_sound

/-- info: 'LaxLogic.QLL.Engine.entailsEq_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms entailsEq_sound

/-- info: 'LaxLogic.QLL.Engine.lowerBoundCert_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lowerBoundCert_sound

/-- info: 'LaxLogic.QLL.Engine.sumTerms_raise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sumTerms_raise

/-- info: 'LaxLogic.QLL.Engine.upClosed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms upClosed_sound

/-- info: 'LaxLogic.QLL.Engine.CSat.of_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSat.of_holds

end LaxLogic.QLL.Engine
