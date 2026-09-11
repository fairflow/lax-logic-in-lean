/-
# `LaxLogic.QLL.CLPExamples` — the draft's examples, run by the engine and checked by the kernel

For Examples 6.1 and 9.5 the kernel itself runs the engine (`runL`, which avoids
hashing) and checks the proof tree it returns, so the theorems below rest on no
compiled code.  The larger programs (the mortgage program, scheduling,
generated adders with hundreds of clauses) are run in `CLPBench.lean`, where
the same checks are executed as compiled Booleans whose soundness is proved.

**Example 6.1**, the three-component timing program:

    θ₁ = ∀s. s ≥ 5 ⊃ A₁(s),   θ₂ = ∀s. s ≥ 9 ⊃ A₂(s),
    θ₃ = ∀t. ∃s. (A₁(s) ∧ A₂(s) ∧ t ≥ s + 35) ⊃ B(t).

For the query `B(z)` the engine returns a proof tree `p`, the kernel checks it,
and the answer constraint is exactly `z ≥ 44`:

    Θ ⊢ total(p) ⊃ B(z)                                           (prv61)
    (∃σ. σ(z) = r ∧ σ ⊨ total(p))  ⟺  44 ≤ r                     (ex61_answer)

**Example 9.5.**  The draft gives the six Table 2 steps and leaves `k = 2…6` of
the translation blank.  Here the six steps are a `Steps` derivation, and
Corollary 9.8 applies to it:

    Θ ⊢ (true ∧ c₁) ∧ c₃ ⊃ true ∧ (Q ∧ true)                      (cor95)

The engine finds the same answer, and exactly the two answers `c₁ ∧ c₃` and
`c₂ ∧ c₄` when asked for all of them.
-/
import LaxLogic.QLL.CLPEngine
import LaxLogic.QLL.CLPAbstract

namespace LaxLogic.QLL.CLPExamples

open LaxLogic.QLL LaxLogic.QLL.Engine LaxLogic.QLL.LinQ LaxLogic.QLL.Surface

/-! ## Writing programs with named variables -/

def v (x : String) : NTm := .var x
def num (q : String) : NTm := .fn q []
def plus (a b : NTm) : NTm := .fn "add" [a, b]
def minus (a b : NTm) : NTm := .fn "sub" [a, b]
def times (a b : NTm) : NTm := .fn "mul" [a, b]
def at_ (P : String) (ts : List NTm) : NForm := .pred P ts
def geq (a b : NTm) : NForm := .pred "geq" [a, b]
def leq (a b : NTm) : NForm := .pred "leq" [a, b]
def lt (a b : NTm) : NForm := .pred "lt" [a, b]
def eq (a b : NTm) : NForm := .pred "eq" [a, b]

def conj : List NForm → NForm
  | [] => .top
  | [A] => A
  | A :: As => .and A (conj As)

def exs (xs : List String) (A : NForm) : NForm := xs.foldr .exists_ A

/-- `∀x̃. body ⊃ head(x̃)`. -/
def cl (head : String) (xs : List String) (body : NForm) : Clause :=
  mkClauseD xs.length head (body.toForm xs.reverse)

def query (A : NForm) : Form := A.toForm []

/-! ## Example 6.1 -/

def ex61 : Program :=
  [ cl "A1" ["s"] (geq (v "s") (num "5")),
    cl "A2" ["s"] (geq (v "s") (num "9")),
    cl "B" ["t"] (exs ["s"] (conj [at_ "A1" [v "s"], at_ "A2" [v "s"],
      geq (v "t") (plus (v "s") (num "35"))])) ]

def goal61 : Form := query (at_ "B" [v "z"])

def proof61 : CProof := ((runL ex61 isLinC false 20 goal61).map (·.1)).getD .top

theorem check61 : checkC isLinC ex61 goal61 proof61 = true := by decide +kernel

theorem prv61 : Prv ex61.forms (.imp proof61.total goal61) :=
  (checkC_sound isLinC ex61 proof61 goal61 check61).prv_total

def cs61 : List LinCon := (consOf proof61.total).getD []

theorem cons61 : (consOf proof61.total).isSome = true := by decide +kernel

/-- The least settling time and the certificate that nothing smaller is possible:
the multipliers select the critical path `z ≥ s + 35`, `s ≥ 9`. -/
def w61 : List (String × ℚ) := [("z", 44), ("_v0", 9)]
def mult61 : List ℚ := [0, 1, 1]

theorem wit61 : checkWitness cs61 (asg w61) = true := by decide +kernel
theorem at61 : asg w61 "z" = 44 := by decide +kernel
theorem lower61 : lowerBoundCert cs61 "z" 44 mult61 = true := by decide +kernel
theorem len61 : mult61.length = cs61.length := by decide +kernel
theorem up61 : upClosed cs61 "z" = true := by decide +kernel

/-- **Example 6.1.**  The answer constraint, projected onto `z`, is `z ≥ 44`. -/
theorem ex61_answer (r : ℚ) : (∃ σ, σ "z" = r ∧ CSat σ proof61.total) ↔ 44 ≤ r := by
  constructor
  · rintro ⟨σ, rfl, hσ⟩
    exact lowerBoundCert_sound lower61 len61 σ (CSat.holds hσ)
  · intro hr
    refine ⟨raise (asg w61) "z" r, by simp [raise], CSat.of_holds cons61 ?_⟩
    exact upClosed_sound up61 (by rw [at61]; exact hr) (checkWitness_sound wit61)

/-! ## Example 9.5 -/

def isC95 (B : String) : Bool := B == "c1" || B == "c2" || B == "c3" || B == "c4"

def θ1 : Clause := cl "P1" [] (at_ "c1" [])
def θ2 : Clause := cl "P2" [] (at_ "c2" [])
def θ3 : Clause := cl "Q" [] (.or (conj [at_ "P1" [], at_ "c3" []]) (conj [at_ "P2" [], at_ "c4" []]))

def ex95 : Program := [θ1, θ2, θ3]

def goal95 : Form := .pred "Q" []

def proof95 : CProof := ((runL ex95 isC95 false 20 goal95).map (·.1)).getD .top

theorem check95 : checkC isC95 ex95 goal95 proof95 = true := by decide +kernel

theorem total95 : proof95.total = .and (.pred "c1" []) (.pred "c3" []) := by decide +kernel

theorem prv95 : Prv ex95.forms (.imp (.and (.pred "c1" []) (.pred "c3" [])) goal95) :=
  total95 ▸ (checkC_sound isC95 ex95 proof95 goal95 check95).prv_total

/-- All answers: the two branches of `θ₃`. -/
theorem all95 : (proveAll ex95 isC95 false 20 goal95 ⟨[], 0⟩).map (·.1.total) =
    [.and (.pred "c1" []) (.pred "c3" []), .and (.pred "c2" []) (.pred "c4" [])] := by
  decide +kernel

def c (i : Nat) : Form := .pred s!"c{i}" []
def P (i : Nat) : Form := .pred s!"P{i}" []

/-- The draft's six steps: Rule 5, 2a, 3, 5, 1, 1. -/
theorem steps95 : Steps isC95 ex95 (fun _ => True)
    ⟨.top, [goal95]⟩ ⟨.and (.and .top (c 1)) (c 3), []⟩ :=
  .step (Step.clause (l := []) (r := []) (cl := θ3) 2 [] rfl rfl rfl (by simp)) <|
  .step (Step.orL (l := []) (r := [])) <|
  .step (Step.and (l := []) (r := [])) <|
  .step (Step.clause (l := []) (r := [c 3]) (cl := θ1) 0 [] rfl rfl rfl (by simp)) <|
  .step (Step.cstr (l := []) (r := [c 3]) rfl trivial) <|
  .step (Step.cstr (l := []) (r := []) rfl trivial) <|
  .refl _

/-- **Example 9.5**, through Corollary 9.8. -/
theorem cor95 : Prv ex95.forms
    (.imp (.and (.and .top (c 1)) (c 3)) (.and .top (.and goal95 .top))) :=
  steps_sound steps95 rfl

/-! ## The `◯` pass on the same examples

The abstract proof of `◯B(z)` against `Θ♯` is the image of the concrete tree.
Its extracted constraint is, verbatim,

    (((true ∧ s≥5) ∧ (((true ∧ s≥9) ∧ (true ∧ true)) ∧ true)) ∧ true) ∧ (true ∧ (true ∧ z ≥ s+35))

(with `s` the engine's `_v0`): the draft's `true ⊗ … ⊗` expression of §6, which it
then simplifies to `z ≥ 44`.  Here the simplification is `⊣⊢` with the total
constraint, whose projection is `ex61_answer`. -/

theorem heads61 : ex61.HeadsOK isLinC := by unfold Program.HeadsOK; decide

theorem abs61 : ATyped (ex61.abs isLinC .ex) .ex goal61 proof61.toA := by
  have h := (checkC_sound isLinC ex61 proof61 goal61 check61).toA .ex heads61
  rwa [Form.strip_pure isLinC (S := goal61) (.pred _ _) (by decide)] at h

/-- `Θ♯₂ ⊢ ◯B(z)` (Theorem 6.3). -/
theorem prvAbs61 : Prv (ex61.abs isLinC .ex).forms (.circ .ex goal61) := abs61.prv

/-- The extracted constraint is the total constraint, up to `⊣⊢` (Theorem 9.7's content). -/
theorem ext61 : PEq (proof61.toA.ext (ex61.table isLinC)).1 proof61.total :=
  let h := checkC_sound isLinC ex61 proof61 goal61 check61
  ((PEq.and_top _).symm.trans (PEq.and (PEq.refl _) (h.active_pure (by decide)).symm)).trans
    (h.ext_total heads61)

/-- Corollary 9.8 by the draft's route: `Θ ⊢ π₁|q| ⊃ B(z)`. -/
theorem cor61 : Prv ex61.forms (.imp (proof61.toA.ext (ex61.table isLinC)).1 goal61) :=
  cor_9_8_abs (by decide) abs61

theorem heads95 : ex95.HeadsOK isC95 := by unfold Program.HeadsOK; decide

/-- **Theorem 9.7 on Example 9.5**: the answer constraint `(true ∧ c₁) ∧ c₃` of the
draft's six steps is, up to `⊣⊢`, the constraint extracted from an abstract proof
of `◯Q` against `Θ♯`. -/
theorem thm97_95 : ∃ p : CProof, CTyped isC95 ex95 goal95 p ∧
    ATyped (ex95.abs isC95 .ex) .ex goal95 p.toA ∧
    PEq (.and (.and .top (c 1)) (c 3)) (p.toA.ext (ex95.table isC95)).1 :=
  thm_9_7 .ex heads95 steps95 (.pred _ _) (by decide)

/-! ## Generated programs -/

/-- A gate: its output settles `d` after all its inputs have. -/
def gate (out : String) (ins : List String) (d : Nat) : Clause :=
  cl out ["t"] (exs ["s"] (conj ((ins.map fun i => at_ i [v "s"]) ++
    [geq (v "t") (plus (v "s") (num (toString d)))])))

/-- A primary input, settled at time 0. -/
def input (x : String) : Clause := cl x ["t"] (geq (v "t") (num "0"))

/-- An `n`-bit ripple-carry adder: `7n + 1` clauses.  Delays: xor 3, and 2, or 2. -/
def adder (n : Nat) : Program :=
  input "c0" :: (List.range n).flatMap fun i =>
    let a := s!"a{i}"; let b := s!"b{i}"; let x := s!"x{i}"; let s := s!"s{i}"
    let g := s!"g{i}"; let p := s!"p{i}"; let ci := s!"c{i}"; let co := s!"c{i+1}"
    [input a, input b, gate x [a, b] 3, gate s [x, ci] 3, gate g [a, b] 2,
     gate p [x, ci] 2, gate co [g, p] 2]

/-- The CLP(R) mortgage program of Example 2.1, over ℚ. -/
def mortgage : Program :=
  [ cl "mortgage" ["P", "D", "I", "MP", "B"]
      (conj [leq (v "D") (num "1"),
             eq (plus (v "B") (v "MP")) (times (v "P") (plus (v "I") (num "1")))]),
    cl "mortgage" ["P", "D", "I", "MP", "B"]
      (conj [lt (num "1") (v "D"),
             at_ "mortgage" [minus (times (v "P") (plus (v "I") (num "1"))) (v "MP"),
                             minus (v "D") (num "1"), v "I", v "MP", v "B"]]) ]


/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.CLPExamples.check61' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check61

/-- info: 'LaxLogic.QLL.CLPExamples.prv61' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prv61

/-- info: 'LaxLogic.QLL.CLPExamples.ex61_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ex61_answer

/-- info: 'LaxLogic.QLL.CLPExamples.check95' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check95

/-- info: 'LaxLogic.QLL.CLPExamples.total95' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms total95

/-- info: 'LaxLogic.QLL.CLPExamples.prv95' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prv95

/-- info: 'LaxLogic.QLL.CLPExamples.all95' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms all95

/-- info: 'LaxLogic.QLL.CLPExamples.steps95' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms steps95

/-- info: 'LaxLogic.QLL.CLPExamples.cor95' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cor95


/-- info: 'LaxLogic.QLL.CLPExamples.abs61' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms abs61

/-- info: 'LaxLogic.QLL.CLPExamples.prvAbs61' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prvAbs61

/-- info: 'LaxLogic.QLL.CLPExamples.ext61' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ext61

/-- info: 'LaxLogic.QLL.CLPExamples.cor61' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cor61

/-- info: 'LaxLogic.QLL.CLPExamples.thm97_95' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms thm97_95

end LaxLogic.QLL.CLPExamples
