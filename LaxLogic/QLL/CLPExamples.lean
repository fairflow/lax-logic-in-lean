/-
# `LaxLogic.QLL.CLPExamples` — the draft's examples

Examples 6.1 and 9.5, run by the engine inside the kernel (`runL`) and checked
there, in both passes; Example 9.5 step by step (`run95_*`), the running
example of the CLP paper: its Table 2 run, SLD and SLD◯ runs state by state,
`Θ♯`, and the extracted constraint; the generated programs (adders, the mortgage program,
scheduling) used by `CLPBench` and `CLPWolfram`.  Write-up:
`docs/qll-clp-writeup.md`, §9.
-/
import LaxLogic.QLL.CLPEngine
import LaxLogic.QLL.CLPAbstract
import LaxLogic.QLL.CLPMachine

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

/-- The kernel runs the engine and accepts its tree. -/
theorem check61 : checkC isLinC ex61 goal61 proof61 = true := by decide +kernel

/-- Answer soundness for Example 6.1. -/
theorem prv61 : Prv ex61.forms (.imp proof61.total goal61) :=
  (checkC_sound isLinC ex61 proof61 goal61 check61).prv_total

/-- The answer constraint as linear constraints. -/
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

/-! ### Example 6.1 as the CLP paper displays it

The program, the engine's proof tree, its total constraint, and the constraint
extracted by the `◯` pass, each checked by the kernel, so that the paper's
Section 9 shows nothing computed by hand.  `_v0` is the engine's fresh
variable for the existential of `θ₂`. -/

-- equality of trees, decided by the kernel in the checks below and in those of
-- the running example
deriving instance DecidableEq for CProof
deriving instance DecidableEq for AProof
deriving instance DecidableEq for SLD.PTree
deriving instance DecidableEq for SLD.ATree
deriving instance DecidableEq for Goal

/-- The program as formulas. -/
theorem run61_program : ex61.forms =
    [.forall_ (.imp (.pred "geq" [.bvar 0, .fn "5" []]) (.pred "A1" [.bvar 0])),
     .forall_ (.imp (.pred "geq" [.bvar 0, .fn "9" []]) (.pred "A2" [.bvar 0])),
     .forall_ (.imp (.exists_ (.and (.pred "A1" [.bvar 0]) (.and (.pred "A2" [.bvar 0])
        (.pred "geq" [.bvar 1, .fn "add" [.bvar 0, .fn "35" []]]))))
        (.pred "B" [.bvar 0]))] := by
  decide +kernel

/-- The engine's proof tree for `B(z)`. -/
theorem run61_tree : proof61 =
    .clause 2 [.fvar "z"] (.exI (.fvar "_v0")
      (.andI (.clause 0 [.fvar "_v0"] (.cstr "geq" [.fvar "_v0", .fn "5" []]))
        (.andI (.clause 1 [.fvar "_v0"] (.cstr "geq" [.fvar "_v0", .fn "9" []]))
          (.cstr "geq" [.fvar "z", .fn "add" [.fvar "_v0", .fn "35" []]])))) := by
  decide +kernel

/-- Its total constraint: the three constraint leaves. -/
theorem run61_total : proof61.total =
    .and (.pred "geq" [.fvar "_v0", .fn "5" []])
      (.and (.pred "geq" [.fvar "_v0", .fn "9" []])
        (.pred "geq" [.fvar "z", .fn "add" [.fvar "_v0", .fn "35" []]])) := by
  decide +kernel

/-- The constraint extracted from the abstract image of the tree (`ext61` proves
it `⊣⊢` the total constraint). -/
theorem run61_ext : (proof61.toA.ext (ex61.table isLinC)).1 =
    .and (.and (.and (.and .top (.pred "geq" [.fvar "_v0", .fn "5" []]))
        (.and (.and (.and .top (.pred "geq" [.fvar "_v0", .fn "9" []])) (.and .top .top)) .top)) .top)
      (.and .top (.and .top (.pred "geq" [.fvar "z", .fn "add" [.fvar "_v0", .fn "35" []]]))) := by
  decide +kernel

/-! ## Example 9.5 -/

def isC95 (B : String) : Bool := B == "c1" || B == "c2" || B == "c3" || B == "c4"

def θ1 : Clause := cl "P1" [] (at_ "c1" [])
def θ2 : Clause := cl "P2" [] (at_ "c2" [])
def θ3 : Clause := cl "Q" [] (.or (conj [at_ "P1" [], at_ "c3" []]) (conj [at_ "P2" [], at_ "c4" []]))

def ex95 : Program := [θ1, θ2, θ3]

def goal95 : Form := .pred "Q" []

def proof95 : CProof := ((runL ex95 isC95 false 20 goal95).map (·.1)).getD .top

/-- The kernel runs the engine and accepts its tree. -/
theorem check95 : checkC isC95 ex95 goal95 proof95 = true := by decide +kernel

/-- The answer constraint is `c₁ ∧ c₃`. -/
theorem total95 : proof95.total = .and (.pred "c1" []) (.pred "c3" []) := by decide +kernel

/-- Answer soundness for Example 9.5. -/
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
  .step (Step.clause (l := []) (r := []) (cl := θ3) 2 [] rfl rfl rfl (by simp) rfl rfl) <|
  .step (Step.orL (l := []) (r := []) rfl rfl) <|
  .step (Step.and (l := []) (r := []) rfl rfl) <|
  .step (Step.clause (l := []) (r := [c 3]) (cl := θ1) 0 [] rfl rfl rfl (by simp) rfl rfl) <|
  .step (Step.cstr (l := []) (r := [c 3]) rfl trivial rfl rfl) <|
  .step (Step.cstr (l := []) (r := []) rfl trivial rfl rfl) <|
  .refl _

/-- **Example 9.5**, through Corollary 9.8. -/
theorem cor95 : Prv ex95.forms
    (.imp (.and (.and .top (c 1)) (c 3)) (.and .top (.and goal95 .top))) :=
  steps_sound steps95 rfl

/-! ## The `◯` pass on the same examples -/

/-- No clause head is a constraint. -/
theorem heads61 : ex61.HeadsOK isLinC := by unfold Program.HeadsOK; decide

/-- The abstract image types against `Θ♯`. -/
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

/-- No clause head is a constraint. -/
theorem heads95 : ex95.HeadsOK isC95 := by unfold Program.HeadsOK; decide

/-- **Theorem 9.7 on Example 9.5**: the answer constraint `(true ∧ c₁) ∧ c₃` of the
draft's six steps is, up to `⊣⊢`, the constraint extracted from an abstract proof
of `◯Q` against `Θ♯`. -/
theorem thm97_95 : ∃ p : CProof, CTyped isC95 ex95 goal95 p ∧
    ATyped (ex95.abs isC95 .ex) .ex goal95 p.toA ∧
    PEq (.and (.and .top (c 1)) (c 3)) (p.toA.ext (ex95.table isC95)).1 :=
  thm_9_7 .ex heads95 steps95 (.pred _ _) (by decide)

/-! ## The running example: Example 9.5, step by step

The CLP paper follows Example 9.5 through its Sections 4–7: the program, its
Table 2 run, the same run as SLD partial trees, the abstract program `Θ♯`, its
SLD◯ run, and the constraint extracted at the end.  Every program, state, tree
and constraint the paper shows for it is in a statement below, checked here. -/

/-- The program, as formulas: `c₁ ⊃ P₁`, `c₂ ⊃ P₂`, `(P₁ ∧ c₃) ∨ (P₂ ∧ c₄) ⊃ Q`. -/
theorem run95_program : ex95.forms =
    [.imp (.pred "c1" []) (.pred "P1" []),
     .imp (.pred "c2" []) (.pred "P2" []),
     .imp (.or (.and (.pred "P1" []) (.pred "c3" [])) (.and (.pred "P2" []) (.pred "c4" [])))
       (.pred "Q" [])] := by
  decide +kernel

/-- The third clause, split into Horn clauses by the indices of its body. -/
theorem run95_horn : θ3.toHorn.map Horn.form =
    [.imp (.and (.pred "P1" []) (.pred "c3" [])) (.pred "Q" []),
     .imp (.and (.pred "P2" []) (.pred "c4" [])) (.pred "Q" [])] := by
  decide +kernel

/-- The draft's six steps as a Table 2 run without pruning, state by state. -/
theorem run95_table2 :
    Step isC95 ex95 SLD.NoPrune ⟨.top, [.pred "Q" []]⟩
      ⟨.top, [.or (.and (.pred "P1" []) (.pred "c3" [])) (.and (.pred "P2" []) (.pred "c4" []))]⟩ ∧
    Step isC95 ex95 SLD.NoPrune
      ⟨.top, [.or (.and (.pred "P1" []) (.pred "c3" [])) (.and (.pred "P2" []) (.pred "c4" []))]⟩
      ⟨.top, [.and (.pred "P1" []) (.pred "c3" [])]⟩ ∧
    Step isC95 ex95 SLD.NoPrune ⟨.top, [.and (.pred "P1" []) (.pred "c3" [])]⟩
      ⟨.top, [.pred "P1" [], .pred "c3" []]⟩ ∧
    Step isC95 ex95 SLD.NoPrune ⟨.top, [.pred "P1" [], .pred "c3" []]⟩
      ⟨.top, [.pred "c1" [], .pred "c3" []]⟩ ∧
    Step isC95 ex95 SLD.NoPrune ⟨.top, [.pred "c1" [], .pred "c3" []]⟩
      ⟨.and .top (.pred "c1" []), [.pred "c3" []]⟩ ∧
    Step isC95 ex95 SLD.NoPrune ⟨.and .top (.pred "c1" []), [.pred "c3" []]⟩
      ⟨.and (.and .top (.pred "c1" [])) (.pred "c3" []), []⟩ :=
  ⟨Step.clause (l := []) (r := []) (cl := θ3) 2 [] rfl rfl rfl (by simp) rfl rfl,
   Step.orL (l := []) (r := []) rfl rfl,
   Step.and (l := []) (r := []) rfl rfl,
   Step.clause (l := []) (r := [.pred "c3" []]) (cl := θ1) 0 [] rfl rfl rfl (by simp) rfl rfl,
   Step.cstr (l := []) (r := [.pred "c3" []]) rfl trivial rfl rfl,
   Step.cstr (l := []) (r := []) rfl trivial rfl rfl⟩

/-- The proof tree the engine finds for `Q`, written out. -/
theorem run95_tree : proof95 =
    .clause 2 [] (.orL (.andI (.clause 0 [] (.cstr "c1" [])) (.cstr "c3" []))) := by
  decide +kernel

/-- The same run on SLD partial trees: each step expands one open leaf. -/
theorem run95_sld :
    SLD.SLDStep isC95 ex95 SLD.NoPrune ⟨.top, [.hole (.pred "Q" [])]⟩
      ⟨.top, [.clause 2 [] (.hole (.or (.and (.pred "P1" []) (.pred "c3" []))
        (.and (.pred "P2" []) (.pred "c4" []))))]⟩ ∧
    SLD.SLDStep isC95 ex95 SLD.NoPrune
      ⟨.top, [.clause 2 [] (.hole (.or (.and (.pred "P1" []) (.pred "c3" []))
        (.and (.pred "P2" []) (.pred "c4" []))))]⟩
      ⟨.top, [.clause 2 [] (.orL (.hole (.and (.pred "P1" []) (.pred "c3" []))))]⟩ ∧
    SLD.SLDStep isC95 ex95 SLD.NoPrune
      ⟨.top, [.clause 2 [] (.orL (.hole (.and (.pred "P1" []) (.pred "c3" []))))]⟩
      ⟨.top, [.clause 2 [] (.orL (.andI (.hole (.pred "P1" [])) (.hole (.pred "c3" []))))]⟩ ∧
    SLD.SLDStep isC95 ex95 SLD.NoPrune
      ⟨.top, [.clause 2 [] (.orL (.andI (.hole (.pred "P1" [])) (.hole (.pred "c3" []))))]⟩
      ⟨.top, [.clause 2 [] (.orL (.andI (.clause 0 [] (.hole (.pred "c1" [])))
        (.hole (.pred "c3" []))))]⟩ ∧
    SLD.SLDStep isC95 ex95 SLD.NoPrune
      ⟨.top, [.clause 2 [] (.orL (.andI (.clause 0 [] (.hole (.pred "c1" [])))
        (.hole (.pred "c3" []))))]⟩
      ⟨.and .top (.pred "c1" []), [.clause 2 [] (.orL (.andI (.clause 0 [] (.cstr "c1" []))
        (.hole (.pred "c3" []))))]⟩ ∧
    SLD.SLDStep isC95 ex95 SLD.NoPrune
      ⟨.and .top (.pred "c1" []), [.clause 2 [] (.orL (.andI (.clause 0 [] (.cstr "c1" []))
        (.hole (.pred "c3" []))))]⟩
      ⟨.and (.and .top (.pred "c1" [])) (.pred "c3" []),
        [.clause 2 [] (.orL (.andI (.clause 0 [] (.cstr "c1" [])) (.cstr "c3" [])))]⟩ :=
  ⟨.mk [] [] (.clause (cl := θ3) 2 [] rfl rfl rfl (by simp) rfl rfl rfl) rfl rfl,
   .mk [] [] (.inClause .orL) rfl rfl,
   .mk [] [] (.inClause (.inOrL .and)) rfl rfl,
   .mk [] [] (.inClause (.inOrL (.andL (.clause (cl := θ1) 0 [] rfl rfl rfl (by simp) rfl rfl rfl))))
     rfl rfl,
   .mk [] [] (.inClause (.inOrL (.andL (.inClause (.cstr rfl trivial))))) rfl rfl,
   .mk [] [] (.inClause (.inOrL (.andR (.cstr rfl trivial)))) rfl rfl⟩

/-- The goals of the seven SLD states (the store, and the open leaves from left to
right) are the seven states of the Table 2 run. -/
theorem run95_goals :
    [SLD.MState.mk .top [.hole (.pred "Q" [])],
     ⟨.top, [.clause 2 [] (.hole (.or (.and (.pred "P1" []) (.pred "c3" []))
        (.and (.pred "P2" []) (.pred "c4" []))))]⟩,
     ⟨.top, [.clause 2 [] (.orL (.hole (.and (.pred "P1" []) (.pred "c3" []))))]⟩,
     ⟨.top, [.clause 2 [] (.orL (.andI (.hole (.pred "P1" [])) (.hole (.pred "c3" []))))]⟩,
     ⟨.top, [.clause 2 [] (.orL (.andI (.clause 0 [] (.hole (.pred "c1" [])))
        (.hole (.pred "c3" []))))]⟩,
     ⟨.and .top (.pred "c1" []), [.clause 2 [] (.orL (.andI (.clause 0 [] (.cstr "c1" []))
        (.hole (.pred "c3" []))))]⟩,
     ⟨.and (.and .top (.pred "c1" [])) (.pred "c3" []),
        [.clause 2 [] (.orL (.andI (.clause 0 [] (.cstr "c1" [])) (.cstr "c3" [])))]⟩].map
      SLD.MState.goal =
    [⟨.top, [.pred "Q" []]⟩,
     ⟨.top, [.or (.and (.pred "P1" []) (.pred "c3" [])) (.and (.pred "P2" []) (.pred "c4" []))]⟩,
     ⟨.top, [.and (.pred "P1" []) (.pred "c3" [])]⟩,
     ⟨.top, [.pred "P1" [], .pred "c3" []]⟩,
     ⟨.top, [.pred "c1" [], .pred "c3" []]⟩,
     ⟨.and .top (.pred "c1" []), [.pred "c3" []]⟩,
     ⟨.and (.and .top (.pred "c1" [])) (.pred "c3" []), []⟩] := by
  decide +kernel

/-- The final SLD tree has no open leaf, and closes to the engine's proof tree. -/
theorem run95_close :
    SLD.PTree.close (.clause 2 [] (.orL (.andI (.clause 0 [] (.cstr "c1" [])) (.cstr "c3" [])))) =
      some proof95 := by
  decide +kernel

/-- The abstract program `Θ♯`: constraints replaced by `⊤`, heads made modal. -/
theorem run95_abs : (ex95.abs isC95 .ex).forms =
    [.imp .top (.circ .ex (.pred "P1" [])),
     .imp .top (.circ .ex (.pred "P2" [])),
     .imp (.or (.and (.pred "P1" []) .top) (.and (.pred "P2" []) .top)) (.circ .ex (.pred "Q" []))] := by
  decide +kernel

/-- The abstract image of the engine's proof tree. -/
theorem run95_abstree : proof95.toA = .impC 2 [] (.orL (.andC (.impC 0 [] .val) .val)) := by
  decide +kernel

/-- The SLD◯ run on `Θ♯`: the same six steps, with `cstr` become `top` and no store. -/
theorem run95_sldc :
    SLD.SLDCStep (ex95.abs isC95 .ex) .ex [.hole (.pred "Q" [])]
      [.impC 2 [] (.hole (.or (.and (.pred "P1" []) .top) (.and (.pred "P2" []) .top)))] ∧
    SLD.SLDCStep (ex95.abs isC95 .ex) .ex
      [.impC 2 [] (.hole (.or (.and (.pred "P1" []) .top) (.and (.pred "P2" []) .top)))]
      [.impC 2 [] (.orL (.hole (.and (.pred "P1" []) .top)))] ∧
    SLD.SLDCStep (ex95.abs isC95 .ex) .ex
      [.impC 2 [] (.orL (.hole (.and (.pred "P1" []) .top)))]
      [.impC 2 [] (.orL (.andC (.hole (.pred "P1" [])) (.hole .top)))] ∧
    SLD.SLDCStep (ex95.abs isC95 .ex) .ex
      [.impC 2 [] (.orL (.andC (.hole (.pred "P1" [])) (.hole .top)))]
      [.impC 2 [] (.orL (.andC (.impC 0 [] (.hole .top)) (.hole .top)))] ∧
    SLD.SLDCStep (ex95.abs isC95 .ex) .ex
      [.impC 2 [] (.orL (.andC (.impC 0 [] (.hole .top)) (.hole .top)))]
      [.impC 2 [] (.orL (.andC (.impC 0 [] .val) (.hole .top)))] ∧
    SLD.SLDCStep (ex95.abs isC95 .ex) .ex
      [.impC 2 [] (.orL (.andC (.impC 0 [] .val) (.hole .top)))]
      [.impC 2 [] (.orL (.andC (.impC 0 [] .val) .val))] :=
  ⟨.mk [] [] (.clause (cl := θ3.abs isC95 .ex) 2 [] rfl rfl rfl rfl (by simp) rfl rfl (by decide))
     rfl rfl,
   .mk [] [] (.inImp .orL) rfl rfl,
   .mk [] [] (.inImp (.inOrL .and)) rfl rfl,
   .mk [] [] (.inImp (.inOrL (.andL
     (.clause (cl := θ1.abs isC95 .ex) 0 [] rfl rfl rfl rfl (by simp) rfl rfl (by decide))))) rfl rfl,
   .mk [] [] (.inImp (.inOrL (.andL (.inImp .top)))) rfl rfl,
   .mk [] [] (.inImp (.inOrL (.andR .top))) rfl rfl⟩

/-- The SLD◯ run is the image of the SLD run under `toA`, tree by tree. -/
theorem run95_toA :
    [SLD.PTree.hole (.pred "Q" []),
     .clause 2 [] (.hole (.or (.and (.pred "P1" []) (.pred "c3" [])) (.and (.pred "P2" []) (.pred "c4" [])))),
     .clause 2 [] (.orL (.hole (.and (.pred "P1" []) (.pred "c3" [])))),
     .clause 2 [] (.orL (.andI (.hole (.pred "P1" [])) (.hole (.pred "c3" [])))),
     .clause 2 [] (.orL (.andI (.clause 0 [] (.hole (.pred "c1" []))) (.hole (.pred "c3" [])))),
     .clause 2 [] (.orL (.andI (.clause 0 [] (.cstr "c1" [])) (.hole (.pred "c3" [])))),
     .clause 2 [] (.orL (.andI (.clause 0 [] (.cstr "c1" [])) (.cstr "c3" [])))].map
      (SLD.PTree.toA isC95) =
    [.hole (.pred "Q" []),
     .impC 2 [] (.hole (.or (.and (.pred "P1" []) .top) (.and (.pred "P2" []) .top))),
     .impC 2 [] (.orL (.hole (.and (.pred "P1" []) .top))),
     .impC 2 [] (.orL (.andC (.hole (.pred "P1" [])) (.hole .top))),
     .impC 2 [] (.orL (.andC (.impC 0 [] (.hole .top)) (.hole .top))),
     .impC 2 [] (.orL (.andC (.impC 0 [] .val) (.hole .top))),
     .impC 2 [] (.orL (.andC (.impC 0 [] .val) .val))] := by
  decide +kernel

/-- The final SLD◯ tree closes to the abstract image of the engine's proof tree. -/
theorem run95_closeA :
    SLD.ATree.close (.impC 2 [] (.orL (.andC (.impC 0 [] .val) .val))) = some proof95.toA := by
  decide +kernel

/-- The constraint extracted from the abstract proof, read with the program's table. -/
theorem run95_ext :
    (AProof.ext (ex95.table isC95) (.impC 2 [] (.orL (.andC (.impC 0 [] .val) .val)))).1 =
      .and (.and (.and (.and .top (.pred "c1" [])) (.and .top .top)) .top)
        (.and .top (.pred "c3" [])) := by
  decide +kernel

/-- **Theorem 9.7 on the running example**: the extracted constraint is, up to `⊣⊢`,
the answer `(⊤ ∧ c₁) ∧ c₃` of the Table 2 run. -/
theorem run95_agree :
    PEq (AProof.ext (ex95.table isC95) (.impC 2 [] (.orL (.andC (.impC 0 [] .val) .val)))).1
      (.and (.and .top (.pred "c1" [])) (.pred "c3" [])) := by
  rw [run95_ext]
  exact ⟨.andI (.andE₁ (.andE₁ (.andE₁ .hd))) (.andE₂ (.andE₂ .hd)),
    .andI (.andI (.andI (.andE₁ .hd) (.andI .topI .topI)) .topI) (.andI .topI (.andE₂ .hd))⟩

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

/-- info: 'LaxLogic.QLL.CLPExamples.run61_program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run61_program

/-- info: 'LaxLogic.QLL.CLPExamples.run61_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run61_tree

/-- info: 'LaxLogic.QLL.CLPExamples.run61_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run61_total

/-- info: 'LaxLogic.QLL.CLPExamples.run61_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run61_ext

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

/-! The running example's checks. -/

/-- info: 'LaxLogic.QLL.CLPExamples.run95_program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run95_program

/-- info: 'LaxLogic.QLL.CLPExamples.run95_horn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run95_horn

/-- info: 'LaxLogic.QLL.CLPExamples.run95_table2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run95_table2

/-- info: 'LaxLogic.QLL.CLPExamples.run95_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run95_tree

/-- info: 'LaxLogic.QLL.CLPExamples.run95_sld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run95_sld

/-- info: 'LaxLogic.QLL.CLPExamples.run95_goals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run95_goals

/-- info: 'LaxLogic.QLL.CLPExamples.run95_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run95_close

/-- info: 'LaxLogic.QLL.CLPExamples.run95_abstree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run95_abstree

/-- info: 'LaxLogic.QLL.CLPExamples.run95_abs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run95_abs

/-- info: 'LaxLogic.QLL.CLPExamples.run95_sldc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run95_sldc

/-- info: 'LaxLogic.QLL.CLPExamples.run95_toA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run95_toA

/-- info: 'LaxLogic.QLL.CLPExamples.run95_closeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run95_closeA

/-- info: 'LaxLogic.QLL.CLPExamples.run95_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run95_ext

/-- info: 'LaxLogic.QLL.CLPExamples.run95_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run95_agree

/-- Precedence scheduling with one shared machine (a disjunctive constraint). -/
def sched : Program :=
  [ cl "schedule" ["Sa", "Sb", "Sc", "Sd", "E"] (conj [
      geq (v "Sa") (num "0"),
      geq (v "Sb") (plus (v "Sa") (num "3")),
      geq (v "Sc") (plus (v "Sa") (num "3")),
      geq (v "Sc") (num "4"),
      geq (v "Sd") (plus (v "Sb") (num "2")),
      geq (v "Sd") (plus (v "Sc") (num "4")),
      geq (v "E") (plus (v "Sd") (num "2")),
      at_ "disjoint" [v "Sc", num "4", v "Sb", num "2"]]),
    cl "disjoint" ["X", "DX", "Y", "DY"] (geq (v "Y") (plus (v "X") (v "DX"))),
    cl "disjoint" ["X", "DX", "Y", "DY"] (geq (v "X") (plus (v "Y") (v "DY"))) ]

end LaxLogic.QLL.CLPExamples
