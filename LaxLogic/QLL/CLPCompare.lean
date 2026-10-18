/-
# `LaxLogic.QLL.CLPCompare` — the mortgage program, measured against SWI-Prolog

The comparison of the CLP paper's Section 12.  The program is the mortgage
program of Example 2.1 of the 1997 report (`CLPExamples.mortgage`, unchanged);
the query is `mortgage(P, D, 1/100, 1721.65, 0)` for a range of durations `D`.
The same program text runs under SWI-Prolog's `library(clpq)`
(`scripts/clp-compare/mortgage.pl`).

The work splits as in lean-certify: an untrusted producer, Boolean checkers
with soundness theorems, and a kernel-checked verdict.

* `produce` (untrusted): the engine's search (`run`, eager pruning), then
  Fourier–Motzkin (`fm`) for a witness fixing `P`, and twice more for the
  Farkas multipliers refuting `P < v` and `P > v`.
* `checkTree`, `checkSat`, `checkBelow`, `checkAbove`: the Boolean checkers
  `checkC`, `checkWitness` and `checkFarkas`, sound by `checkC_sound`,
  `checkWitness_sound` and `checkFarkas_unsat`.
* `answerK`: answer soundness, `Θ ⊢ c ↠ G`, packaged as a lean-certify
  `Certifier` from `checkC_sound` and `CTyped.prv_total`; its verdicts are
  checked by the kernel (`Certifier.verdict`, `decide +kernel`) with the axioms
  `[propext, Quot.sound]`.  The arithmetic checkers are not packaged: their
  soundness theorems use `Classical.choice` (through Mathlib's `ℚ`), outside
  lean-certify's axiom allow-list.

The benchmark driver is `tools/ClpCompare.lean` (executable `clpcompare`).
-/
import LaxLogic.QLL.CLPExamples
import LeanCertify

namespace LaxLogic.QLL.Compare

open LaxLogic.QLL LaxLogic.QLL.Engine LaxLogic.QLL.LinQ LaxLogic.QLL.CLPExamples Certify

/-! ## Answer soundness as a lean-certify certifier -/

/-- A specification: the constraint classifier, the program, the query, and
the claimed answer constraint. -/
abbrev AnsSpec := (String → Bool) × Program × Form × Form

/-- **Answer soundness as a certifier.**  The certificate is a proof tree
whose total constraint is the claimed answer `c`; the property is
`Θ ⊢ c ↠ G`.  The soundness proof is `checkC_sound` followed by
`CTyped.prv_total`. -/
def answerK : Certifier AnsSpec CProof (fun s => Prv s.2.1.forms (.imp s.2.2.2 s.2.2.1)) where
  check s p := checkC s.1 s.2.1 s.2.2.1 p && decide (p.total = s.2.2.2)
  sound s p h := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2 ▸ (checkC_sound s.1 s.2.1 p s.2.2.1 h.1).prv_total

/-! ## The query, the producer and the checkers -/

/-- The query `mortgage(P, D, 1/100, 1721.65, 0)`. -/
def mgQuery (d : Nat) : Form :=
  query (at_ "mortgage" [v "P", num (toString d), num "1/100", num "172165/100", num "0"])

/-- A depth bound for the search, linear in `D` (the search never reaches it). -/
def mgFuel (d : Nat) : Nat := 10 * d + 50

/-- `P − v < 0` and `v − P < 0`: the two constraints whose refutation fixes `P = v`. -/
def belowCon (v : ℚ) : LinCon := ⟨(Lin.var "P").sub (Lin.cst v), .lt⟩
def aboveCon (v : ℚ) : LinCon := ⟨(Lin.cst v).sub (Lin.var "P"), .lt⟩

/-- What the untrusted producer returns: the proof tree, the answer constraint
read as linear constraints, a witness, the value of `P`, and Farkas
multipliers refuting `P < v` and `P > v`. -/
structure Produced where
  tree : CProof
  cons : List LinCon
  witness : List (String × ℚ)
  value : ℚ
  below : List ℚ
  above : List ℚ

/-- The search alone. -/
def search (d : Nat) : Option CProof :=
  (run mortgage isLinC true (mgFuel d) (mgQuery d)).map (·.1)

/-- The arithmetic producer on a found tree: `fm`, untrusted. -/
def arith (p : CProof) : Option Produced :=
  match consOf p.total with
  | none => none
  | some cs =>
    match fm cs with
    | .sat w =>
      let val := asg w "P"
      match fm (cs ++ [belowCon val]), fm (cs ++ [aboveCon val]) with
      | .unsat m₁, .unsat m₂ => some ⟨p, cs, w, val, m₁, m₂⟩
      | _, _ => none
    | _ => none

/-- The tree check: `checkC` (sound by `checkC_sound`). -/
def checkTree (d : Nat) (r : Produced) : Bool := checkC isLinC mortgage (mgQuery d) r.tree

/-- The answer constraint, read from the tree as linear constraints. -/
def treeCons (r : Produced) : List LinCon := (consOf r.tree.total).getD [⟨Lin.cst 1, .le⟩]

/-- The witness satisfies the answer constraint (`checkWitness_sound`).  The
constraints are read from the tree again, not taken from the producer. -/
def checkSat (r : Produced) : Bool := checkWitness (treeCons r) (asg r.witness)

/-- No solution has `P < v` (`checkFarkas_unsat`). -/
def checkBelow (r : Produced) : Bool :=
  checkFarkas (r.below.zip (treeCons r ++ [belowCon r.value]))

/-- No solution has `P > v` (`checkFarkas_unsat`). -/
def checkAbove (r : Produced) : Bool :=
  checkFarkas (r.above.zip (treeCons r ++ [aboveCon r.value]))

/-! ## The certifier on Example 9.5, and the gate watched failing -/

/-- Corollary 9.8 for Example 9.5, through the certifier: the total `c1 ∧ c3`
of the tree implies the query. -/
theorem answer95 : Prv ex95.forms (.imp (.and (.pred "c1" []) (.pred "c3" [])) goal95) :=
  answerK.verdict (isC95, ex95, goal95, .and (.pred "c1" []) (.pred "c3" []))
    (.clause 2 [] (.orL (.andI (.clause 0 [] (.cstr "c1" [])) (.cstr "c3" []))))

/-- info: 'LaxLogic.QLL.Compare.answer95' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms answer95

/-- info: R4 passes: answer95 depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms answer95

/-- info: R3 passes: the evaluation path of answerK is structural -/
#guard_msgs in #certify_structural answerK

/-- info: R2 passes: the property of answerK mentions no budget -/
#guard_msgs in #certify_statement answerK

/-- The gate rejects a tree that applies the wrong disjunct. -/
example : answerK.check (isC95, ex95, goal95, .and (.pred "c1" []) (.pred "c3" []))
    (.clause 2 [] (.orR (.andI (.clause 0 [] (.cstr "c1" [])) (.cstr "c3" [])))) = false := by
  decide +kernel

/-! ## Printing a certificate as Lean source, for the kernel-checked fact files -/

partial def litTm : Tm → String
  | .fvar x => s!"(Tm.fvar {x.quote})"
  | .bvar n => s!"(Tm.bvar {n})"
  | .fn f ts => s!"(Tm.fn {f.quote} [{", ".intercalate (ts.map litTm)}])"

partial def litTree : CProof → String
  | .top => "CProof.top"
  | .cstr B ts => s!"(CProof.cstr {B.quote} [{", ".intercalate (ts.map litTm)}])"
  | .andI p q => s!"(CProof.andI {litTree p} {litTree q})"
  | .orL p => s!"(CProof.orL {litTree p})"
  | .orR p => s!"(CProof.orR {litTree p})"
  | .exI t p => s!"(CProof.exI {litTm t} {litTree p})"
  | .clause w ts p => s!"(CProof.clause {w} [{", ".intercalate (ts.map litTm)}] {litTree p})"

end LaxLogic.QLL.Compare
