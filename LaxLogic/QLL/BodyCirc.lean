/-
# `LaxLogic.QLL.BodyCirc` — `◯` in clause bodies

Clause bodies are Σ-formulas (Def 5.1, `IsSigma`), so `◯` occurs only at a
clause head.  This module settles what a body `◯` would buy, and the answer
turns on the head.

**With a plain head, a body `◯` is strictly stronger** — it lets a lax premise
justify a non-lax conclusion, i.e. it *discharges* a constraint:

    (A ∧ ◯B) ⊃ P   ⊢   (A ∧ B) ⊃ P                            (`body_circ_to_plain`)
    (A ∧ B) ⊃ P    ⊬   (A ∧ ◯B) ⊃ P                           (`not_prv_plain_to_body_circ`)

The countermodel is two worlds `w0 ≤ w1`, every arrow modal, nothing fallible,
`A` everywhere and `B`, `P` at `w1` only.  Discharging is the fault refuted in
`HerbrandCLP.p66_refuted`, and is sound only under `⊢ ◯c` (`p66_with_lax`).

**With a modal head the two forms are interderivable**, because `◯E` absorbs the
body's `◯`:

    (A ∧ ◯B) ⊃ ◯P   ⊣⊢   (A ∧ B) ⊃ ◯P              (`clause3`, `clause4`)
    ∀t. (A t ∧ ◯B t) ⊃ ◯P t  ⊣⊢  ∀t. (A t ∧ B t) ⊃ ◯P t   (`fo_I_to_II`, `fo_II_to_I`)

Since every clause of an abstract program `Θ♯` has a modal head, a body `◯`
adds nothing there: it is `val`, contributing `⊤`.  Nesting the same `◯` adds
nothing either, `◯◯A ⊣⊢ ◯A` (`circ_circ_iff`); layers would need a family of
modalities, not more of one.

**Operationally** (the program at the end): the constraints in an answer come
from the clauses that carry them, once each, however indirectly they are
reached.  For `θ₂ : ∀t. P(t) ⊃ Q(t)`, whose body is a bare atom, the table
entry is `true`, and the answer for `Q(z)` is exactly `θ₀`'s and `θ₁`'s
constraints.  So exercising the body-`◯` form neither adds a constraint term
nor relaxes one.
-/
import LaxLogic.QLL.CLPExamples

namespace LaxLogic.QLL.BodyCirc

open LaxLogic.QLL LaxLogic.QLL.Engine LaxLogic.QLL.LinQ LaxLogic.QLL.CLPExamples

/-! ## Nesting one `◯` adds nothing -/

/-- `◯` is idempotent, so `◯`-depth is not a layering device. -/
theorem circ_circ_iff (Γ : List Form) (q : Q) (A : Form) :
    Prv Γ (.circ q (.circ q A)) ↔ Prv Γ (.circ q A) :=
  ⟨fun h => Prv.circE h (Prv.var (List.Mem.head _)), fun h => Prv.circI h⟩

/-! ## A plain head: the body `◯` is strictly stronger -/

/-- A body `◯` implies the same clause with the `◯` deleted. -/
theorem body_circ_to_plain (q : Q) (A B P : Form) :
    Prv [.imp (.and A (.circ q B)) P] (.imp (.and A B) P) :=
  Prv.impI (Prv.impE (Prv.var (List.Mem.tail _ (List.Mem.head _)))
    (Prv.andI (Prv.andE₁ (Prv.var (List.Mem.head _)))
      (Prv.circI (Prv.andE₂ (Prv.var (List.Mem.head _))))))

/-- Two worlds `w0 ≤ w1`. -/
inductive W2 | w0 | w1
  deriving DecidableEq

/-- The order `w0 ≤ w1`. -/
def W2.le : W2 → W2 → Bool
  | .w0, _   => true
  | .w1, .w1 => true
  | _,   _   => false

/-- Every arrow modal, nothing fallible; `A` everywhere, `B` and `P` at `w1`. -/
def m2 : KModel where
  S := W2
  D := Unit
  Dom _ _ := True
  Ri a b := W2.le a b = true
  RA a b := W2.le a b = true
  RE a b := W2.le a b = true
  Fl _ := False
  refl_i a := by cases a <;> rfl
  trans_i := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  refl_A a := by cases a <;> rfl
  trans_A := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  sub_A h := h
  refl_E a := by cases a <;> rfl
  trans_E := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  sub_E h := h
  dom_mono _ _ := trivial
  d₀ := ()
  dom_d₀ _ := trivial
  hered_Fl := by intro a b _ h; exact h.elim
  fn _ _ := ()
  I w p _ := match w with
    | .w0 => p = "A"
    | .w1 => True
  hered_I := by
    intro a b p ds h hI
    cases a <;> cases b <;>
      first | exact hI | exact trivial | exact absurd h (by decide)
  fn_dom _ := trivial

/-- The converse fails: with a plain head, a body `◯` discharges a constraint. -/
theorem not_prv_plain_to_body_circ :
    ¬ Prv [.imp (.and (.pred "A" []) (.pred "B" [])) (.pred "P" [])]
        (.imp (.and (.pred "A" []) (.circ .ex (.pred "B" []))) (.pred "P" [])) := by
  intro h
  have hyp : ∀ C ∈ [Form.imp (.and (.pred "A" []) (.pred "B" [])) (.pred "P" [])],
      m2.force C W2.w0 (fun _ => ()) [] := by
    intro C hC
    rcases List.mem_singleton.1 hC with rfl
    intro v _ hAB
    cases v with
    | w0 =>
        rcases hAB.2 with h' | h'
        · exact h'.elim
        · have hb : ("B" : String) = "A" := h'
          exact absurd hb (by decide)
    | w1 => exact Or.inr trivial
  have hs := Prv.sound h m2 W2.w0 (fun _ => ()) (fun _ _ => trivial) hyp
  have hA : m2.force (.pred "A" []) W2.w0 (fun _ => ()) [] := Or.inr rfl
  have hcB : m2.force (.circ .ex (.pred "B" [])) W2.w0 (fun _ => ()) [] := by
    intro v _
    cases v with
    | w0 => exact ⟨W2.w1, rfl, Or.inr trivial⟩
    | w1 => exact ⟨W2.w1, rfl, Or.inr trivial⟩
  rcases hs W2.w0 rfl ⟨hA, hcB⟩ with h' | h'
  · exact h'.elim
  · have hp : ("P" : String) = "A" := h'
    exact absurd hp (by decide)

/-! ## A modal head: the two clause forms are interderivable -/

/-- `(A ∧ ◯B) ⊃ ◯P  ⊢  (A ∧ B) ⊃ ◯P`. -/
theorem clause3 (q : Q) (A B P : Form) :
    Prv [.imp (.and A (.circ q B)) (.circ q P)] (.imp (.and A B) (.circ q P)) := by
  refine Prv.impI ?_
  have hab : Prv [Form.and A B, .imp (.and A (.circ q B)) (.circ q P)] (.and A B) :=
    Prv.var (List.Mem.head _)
  have hcl : Prv [Form.and A B, .imp (.and A (.circ q B)) (.circ q P)]
      (.imp (.and A (.circ q B)) (.circ q P)) :=
    Prv.var (List.Mem.tail _ (List.Mem.head _))
  exact Prv.impE hcl (Prv.andI (Prv.andE₁ hab) (Prv.circI (Prv.andE₂ hab)))

/-- The converse, available because the head is modal: `◯E` absorbs the body's `◯`. -/
theorem clause4 (q : Q) (A B P : Form) :
    Prv [.imp (.and A B) (.circ q P)] (.imp (.and A (.circ q B)) (.circ q P)) := by
  refine Prv.impI ?_
  have h1 : Prv [Form.and A (.circ q B), .imp (.and A B) (.circ q P)] (.and A (.circ q B)) :=
    Prv.var (List.Mem.head _)
  refine Prv.circE (Prv.andE₂ h1) ?_
  have h2 : Prv [B, Form.and A (.circ q B), .imp (.and A B) (.circ q P)] (.and A (.circ q B)) :=
    Prv.var (List.Mem.tail _ (List.Mem.head _))
  have hB : Prv [B, Form.and A (.circ q B), .imp (.and A B) (.circ q P)] B :=
    Prv.var (List.Mem.head _)
  have hcl : Prv [B, Form.and A (.circ q B), .imp (.and A B) (.circ q P)]
      (.imp (.and A B) (.circ q P)) :=
    Prv.var (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  exact Prv.impE hcl (Prv.andI (Prv.andE₁ h2) hB)

/-! ## The same, first-order -/

/-- `∀t. (A t ∧ ◯B t) ⊃ ◯P t`. -/
def clI (q : Q) : Form :=
  .forall_ (.imp (.and (.pred "A" [.bvar 0]) (.circ q (.pred "B" [.bvar 0])))
    (.circ q (.pred "P" [.bvar 0])))

/-- `∀t. (A t ∧ B t) ⊃ ◯P t`. -/
def clII (q : Q) : Form :=
  .forall_ (.imp (.and (.pred "A" [.bvar 0]) (.pred "B" [.bvar 0]))
    (.circ q (.pred "P" [.bvar 0])))

theorem fo_I_to_II (q : Q) : Prv [clI q] (clII q) := by
  refine Prv.allI_of_fresh (c := "w") (by cases q <;> decide) (by cases q <;> decide) ?_
  show Prv [clI q] (.imp (.and (.pred "A" [.fvar "w"]) (.pred "B" [.fvar "w"]))
    (.circ q (.pred "P" [.fvar "w"])))
  refine Prv.impI ?_
  have hcl : Prv [Form.and (.pred "A" [.fvar "w"]) (.pred "B" [.fvar "w"]), clI q]
      (.imp (.and (.pred "A" [.fvar "w"]) (.circ q (.pred "B" [.fvar "w"])))
        (.circ q (.pred "P" [.fvar "w"]))) :=
    Prv.allE (.fvar "w") trivial (Prv.var (List.Mem.tail _ (List.Mem.head _)))
  have hab : Prv [Form.and (.pred "A" [.fvar "w"]) (.pred "B" [.fvar "w"]), clI q]
      (.and (.pred "A" [.fvar "w"]) (.pred "B" [.fvar "w"])) :=
    Prv.var (List.Mem.head _)
  exact Prv.impE hcl (Prv.andI (Prv.andE₁ hab) (Prv.circI (Prv.andE₂ hab)))

theorem fo_II_to_I (q : Q) : Prv [clII q] (clI q) := by
  refine Prv.allI_of_fresh (c := "w") (by cases q <;> decide) (by cases q <;> decide) ?_
  show Prv [clII q] (.imp (.and (.pred "A" [.fvar "w"]) (.circ q (.pred "B" [.fvar "w"])))
    (.circ q (.pred "P" [.fvar "w"])))
  refine Prv.impI ?_
  have h1 : Prv [Form.and (.pred "A" [.fvar "w"]) (.circ q (.pred "B" [.fvar "w"])), clII q]
      (.and (.pred "A" [.fvar "w"]) (.circ q (.pred "B" [.fvar "w"]))) :=
    Prv.var (List.Mem.head _)
  refine Prv.circE (Prv.andE₂ h1) ?_
  have h2 : Prv [Form.pred "B" [.fvar "w"],
      Form.and (.pred "A" [.fvar "w"]) (.circ q (.pred "B" [.fvar "w"])), clII q]
      (.and (.pred "A" [.fvar "w"]) (.circ q (.pred "B" [.fvar "w"]))) :=
    Prv.var (List.Mem.tail _ (List.Mem.head _))
  have hB : Prv [Form.pred "B" [.fvar "w"],
      Form.and (.pred "A" [.fvar "w"]) (.circ q (.pred "B" [.fvar "w"])), clII q]
      (.pred "B" [.fvar "w"]) :=
    Prv.var (List.Mem.head _)
  have hcl : Prv [Form.pred "B" [.fvar "w"],
      Form.and (.pred "A" [.fvar "w"]) (.circ q (.pred "B" [.fvar "w"])), clII q]
      (.imp (.and (.pred "A" [.fvar "w"]) (.pred "B" [.fvar "w"]))
        (.circ q (.pred "P" [.fvar "w"]))) :=
    Prv.allE (.fvar "w") trivial (Prv.var (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  exact Prv.impE hcl (Prv.andI (Prv.andE₁ h2) hB)

/-! ## Indirect firing: a first-order program

    θ₀ : ∀s. s ≥ 5 ⊃ B(s)
    θ₁ : ∀t. (∃s. B(s) ∧ t ≥ s + 2) ⊃ P(t)
    θ₂ : ∀t. P(t) ⊃ Q(t)

The goal `Q(z)` matches `θ₂`, whose body is a bare atom; the constraints reach
the answer through `θ₁` and `θ₀`. -/
def exQ : Program :=
  [ cl "B" ["s"] (geq (v "s") (num "5")),
    cl "P" ["t"] (exs ["s"] (conj [at_ "B" [v "s"], geq (v "t") (plus (v "s") (num "2"))])),
    cl "Q" ["t"] (at_ "P" [v "t"]) ]

def goalQ : Form := query (at_ "Q" [v "z"])

def proofQ : CProof := ((runL exQ isLinC false 20 goalQ).map (·.1)).getD .top

/-- The kernel runs the engine and accepts its tree. -/
theorem checkQ : checkC isLinC exQ goalQ proofQ = true := by decide +kernel

/-- Answer soundness: `Θ ⊢ total(p) ⊃ Q(z)`. -/
theorem prvQ : Prv exQ.forms (.imp proofQ.total goalQ) :=
  (checkC_sound isLinC exQ proofQ goalQ checkQ).prv_total

theorem headsQ : exQ.HeadsOK isLinC := by unfold Program.HeadsOK; decide

/-- The abstract image types against `Θ♯`. -/
theorem absQ : ATyped (exQ.abs isLinC .ex) .ex goalQ proofQ.toA := by
  have h := (checkC_sound isLinC exQ proofQ goalQ checkQ).toA .ex headsQ
  rwa [Form.strip_pure isLinC (S := goalQ) (.pred _ _) (by decide)] at h

/-- The extracted constraint is the answer constraint, up to `⊣⊢`. -/
theorem extQ : PEq (proofQ.toA.ext (exQ.table isLinC)).1 proofQ.total :=
  let h := checkC_sound isLinC exQ proofQ goalQ checkQ
  ((PEq.and_top _).symm.trans (PEq.and (PEq.refl _) (h.active_pure (by decide)).symm)).trans
    (h.ext_total headsQ)

-- The answer for `Q(z)`: exactly `θ₀`'s and `θ₁`'s constraints.
/-- info: some "(geq(_v0, 5) ∧ geq(z, add(_v0, 2)))" -/
#guard_msgs in #eval (runL exQ isLinC false 20 goalQ).map (fun r => showForm r.1.total)

-- The same constraint from the `◯` pass, with the `⊤` units of the writer monad.
/-- info: "(((((true ∧ geq(_v0, 5)) ∧ (true ∧ true)) ∧ true) ∧ (true ∧ geq(z, add(_v0, 2)))) ∧ true)" -/
#guard_msgs in #eval showForm (proofQ.toA.ext (exQ.table isLinC)).1

-- The indirect clause `θ₂` contributes nothing: its table entry is `⊤`.
/-- info: "true" -/
#guard_msgs in #eval showForm (exQ.table isLinC 2 [Tm.fvar "z"] proofQ.wit)

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.BodyCirc.circ_circ_iff' does not depend on any axioms -/
#guard_msgs in #print axioms circ_circ_iff

/-- info: 'LaxLogic.QLL.BodyCirc.clause4' does not depend on any axioms -/
#guard_msgs in #print axioms clause4

/-- info: 'LaxLogic.QLL.BodyCirc.not_prv_plain_to_body_circ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms not_prv_plain_to_body_circ

/-- info: 'LaxLogic.QLL.BodyCirc.fo_II_to_I' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fo_II_to_I

/-- info: 'LaxLogic.QLL.BodyCirc.extQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extQ

end LaxLogic.QLL.BodyCirc
