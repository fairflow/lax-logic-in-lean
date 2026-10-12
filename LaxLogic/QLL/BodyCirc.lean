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
    ∀t. (∃s. ◯B s ∧ C s t) ⊃ ◯P t  ⊣⊢  ∀t. (∃s. B s ∧ C s t) ⊃ ◯P t
                                       (`fo_ex_I_to_II`, `fo_ex_II_to_I`)

the last being the shape a clause body actually has: the `◯` sits under the
existential, and `◯E` still absorbs it.

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

**The inclusion lemma.**  What distinguishes two derivations of one `◯S` is
the multiset of table entries they summon (`AProof.entries`); everything else
is identified by the monad laws.  Inclusion of entries gives entailment of
the extracted constraints for every table:

    entries a ⊆ entries a'   →   π₁|a'|_T ⊢ π₁|a|_T          (`AProof.ext_prv_of_entries_subset`)

so a derivation summoning fewer entries can be preferred at the abstract
level, before any constraint is looked at.
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

/-! ## The same with `◯` under an existential — the shape a clause body actually has -/

/-- `∀t. (∃s. ◯B s ∧ C s t) ⊃ ◯P t`. -/
def clEI (q : Q) : Form :=
  .forall_ (.imp (.exists_ (.and (.circ q (.pred "B" [.bvar 0])) (.pred "C" [.bvar 0, .bvar 1])))
    (.circ q (.pred "P" [.bvar 0])))

/-- `∀t. (∃s. B s ∧ C s t) ⊃ ◯P t`. -/
def clEII (q : Q) : Form :=
  .forall_ (.imp (.exists_ (.and (.pred "B" [.bvar 0]) (.pred "C" [.bvar 0, .bvar 1])))
    (.circ q (.pred "P" [.bvar 0])))

theorem fo_ex_I_to_II (q : Q) : Prv [clEI q] (clEII q) := by
  refine Prv.allI_of_fresh (c := "w") (by cases q <;> decide) (by cases q <;> decide) ?_
  show Prv [clEI q]
    (.imp (.exists_ (.and (.pred "B" [.bvar 0]) (.pred "C" [.bvar 0, .fvar "w"])))
      (.circ q (.pred "P" [.fvar "w"])))
  refine Prv.impI ?_
  refine Prv.exE_of_fresh (c := "u") (by cases q <;> decide) (by cases q <;> decide)
    (by cases q <;> decide) (Prv.var (List.Mem.head _)) ?_
  have hbc : Prv [Form.and (.pred "B" [.fvar "u"]) (.pred "C" [.fvar "u", .fvar "w"]),
      Form.exists_ (.and (.pred "B" [.bvar 0]) (.pred "C" [.bvar 0, .fvar "w"])), clEI q]
      (.and (.pred "B" [.fvar "u"]) (.pred "C" [.fvar "u", .fvar "w"])) :=
    Prv.var (List.Mem.head _)
  have hcl : Prv [Form.and (.pred "B" [.fvar "u"]) (.pred "C" [.fvar "u", .fvar "w"]),
      Form.exists_ (.and (.pred "B" [.bvar 0]) (.pred "C" [.bvar 0, .fvar "w"])), clEI q]
      (.imp (.exists_ (.and (.circ q (.pred "B" [.bvar 0])) (.pred "C" [.bvar 0, .fvar "w"])))
        (.circ q (.pred "P" [.fvar "w"]))) :=
    Prv.allE (.fvar "w") trivial
      (Prv.var (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hex : Prv [Form.and (.pred "B" [.fvar "u"]) (.pred "C" [.fvar "u", .fvar "w"]),
      Form.exists_ (.and (.pred "B" [.bvar 0]) (.pred "C" [.bvar 0, .fvar "w"])), clEI q]
      (.exists_ (.and (.circ q (.pred "B" [.bvar 0])) (.pred "C" [.bvar 0, .fvar "w"]))) :=
    Prv.exI (.fvar "u") trivial (Prv.andI (Prv.circI (Prv.andE₁ hbc)) (Prv.andE₂ hbc))
  exact Prv.impE hcl hex

theorem fo_ex_II_to_I (q : Q) : Prv [clEII q] (clEI q) := by
  refine Prv.allI_of_fresh (c := "w") (by cases q <;> decide) (by cases q <;> decide) ?_
  show Prv [clEII q]
    (.imp (.exists_ (.and (.circ q (.pred "B" [.bvar 0])) (.pred "C" [.bvar 0, .fvar "w"])))
      (.circ q (.pred "P" [.fvar "w"])))
  refine Prv.impI ?_
  refine Prv.exE_of_fresh (c := "u") (by cases q <;> decide) (by cases q <;> decide)
    (by cases q <;> decide) (Prv.var (List.Mem.head _)) ?_
  have h1 : Prv [Form.and (.circ q (.pred "B" [.fvar "u"])) (.pred "C" [.fvar "u", .fvar "w"]),
      Form.exists_ (.and (.circ q (.pred "B" [.bvar 0])) (.pred "C" [.bvar 0, .fvar "w"])),
      clEII q]
      (.and (.circ q (.pred "B" [.fvar "u"])) (.pred "C" [.fvar "u", .fvar "w"])) :=
    Prv.var (List.Mem.head _)
  refine Prv.circE (Prv.andE₁ h1) ?_
  have h2 : Prv [Form.pred "B" [.fvar "u"],
      Form.and (.circ q (.pred "B" [.fvar "u"])) (.pred "C" [.fvar "u", .fvar "w"]),
      Form.exists_ (.and (.circ q (.pred "B" [.bvar 0])) (.pred "C" [.bvar 0, .fvar "w"])),
      clEII q]
      (.and (.circ q (.pred "B" [.fvar "u"])) (.pred "C" [.fvar "u", .fvar "w"])) :=
    Prv.var (List.Mem.tail _ (List.Mem.head _))
  have hB : Prv [Form.pred "B" [.fvar "u"],
      Form.and (.circ q (.pred "B" [.fvar "u"])) (.pred "C" [.fvar "u", .fvar "w"]),
      Form.exists_ (.and (.circ q (.pred "B" [.bvar 0])) (.pred "C" [.bvar 0, .fvar "w"])),
      clEII q]
      (.pred "B" [.fvar "u"]) :=
    Prv.var (List.Mem.head _)
  have hcl : Prv [Form.pred "B" [.fvar "u"],
      Form.and (.circ q (.pred "B" [.fvar "u"])) (.pred "C" [.fvar "u", .fvar "w"]),
      Form.exists_ (.and (.circ q (.pred "B" [.bvar 0])) (.pred "C" [.bvar 0, .fvar "w"])),
      clEII q]
      (.imp (.exists_ (.and (.pred "B" [.bvar 0]) (.pred "C" [.bvar 0, .fvar "w"])))
        (.circ q (.pred "P" [.fvar "w"]))) :=
    Prv.allE (.fvar "w") trivial
      (Prv.var (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  have hex : Prv [Form.pred "B" [.fvar "u"],
      Form.and (.circ q (.pred "B" [.fvar "u"])) (.pred "C" [.fvar "u", .fvar "w"]),
      Form.exists_ (.and (.circ q (.pred "B" [.bvar 0])) (.pred "C" [.bvar 0, .fvar "w"])),
      clEII q]
      (.exists_ (.and (.pred "B" [.bvar 0]) (.pred "C" [.bvar 0, .fvar "w"]))) :=
    Prv.exI (.fvar "u") trivial (Prv.andI hB (Prv.andE₂ h2))
  exact Prv.impE hcl hex

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

end LaxLogic.QLL.BodyCirc

namespace LaxLogic.QLL

/-! ## The inclusion lemma: which table entries a derivation summons

Two abstract derivations of the same `◯S` can differ in the clause applications
they make, and only there: the monad laws (`WM.bind_*`) identify everything
else.  The entries `(w, t̃, z)` a derivation summons fix its constraint
parametrically in the table, and inclusion of entries gives entailment for
*every* table — a preference between derivations that needs no domain. -/

/-- The witness of an abstract proof; it does not depend on the table. -/
def AProof.wit : AProof → Wit
  | .val => .unit
  | .andC p r => .pair p.wit r.wit
  | .orL p => .inl p.wit
  | .orR p => .inr p.wit
  | .exC t p => .pack t p.wit
  | .impC _ _ _ => .unit

/-- `π₂|a|` is `a.wit`, whatever the table. -/
theorem AProof.ext_snd (T : Nat → List Tm → Wit → Form) :
    ∀ a : AProof, (a.ext T).2 = a.wit
  | .val => rfl
  | .andC p r => by
      show Wit.pair (p.ext T).2 (r.ext T).2 = Wit.pair p.wit r.wit
      rw [AProof.ext_snd T p, AProof.ext_snd T r]
  | .orL p => by
      show Wit.inl (p.ext T).2 = Wit.inl p.wit
      rw [AProof.ext_snd T p]
  | .orR p => by
      show Wit.inr (p.ext T).2 = Wit.inr p.wit
      rw [AProof.ext_snd T p]
  | .exC t p => by
      show Wit.pack t (p.ext T).2 = Wit.pack t p.wit
      rw [AProof.ext_snd T p]
  | .impC _ _ _ => rfl

/-- The table entries a derivation summons: `(w, t̃, z)` at each clause application. -/
def AProof.entries : AProof → List (Nat × List Tm × Wit)
  | .val => []
  | .andC p r => p.entries ++ r.entries
  | .orL p => p.entries
  | .orR p => p.entries
  | .exC _ p => p.entries
  | .impC w ts p => p.entries ++ [(w, ts, p.wit)]

/-- Each summoned entry is entailed by the extracted constraint. -/
theorem AProof.prv_entry (T : Nat → List Tm → Wit → Form) :
    ∀ (a : AProof) (e : Nat × List Tm × Wit), e ∈ a.entries →
      Prv [(a.ext T).1] (T e.1 e.2.1 e.2.2)
  | .val, _, he => nomatch he
  | .andC p r, e, he => by
      have he' : e ∈ p.entries ++ r.entries := he
      show Prv [Form.and (p.ext T).1 (.and (r.ext T).1 .top)] _
      rcases List.mem_append.1 he' with h | h
      · exact Prv.cut1 (Prv.andE₁ Prv.hd) (AProof.prv_entry T p e h)
      · exact Prv.cut1 (Prv.andE₁ (Prv.andE₂ Prv.hd)) (AProof.prv_entry T r e h)
  | .orL p, e, he => by
      show Prv [Form.and (p.ext T).1 .top] _
      exact Prv.cut1 (Prv.andE₁ Prv.hd) (AProof.prv_entry T p e he)
  | .orR p, e, he => by
      show Prv [Form.and (p.ext T).1 .top] _
      exact Prv.cut1 (Prv.andE₁ Prv.hd) (AProof.prv_entry T p e he)
  | .exC _ p, e, he => by
      show Prv [Form.and (p.ext T).1 .top] _
      exact Prv.cut1 (Prv.andE₁ Prv.hd) (AProof.prv_entry T p e he)
  | .impC w ts p, e, he => by
      have he' : e ∈ p.entries ++ [(w, ts, p.wit)] := he
      show Prv [Form.and (p.ext T).1 (T w ts (p.ext T).2)] _
      rcases List.mem_append.1 he' with h | h
      · exact Prv.cut1 (Prv.andE₁ Prv.hd) (AProof.prv_entry T p e h)
      · rw [List.mem_singleton.1 h, AProof.ext_snd T p]
        exact Prv.andE₂ Prv.hd

/-- The extracted constraint follows from the summoned entries. -/
theorem AProof.prv_ext_of_entries (T : Nat → List Tm → Wit → Form) (Γ : List Form) :
    ∀ a : AProof, (∀ e ∈ a.entries, Prv Γ (T e.1 e.2.1 e.2.2)) → Prv Γ (a.ext T).1
  | .val, _ => Prv.topI
  | .andC p r, h => by
      have h' : ∀ e ∈ p.entries ++ r.entries, Prv Γ (T e.1 e.2.1 e.2.2) := h
      show Prv Γ (Form.and (p.ext T).1 (.and (r.ext T).1 .top))
      exact Prv.andI
        (AProof.prv_ext_of_entries T Γ p fun e he => h' e (List.mem_append_left _ he))
        (Prv.andI
          (AProof.prv_ext_of_entries T Γ r fun e he => h' e (List.mem_append_right _ he))
          Prv.topI)
  | .orL p, h => by
      show Prv Γ (Form.and (p.ext T).1 .top)
      exact Prv.andI (AProof.prv_ext_of_entries T Γ p h) Prv.topI
  | .orR p, h => by
      show Prv Γ (Form.and (p.ext T).1 .top)
      exact Prv.andI (AProof.prv_ext_of_entries T Γ p h) Prv.topI
  | .exC _ p, h => by
      show Prv Γ (Form.and (p.ext T).1 .top)
      exact Prv.andI (AProof.prv_ext_of_entries T Γ p h) Prv.topI
  | .impC w ts p, h => by
      have h' : ∀ e ∈ p.entries ++ [(w, ts, p.wit)], Prv Γ (T e.1 e.2.1 e.2.2) := h
      show Prv Γ (Form.and (p.ext T).1 (T w ts (p.ext T).2))
      rw [AProof.ext_snd T p]
      exact Prv.andI
        (AProof.prv_ext_of_entries T Γ p fun e he => h' e (List.mem_append_left _ he))
        (h' (w, ts, p.wit) (List.mem_append_right _ (List.mem_singleton.2 rfl)))

/-- **The inclusion lemma.**  If every entry `a` summons is summoned by `a'`, then
`a'`'s extracted constraint entails `a`'s, for every table. -/
theorem AProof.ext_prv_of_entries_subset (T : Nat → List Tm → Wit → Form) {a a' : AProof}
    (h : ∀ e ∈ a.entries, e ∈ a'.entries) : Prv [(a'.ext T).1] (a.ext T).1 :=
  AProof.prv_ext_of_entries T _ a fun e he => AProof.prv_entry T a' e (h e he)

/-- Derivations summoning the same entries extract the same constraint, up to `⊣⊢`. -/
theorem AProof.ext_peq_of_entries_eq (T : Nat → List Tm → Wit → Form) {a a' : AProof}
    (h : ∀ e, e ∈ a.entries ↔ e ∈ a'.entries) : PEq (a.ext T).1 (a'.ext T).1 :=
  ⟨AProof.ext_prv_of_entries_subset T fun e he => (h e).2 he,
   AProof.ext_prv_of_entries_subset T fun e he => (h e).1 he⟩

/-! ## `◯` over a conjunction: interderivable, but not the same realisers

`◯(A ∧ B) ⊣⊢ ◯A ∧ ◯B` in QLL.  Under extraction the two sides have different
types, `C × (|A| × |B|)` against `(C × |A|) × (C × |B|)`: on the left one
constraint may relate both witnesses, on the right each constraint sees only
its own.  The two directions of the equivalence are the double strength
`dstr` and the duplication `dup`, and `dup ∘ dstr` is not the identity, so a
clause body cannot be regrouped this way without changing what is extracted.
In Fig. 3 as built here, `∧◯` is `dstr` (`AProof.ext_andC`): a constraint
relating two subgoals' witnesses can live only in the table entry of the
enclosing clause. -/

/-- `◯(A ∧ B) ⊢ ◯A ∧ ◯B`. -/
theorem circ_and_split (q : Q) (A B : Form) :
    Prv [.circ q (.and A B)] (.and (.circ q A) (.circ q B)) :=
  Prv.andI (Prv.circE Prv.hd (Prv.circI (Prv.andE₁ Prv.hd)))
    (Prv.circE Prv.hd (Prv.circI (Prv.andE₂ Prv.hd)))

/-- `◯A ∧ ◯B ⊢ ◯(A ∧ B)`. -/
theorem circ_and_join (q : Q) (A B : Form) :
    Prv [.and (.circ q A) (.circ q B)] (.circ q (.and A B)) :=
  Prv.circE (Prv.andE₁ Prv.hd)
    (Prv.circE (Prv.andE₂ (Prv.var (List.Mem.tail _ (List.Mem.head _))))
      (Prv.circI (Prv.andI (Prv.var (List.Mem.tail _ (List.Mem.head _))) Prv.hd)))

/-- The double strength: two independent computations combined. -/
def dstr {α β : Type} (m : WM α × WM β) : WM (α × β) := (.and m.1.1 m.2.1, (m.1.2, m.2.2))

/-- Duplication: one joint constraint handed to both components. -/
def dup {α β : Type} (m : WM (α × β)) : WM α × WM β := ((m.1, m.2.1), (m.1, m.2.2))

/-- `dstr ∘ dup` is the identity up to `⊣⊢`. -/
theorem dstr_dup {α β : Type} (m : WM (α × β)) : WEq (dstr (dup m)) m :=
  ⟨⟨Prv.andE₁ Prv.hd, Prv.andI Prv.hd Prv.hd⟩, rfl⟩

/-- `dup ∘ dstr` is not: the first component of `((⊤, ⋆), (⊥, ⋆))` comes back as `(⊤ ∧ ⊥, ⋆)`. -/
theorem not_dup_dstr :
    ¬ WEq (dup (dstr ((Form.top, Wit.unit), (Form.bot, Wit.unit)))).1 (Form.top, Wit.unit) := by
  intro h
  have hb : Prv [Form.top] Form.bot := Prv.andE₂ h.1.2
  have hs := Prv.sound hb BodyCirc.m2 BodyCirc.W2.w0 (fun _ => ()) (fun _ _ => trivial)
    (fun B hB => by rcases List.mem_singleton.1 hB with rfl; trivial)
  exact hs

/-- Fig. 3's `∧◯` is the double strength: the second constraint does not see the first witness. -/
theorem AProof.ext_andC (T : Nat → List Tm → Wit → Form) (p r : AProof) :
    (AProof.andC p r).ext T = (.and (p.ext T).1 (.and (r.ext T).1 .top), .pair (p.ext T).2 (r.ext T).2) :=
  rfl

/-! ## Decorating a disjunct: `A ∨ ◯B`

A goal may be a disjunction with the modality on one disjunct only: "either `A`
outright, or `B` up to a constraint".  Under an outer `◯` the decoration
collapses (`circ_or_circ_collapse`, `circ_or_circ_expand`); as a plain goal
`A ∨ ◯B` is strictly weaker than `A ∨ B` (`or_to_or_circ`, and the REFUTED
converse in `BodyCirc`).  Under extraction a disjunction is a sum with each
branch's constraint inside its injection (`AProof.ext_orL`), so a branch whose
summoned entries all have table value `⊤` extracts `⊤`
(`AProof.ext_top_of_pure`), which every other answer of the goal entails
(`AProof.once_of_pure`): a sound `once`. -/

/-- `◯(A ∨ ◯B) ⊢ ◯(A ∨ B)`. -/
theorem circ_or_circ_collapse (q : Q) (A B : Form) :
    Prv [.circ q (.or A (.circ q B))] (.circ q (.or A B)) :=
  Prv.circE Prv.hd (Prv.orE Prv.hd (Prv.circI (Prv.orI₁ Prv.hd))
    (Prv.circE Prv.hd (Prv.circI (Prv.orI₂ Prv.hd))))

/-- `◯(A ∨ B) ⊢ ◯(A ∨ ◯B)`: under `◯` the decoration is invisible. -/
theorem circ_or_circ_expand (q : Q) (A B : Form) :
    Prv [.circ q (.or A B)] (.circ q (.or A (.circ q B))) :=
  Prv.circE Prv.hd
    (Prv.circI (Prv.orE Prv.hd (Prv.orI₁ Prv.hd) (Prv.orI₂ (Prv.circI Prv.hd))))

/-- `A ∨ B ⊢ A ∨ ◯B`: as a plain goal the decorated form is weaker. -/
theorem or_to_or_circ (q : Q) (A B : Form) : Prv [.or A B] (.or A (.circ q B)) :=
  Prv.orE Prv.hd (Prv.orI₁ Prv.hd) (Prv.orI₂ (Prv.circI Prv.hd))

/-- `∨◯` is a sum: the branch's constraint travels with the injection. -/
theorem AProof.ext_orL (T : Nat → List Tm → Wit → Form) (p : AProof) :
    (AProof.orL p).ext T = (.and (p.ext T).1 .top, .inl (p.ext T).2) := rfl

theorem AProof.ext_orR (T : Nat → List Tm → Wit → Form) (p : AProof) :
    (AProof.orR p).ext T = (.and (p.ext T).1 .top, .inr (p.ext T).2) := rfl

/-- A derivation whose summoned entries all have table value `⊤` extracts `⊤`. -/
theorem AProof.ext_top_of_pure (T : Nat → List Tm → Wit → Form) (a : AProof)
    (h : ∀ e ∈ a.entries, PEq (T e.1 e.2.1 e.2.2) .top) : PEq (a.ext T).1 .top :=
  ⟨Prv.topI, AProof.prv_ext_of_entries T [.top] a fun e he => (h e he).2⟩

/-- **A sound `once`.**  Every other derivation's answer entails such a derivation's. -/
theorem AProof.once_of_pure (T : Nat → List Tm → Wit → Form) {a a' : AProof}
    (h : ∀ e ∈ a.entries, PEq (T e.1 e.2.1 e.2.2) .top) :
    Prv [(a'.ext T).1] (a.ext T).1 :=
  Prv.cut1 Prv.topI (AProof.ext_top_of_pure T a h).2

end LaxLogic.QLL

namespace LaxLogic.QLL.BodyCirc

open LaxLogic.QLL LaxLogic.QLL.Engine LaxLogic.QLL.LinQ LaxLogic.QLL.CLPExamples

-- The entries the example's derivation summons: `θ₂` at `z`, `θ₁` at `z`, `θ₀` at `_v0`.
/-- info: [(0, ["_v0"]), (1, ["z"]), (2, ["z"])] -/
#guard_msgs in #eval proofQ.toA.entries.map fun e => (e.1, e.2.1.map Engine.showTm)
/-- info: 'LaxLogic.QLL.AProof.ext_prv_of_entries_subset' depends on axioms: [propext] -/
#guard_msgs in #print axioms AProof.ext_prv_of_entries_subset

/-! ## Decorating a disjunct, concretely -/

/-- REFUTED: `P ∨ ◯B ⊬ P ∨ B`; in the two-world model the lax branch is the only one open. -/
theorem not_prv_or_circ_to_or :
    ¬ Prv [.or (.pred "P" []) (.circ .ex (.pred "B" []))]
        (.or (.pred "P" []) (.pred "B" [])) := by
  intro h
  have hyp : ∀ C ∈ [Form.or (.pred "P" []) (.circ .ex (.pred "B" []))],
      m2.force C W2.w0 (fun _ => ()) [] := by
    intro C hC
    rcases List.mem_singleton.1 hC with rfl
    refine Or.inr ?_
    intro v _
    cases v with
    | w0 => exact ⟨W2.w1, rfl, Or.inr trivial⟩
    | w1 => exact ⟨W2.w1, rfl, Or.inr trivial⟩
  have hs := Prv.sound h m2 W2.w0 (fun _ => ()) (fun _ _ => trivial) hyp
  rcases hs with h' | h'
  · rcases h' with h'' | h''
    · exact h''.elim
    · have hp : ("P" : String) = "A" := h''
      exact absurd hp (by decide)
  · rcases h' with h'' | h''
    · exact h''.elim
    · have hb : ("B" : String) = "A" := h''
      exact absurd hb (by decide)

/-- `Q(t) ⊂ R(t) ∨ ∃s. B(s) ∧ t ≥ s + 2`, with `R` constraint-free. -/
def exD : Program :=
  [ cl "R" ["t"] (conj []),
    cl "B" ["s"] (geq (v "s") (num "5")),
    cl "Q" ["t"] (.or (at_ "R" [v "t"])
      (exs ["s"] (conj [at_ "B" [v "s"], geq (v "t") (plus (v "s") (num "2"))]))) ]

def goalD : Form := query (at_ "Q" [v "z"])

def proofD : CProof := ((runL exD isLinC false 20 goalD).map (·.1)).getD .top

theorem checkD : checkC isLinC exD goalD proofD = true := by decide +kernel

theorem headsD : exD.HeadsOK isLinC := by unfold Program.HeadsOK; decide

/-- Both branches: the free one answers `⊤`, the other carries `B`'s constraint. -/
theorem allD_len : (proveAll exD isLinC false 20 goalD ⟨[], 0⟩).length = 2 := by
  decide +kernel

/-- info: ["true", "(geq(_v0, 5) ∧ geq(z, add(_v0, 2)))"] -/
#guard_msgs in #eval (proveAll exD isLinC false 20 goalD ⟨[], 0⟩).map fun r => showForm r.1.total

theorem totalD : proofD.total = .top := by decide +kernel

/-- The free branch extracts `⊤` under the `◯` pass. -/
theorem extD_top : PEq (proofD.toA.ext (exD.table isLinC)).1 .top :=
  let h := checkC_sound isLinC exD proofD goalD checkD
  have e : PEq (proofD.toA.ext (exD.table isLinC)).1 proofD.total :=
    ((PEq.and_top _).symm.trans (PEq.and (PEq.refl _) (h.active_pure (by decide)).symm)).trans
      (h.ext_total headsD)
  totalD ▸ e

/-- The sound `once`, on this program: every other derivation's answer entails the free
branch's. -/
theorem onceD (a' : AProof) :
    Prv [(a'.ext (exD.table isLinC)).1] (proofD.toA.ext (exD.table isLinC)).1 :=
  Prv.cut1 Prv.topI extD_top.2

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.BodyCirc.circ_circ_iff' does not depend on any axioms -/
#guard_msgs in #print axioms circ_circ_iff

/-- info: 'LaxLogic.QLL.BodyCirc.clause4' does not depend on any axioms -/
#guard_msgs in #print axioms clause4

/-- info: 'LaxLogic.QLL.BodyCirc.not_prv_plain_to_body_circ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms not_prv_plain_to_body_circ

/-- info: 'LaxLogic.QLL.BodyCirc.fo_II_to_I' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fo_II_to_I

/-- info: 'LaxLogic.QLL.AProof.once_of_pure' depends on axioms: [propext] -/
#guard_msgs in #print axioms AProof.once_of_pure

/-- info: 'LaxLogic.QLL.BodyCirc.not_prv_or_circ_to_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms not_prv_or_circ_to_or

/--
info: 'LaxLogic.QLL.BodyCirc.extD_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms extD_top

/-- info: 'LaxLogic.QLL.BodyCirc.fo_ex_II_to_I' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fo_ex_II_to_I

/-- info: 'LaxLogic.QLL.BodyCirc.extQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extQ

end LaxLogic.QLL.BodyCirc
