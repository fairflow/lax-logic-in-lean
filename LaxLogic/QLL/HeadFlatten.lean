/-
# `LaxLogic.QLL.HeadFlatten` — variable-only heads lose nothing, given equality

Def 5.1 restricts clause heads to `P(x₁,…,xₘ)` with distinct variables, so
resolution is matching (`Form.instAll`), never unification.  A clause with a
constructor in its head is recovered by *flattening*, the first step of Clark's
completed definition (1978):

    ∀y. S y ⊃ P(f y)      ⇝      ∀x. (∃y. x = f y ∧ S y) ⊃ P x

The two are interderivable given the equality axioms a constraint theory
supplies, and nothing else: one direction needs reflexivity, the other
substitutivity in `P`.

    flat,  ∀x. x = x                     ⊢  orig                 (`flat_to_orig`)
    orig,  ∀x y. x = y ⊃ P y ⊃ P x       ⊢  flat                 (`orig_to_flat`)

The same two axioms suffice when the head is `◯P(f y)`: substitutivity lifts
through `◯` by `◯E` (`flat_to_orig_circ`, `orig_to_flat_circ`).  So the fact
is native to the ◯-free fragment and unchanged by `◯`.  What the constraint
framework contributes is that `=` is a *constraint*, solved in the domain
(Clark's equality theory over the Herbrand universe), rather than an
algorithm wired into resolution.  This development has no such solver — `eq`
is read as linear arithmetic over ℚ only — so constructor heads are
logically available here and computationally not.
-/
import LaxLogic.QLL.ProvFresh
import LaxLogic.QLL.CLPOper

namespace LaxLogic.QLL.HeadFlatten

/-- `∀y. S y ⊃ P(f y)`: a constructor in the head. -/
def orig : Form :=
  .forall_ (.imp (.pred "S" [.bvar 0]) (.pred "P" [.fn "f" [.bvar 0]]))

/-- `∀x. (∃y. eq(x, f y) ∧ S y) ⊃ P x`: its flattening. -/
def flat : Form :=
  .forall_ (.imp (.exists_ (.and (.pred "eq" [.bvar 1, .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])))
    (.pred "P" [.bvar 0]))

/-- `∀x. eq(x, x)`. -/
def eqRefl : Form := .forall_ (.pred "eq" [.bvar 0, .bvar 0])

/-- `∀x y. eq(x, y) ⊃ P y ⊃ P x`. -/
def eqSubst : Form :=
  .forall_ (.forall_ (.imp (.pred "eq" [.bvar 1, .bvar 0])
    (.imp (.pred "P" [.bvar 0]) (.pred "P" [.bvar 1]))))

theorem lc_fw : Tm.lcAt 0 (.fn "f" [.fvar "w"]) := ⟨trivial, trivial⟩
theorem lc_fu : Tm.lcAt 0 (.fn "f" [.fvar "u"]) := ⟨trivial, trivial⟩

/-! ## The ◯-free fragment -/

/-- Flattened plus reflexivity gives the constructor-headed clause. -/
theorem flat_to_orig : Prv [flat, eqRefl] orig := by
  refine Prv.allI_of_fresh (c := "w") (by decide) (by decide) ?_
  show Prv [flat, eqRefl] (.imp (.pred "S" [.fvar "w"]) (.pred "P" [.fn "f" [.fvar "w"]]))
  refine Prv.impI ?_
  have hfl : Prv [Form.pred "S" [.fvar "w"], flat, eqRefl]
      (.imp (.exists_ (.and (.pred "eq" [.fn "f" [.fvar "w"], .fn "f" [.bvar 0]])
        (.pred "S" [.bvar 0]))) (.pred "P" [.fn "f" [.fvar "w"]])) :=
    Prv.allE (.fn "f" [.fvar "w"]) lc_fw (Prv.var (List.Mem.tail _ (List.Mem.head _)))
  have hrefl : Prv [Form.pred "S" [.fvar "w"], flat, eqRefl]
      (.pred "eq" [.fn "f" [.fvar "w"], .fn "f" [.fvar "w"]]) :=
    Prv.allE (.fn "f" [.fvar "w"]) lc_fw
      (Prv.var (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hS : Prv [Form.pred "S" [.fvar "w"], flat, eqRefl] (.pred "S" [.fvar "w"]) :=
    Prv.var (List.Mem.head _)
  exact Prv.impE hfl (Prv.exI (.fvar "w") trivial (Prv.andI hrefl hS))

/-- Constructor-headed plus substitutivity gives the flattened clause. -/
theorem orig_to_flat : Prv [orig, eqSubst] flat := by
  refine Prv.allI_of_fresh (c := "w") (by decide) (by decide) ?_
  show Prv [orig, eqSubst]
    (.imp (.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])))
      (.pred "P" [.fvar "w"]))
  refine Prv.impI ?_
  refine Prv.exE_of_fresh (c := "u") (by decide) (by decide) (by decide)
    (Prv.var (List.Mem.head _)) ?_
  have h : Prv [Form.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"]),
      Form.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])),
      orig, eqSubst]
      (.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"])) :=
    Prv.var (List.Mem.head _)
  have horig : Prv [Form.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"]),
      Form.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])),
      orig, eqSubst]
      (.imp (.pred "S" [.fvar "u"]) (.pred "P" [.fn "f" [.fvar "u"]])) :=
    Prv.allE (.fvar "u") trivial
      (Prv.var (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hsub1 : Prv [Form.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"]),
      Form.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])),
      orig, eqSubst]
      (.forall_ (.imp (.pred "eq" [.fvar "w", .bvar 0])
        (.imp (.pred "P" [.bvar 0]) (.pred "P" [.fvar "w"])))) :=
    Prv.allE (.fvar "w") trivial
      (Prv.var (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  have hsub : Prv [Form.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"]),
      Form.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])),
      orig, eqSubst]
      (.imp (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]])
        (.imp (.pred "P" [.fn "f" [.fvar "u"]]) (.pred "P" [.fvar "w"]))) :=
    Prv.allE (.fn "f" [.fvar "u"]) lc_fu hsub1
  exact Prv.impE (Prv.impE hsub (Prv.andE₁ h)) (Prv.impE horig (Prv.andE₂ h))

/-! ## The same with a modal head, and the same two axioms -/

/-- `∀y. S y ⊃ ◯P(f y)`. -/
def origC (q : Q) : Form :=
  .forall_ (.imp (.pred "S" [.bvar 0]) (.circ q (.pred "P" [.fn "f" [.bvar 0]])))

/-- `∀x. (∃y. eq(x, f y) ∧ S y) ⊃ ◯P x`. -/
def flatC (q : Q) : Form :=
  .forall_ (.imp (.exists_ (.and (.pred "eq" [.bvar 1, .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])))
    (.circ q (.pred "P" [.bvar 0])))

theorem flat_to_orig_circ (q : Q) : Prv [flatC q, eqRefl] (origC q) := by
  refine Prv.allI_of_fresh (c := "w") (by cases q <;> decide) (by cases q <;> decide) ?_
  show Prv [flatC q, eqRefl]
    (.imp (.pred "S" [.fvar "w"]) (.circ q (.pred "P" [.fn "f" [.fvar "w"]])))
  refine Prv.impI ?_
  have hfl : Prv [Form.pred "S" [.fvar "w"], flatC q, eqRefl]
      (.imp (.exists_ (.and (.pred "eq" [.fn "f" [.fvar "w"], .fn "f" [.bvar 0]])
        (.pred "S" [.bvar 0]))) (.circ q (.pred "P" [.fn "f" [.fvar "w"]]))) :=
    Prv.allE (.fn "f" [.fvar "w"]) lc_fw (Prv.var (List.Mem.tail _ (List.Mem.head _)))
  have hrefl : Prv [Form.pred "S" [.fvar "w"], flatC q, eqRefl]
      (.pred "eq" [.fn "f" [.fvar "w"], .fn "f" [.fvar "w"]]) :=
    Prv.allE (.fn "f" [.fvar "w"]) lc_fw
      (Prv.var (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hS : Prv [Form.pred "S" [.fvar "w"], flatC q, eqRefl] (.pred "S" [.fvar "w"]) :=
    Prv.var (List.Mem.head _)
  exact Prv.impE hfl (Prv.exI (.fvar "w") trivial (Prv.andI hrefl hS))

/-- Substitutivity lifts through `◯` by `◯E`; no modal equality axiom is needed. -/
theorem orig_to_flat_circ (q : Q) : Prv [origC q, eqSubst] (flatC q) := by
  refine Prv.allI_of_fresh (c := "w") (by cases q <;> decide) (by cases q <;> decide) ?_
  show Prv [origC q, eqSubst]
    (.imp (.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])))
      (.circ q (.pred "P" [.fvar "w"])))
  refine Prv.impI ?_
  refine Prv.exE_of_fresh (c := "u") (by cases q <;> decide) (by cases q <;> decide)
    (by cases q <;> decide) (Prv.var (List.Mem.head _)) ?_
  have h : Prv [Form.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"]),
      Form.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])),
      origC q, eqSubst]
      (.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"])) :=
    Prv.var (List.Mem.head _)
  have horig : Prv [Form.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"]),
      Form.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])),
      origC q, eqSubst]
      (.imp (.pred "S" [.fvar "u"]) (.circ q (.pred "P" [.fn "f" [.fvar "u"]]))) :=
    Prv.allE (.fvar "u") trivial
      (Prv.var (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hsub1 : Prv [Form.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"]),
      Form.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])),
      origC q, eqSubst]
      (.forall_ (.imp (.pred "eq" [.fvar "w", .bvar 0])
        (.imp (.pred "P" [.bvar 0]) (.pred "P" [.fvar "w"])))) :=
    Prv.allE (.fvar "w") trivial
      (Prv.var (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  have hsub : Prv [Form.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"]),
      Form.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])),
      origC q, eqSubst]
      (.imp (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]])
        (.imp (.pred "P" [.fn "f" [.fvar "u"]]) (.pred "P" [.fvar "w"]))) :=
    Prv.allE (.fn "f" [.fvar "u"]) lc_fu hsub1
  have hPf : Prv [Form.and (.pred "eq" [.fvar "w", .fn "f" [.fvar "u"]]) (.pred "S" [.fvar "u"]),
      Form.exists_ (.and (.pred "eq" [.fvar "w", .fn "f" [.bvar 0]]) (.pred "S" [.bvar 0])),
      origC q, eqSubst]
      (.circ q (.pred "P" [.fn "f" [.fvar "u"]])) :=
    Prv.impE horig (Prv.andE₂ h)
  refine Prv.circE hPf ?_
  exact Prv.circI (Prv.impE (Prv.impE hsub.weaken_cons (Prv.andE₁ h.weaken_cons))
    (Prv.var (List.Mem.head _)))

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.HeadFlatten.flat_to_orig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms flat_to_orig

/-- info: 'LaxLogic.QLL.HeadFlatten.orig_to_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms orig_to_flat

/-- info: 'LaxLogic.QLL.HeadFlatten.flat_to_orig_circ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms flat_to_orig_circ

/-- info: 'LaxLogic.QLL.HeadFlatten.orig_to_flat_circ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms orig_to_flat_circ

end LaxLogic.QLL.HeadFlatten
