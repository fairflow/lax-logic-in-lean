/-
# `LaxLogic.QLL` — a deep embedding of the abstract logic of TPHOLs 2001

`LaxLogic.Obligation` renders the paper *shallowly*: a refinement pair is a
Lean proposition and its proof is a Lean proof.  This library renders the same
paper *deeply*: a formula is a tree, a proof is a tree, and whether the second
proves the first is to be decided by a program rather than discharged by a
tactic.
-/
import LaxLogic.QLL.Syntax
import LaxLogic.QLL.Deriv
