/-
T3 — THE CERTIFICATE FORMAT: a refutation as decidable data.

The thread's goal statement asks for a refutation that is "a finite
syntactic object, built forwards by rules, checkable by a DECIDABLE
rule-application predicate".  T1 gave the rules, T2 proved they are
enough.  This file supplies the third thing: a `Bool`-valued predicate
that decides whether a piece of finite data IS a construction of the
calculus, so that "REFUTED" is a `decide` and not a hand-built term.

Two layers, deliberately separate:

* **`BuiltB`** — decides membership of the class `solo`/`join`
  generate.  Unfolded (`Reject/Complete.lean` §1) that class is the
  finite `Rᵢ`-TREES with fallible worlds only at leaves, so `BuiltB`
  tests exactly: rooted, `Rᵢ`-antisymmetric, every world's set of
  `Rᵢ`-predecessors a chain, and no fallible world with a strict
  successor.
* **`certifies`** — the whole check: well-formed frame, in the built
  class, root forces `Γ`, root refutes `C`.  Soundness rides on the
  repo's existing bridge `FinCM.not_provable_of_check`, so nothing new
  has to be trusted.

The split matters.  Soundness of a certificate does NOT need
`BuiltB` — `checkB` alone certifies underivability for ANY finite
model.  `BuiltB` says the certificate is in CANONICAL FORM — it is a property
of the object, not a record of how the object was obtained.  It is what
a searcher should range over, because T2 (`gen_of_reduced`) says
completeness lives in that class and nowhere smaller.

**Not a derivation, and the distinction is not pedantic.**  A
derivation is indexed by what it derives and records which rule fired
where, which is what buys the proof-theoretic payoffs — subformula
property, cut admissibility, interpolation.  A model plus a decidable
class predicate gives induction on the MODEL (`height_induction`, which
is exactly what T2 uses) but no sequent to state lemmas about and no
derivation to induct on.  The clean evidence is `not_laxND_of_check_any`
below: ONE object settles MANY sequents, one per world.  A derivation
cannot do that — it derives one thing.  That asymmetry is the signature
of a countermodel, and it is precisely why the sharing in T3's searcher
pays.  What this file supplies is therefore *canonical-form
countermodels, checkable by a decidable predicate*; a genuine calculus
would need FRJ's sequent syntax and derivations as an inductive type
over it, at which point T1/T2 become its adequacy proof.
-/
import Reject.Complete
import LaxLogic.PLLCountermodelEmit

namespace Reject

open PLLND PLLND.FinCM

/-! ## 1. Deciding the built class -/

/-- World 0 is `Rᵢ`-below everything: the model has a ROOT. -/
def rootedB (M : FinCM) : Bool := (List.range M.n).all fun w => M.riB 0 w

/-- `Rᵢ` is antisymmetric — `Reduced`, decidably. -/
def reducedB (M : FinCM) : Bool :=
  (List.range M.n).all fun x => (List.range M.n).all fun y =>
    !(M.riB x y && M.riB y x) || decide (x = y)

/-- Every world's set of `Rᵢ`-predecessors is a chain: the frame is a
TREE, not merely a poset. -/
def treeB (M : FinCM) : Bool :=
  (List.range M.n).all fun w => (List.range M.n).all fun x =>
    (List.range M.n).all fun y =>
      !(M.riB x w && M.riB y w) || M.riB x y || M.riB y x

/-- Fallible worlds have no strict `Rᵢ`-successor.  `join` sets its new
root's `F` to `False` unconditionally, so in a construction
fallibility can only ever be introduced by `solo`, at a leaf. -/
def falLeavesB (M : FinCM) : Bool :=
  (List.range M.n).all fun w =>
    !(M.fallB w) ||
      (List.range M.n).all fun v => !(M.riB w v) || decide (v = w)

/-- **The built class, decidably.** -/
def BuiltB (M : FinCM) : Bool :=
  M.wellB && rootedB M && reducedB M && treeB M && falLeavesB M

/-! ## 2. The certificate -/

/-- **A refutation certificate**: finite data whose validity is a
`Bool`.  `certifies M w Γ C` says `M` is a construction of the
calculus and its world `w` forces `Γ` and refutes `C`. -/
def certifies (M : FinCM) (w : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    Bool :=
  BuiltB M && checkB M w Γ C

/-- **Soundness of the certificate format** — the whole point: a
`Bool` that decides underivability. -/
theorem not_laxND_of_certifies {M : FinCM} {w : Nat}
    {Γ : List PLLFormula} {C : PLLFormula} (h : certifies M w Γ C = true) :
    Γ ⊬ C :=
  not_provable_of_check (by
    simp only [certifies, Bool.and_eq_true] at h
    exact h.2)

/-- The certificate is sound at ANY world, not only the root — which
is what makes MINING a derivation worthwhile: one certificate settles
one underivability per world, not one per certificate. -/
theorem not_laxND_of_check_any {M : FinCM} (w : Nat)
    {Γ : List PLLFormula} {C : PLLFormula} (h : checkB M w Γ C = true) :
    Γ ⊬ C :=
  not_provable_of_check h

/-! ## 3. Pins -/

/--
info: 'Reject.not_laxND_of_certifies' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_laxND_of_certifies

/--
info: 'Reject.not_laxND_of_check_any' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_laxND_of_check_any

end Reject
