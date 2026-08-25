/-
# The RN(◯,{}) dictionary database — the type layer

What went wrong in round 1 was not arithmetic.  `wip/rnDict.lean` states
323 cell theorems of which 87 are `theorem foo : Interd a b := sorry`.
A `sorry` **asserts**: it produces an inhabitant of the type, so a
sorried cell can be applied, cited and depended on exactly as a proved
one can, and is distinguishable from a proof only by reading its body or
its axioms.  "Still to be determined" and "asserted without proof" thus
became the same object, and every tally taken over that record was void.

The second fault was subtler and is the one this file is shaped around:

> **Status is not a property of a cell.  It is a property of a
> (cell, representative set, engine) triple.**

`Rewrite/Catalogue.lean` records `cAnd_8_10`, `cImp_9_4`, `cImp_12_4`
and `cImp_14_4` as REFUTED.  What is refuted is their round-1
*statement*, a collapse to `q0`, asked against the fifteen
representatives `q0 … q14`.  Against the sixteen that include
`q15 = q9 ⊃ q4` all four are PROVED — they are exactly the four §40
witnesses `w1 … w4` of `wip/rnSepColl.lean`.  Neither verdict is wrong;
they answer different questions.  A record that stores only "REFUTED"
against the cell has thrown away the half of the question that decides
which.

## What the types do about it

* `Claim` carries the `scope` — the representative set the question was
  asked against — and `Claim.wellScoped` makes it MANDATORY on a
  negative claim.  A negative claim without a scope is not a false
  claim; it is not a claim at all.
* `Entry.ok : ev.Certifies claim` is a proof field.  There is no
  constructor of `Entry` that omits it, so an unproved entry is
  *unwritable*, not merely discouraged.  The pattern is `Rewrite.RwRule`
  and its `ok : Interd lhs rhs` field (`Rewrite/Core.lean`), which is
  what makes `norm_interd` unconditional.
* `Frontier` is `List Claim` and nothing else.  An UNSETTLED question
  gets no declaration of its own: it is a piece of data describing a
  question, and constructing it asserts nothing whatsoever.  There is
  deliberately no `Entry`-like structure with a `status` field, because
  a status field is how "open" and "asserted" become the same shape
  again.

## Discipline in force in this file

Zero `sorry`.  A statement that is not proved is written as
`def name : Prop := …`, which names it without asserting it — the
pattern of `FRJO/Core.lean` and `Certified/Register.lean`.  Every
definition that a later layer will cite carries a `#guard_msgs`-checked
`#print axioms` at the foot of the file.

## Where this sits

Layer 1 is `Certified/Register.lean` (the theorems the database may
cite, each re-pinned).  Layer 2 is `tools/` (the engines).  This is the
type layer of layer 3.  The arrow runs upward only: nothing here may be
imported by layer 1 or 2.

## What the types do NOT do — the residual hole, measured

`Entry.ok` makes an entry unwritable unless its claim is PROVED.  It
does not make an entry unwritable unless its claim is proved *without
`sorry`*, because a `sorry` inhabits its type: an `ok` field discharged
by a sorried theorem typechecks.  This was tested, not assumed.  Three
attempts, run against this module:

1. a negative entry with `scope := none` — REJECTED, `wellScoped`
   unprovable (`… .scope.isSome = true` has no `rfl`);
2. `Evidence.proof` offered for a negative claim — REJECTED,
   `decide` reports `Rel.nle.IsPositive` false;
3. `ok := cAnd_4_14`, one of the 87 sorried cells of `wip/rnDict.lean` —
   **ACCEPTED**, and `#print axioms` on it reads
   `depends on axioms: [sorryAx]`.

So the type layer closes the *scope* fault and the *evidence/claim
mismatch* fault by construction, and the *sorry* fault only in
combination with a `#guard_msgs`-checked `#print axioms`.  Attempt 3 is
caught by the pin and by nothing else.  Every entry admitted to the
database must therefore be pinned; that is a rule about the database,
enforceable only at the point where entries are added, and it is the one
obligation this file cannot discharge on the reader's behalf.

## A note on the imports

The worked examples, which cite `wip/rnSep.lean` and `wip/rnSepColl.lean`
(and through them the sorried `wip/rnDict.lean`), moved to
`RNDB/Examples.lean` on 2026-08-24 so that THIS module — the schema every
entry file imports — is `wip`-free.  The schema needs only the shared
representatives and the `Deriv`/`Interd` definitions.
-/
import LaxLogic.RN.Reps
import LaxLogic.Interd

namespace RNDB

open PLLFormula
open PLLND
open PLLND.SemUI

/-! ## 1. Relations

Three relations, and no fourth.  In particular there is no `unknown`
constructor: an unsettled question is not a relation between two
formulas, it is an absent entry.  Its home is `Frontier`. -/

/-- The relation a claim asserts between its two formulas. -/
inductive Rel where
  /-- `lhs ⊢ rhs` — one-directional entailment. -/
  | le
  /-- `lhs ⊣⊢ rhs` — interderivability, both directions. -/
  | interd
  /-- `lhs ⊬ rhs` — the entailment FAILS.  This is the negative
  direction, and the only one that needs a scope: see `Claim.scope`. -/
  | nle
  deriving DecidableEq, Repr, Inhabited

/-- The two positive relations. -/
def Rel.IsPositive (r : Rel) : Prop := r ≠ Rel.nle

instance : DecidablePred Rel.IsPositive := fun r =>
  inferInstanceAs (Decidable (r ≠ Rel.nle))

/-! ## 2. Claims

A `Claim` is DATA: a description of a question together with the answer
it proposes.  Writing one down asserts nothing.  `Claim.Holds` says what
it would take for the proposed answer to be right; only `Entry` demands
a proof of it. -/

/-- A proposed fact about two closed formulas, together with the
representative set the question was asked against.

`scope = some R` records that the question was posed relative to the
representative set `R`.  For a NEGATIVE claim this is not decoration:
`w1 ⊬ q0` asked against `q0 … q14` and asked against `q0 … q15` are
different questions with different answers, and a record that keeps only
the answer cannot tell you which was asked.  `Claim.wellScoped` requires
it.  On a positive claim the scope is optional, because `⊢` and `⊣⊢` are
absolute: a derivation does not stop being a derivation when the
representative set grows. -/
structure Claim where
  /-- The formula on the left of the relation. -/
  lhs : PLLFormula
  /-- The formula on the right of the relation. -/
  rhs : PLLFormula
  /-- Which relation is claimed. -/
  rel : Rel
  /-- The representative set the question was asked against.  Mandatory
  on a negative claim (`Claim.wellScoped`). -/
  scope : Option (List PLLFormula)
  deriving DecidableEq, Repr, Inhabited

/-- What the claim asserts. -/
def Claim.Holds (c : Claim) : Prop :=
  match c.rel with
  | Rel.le => Deriv [c.lhs] c.rhs
  | Rel.interd => Interd c.lhs c.rhs
  | Rel.nle => ¬ Deriv [c.lhs] c.rhs

@[simp] theorem Claim.Holds_le (φ ψ : PLLFormula) (s : Option (List PLLFormula)) :
    Claim.Holds ⟨φ, ψ, Rel.le, s⟩ = Deriv [φ] ψ := rfl

@[simp] theorem Claim.Holds_interd (φ ψ : PLLFormula) (s : Option (List PLLFormula)) :
    Claim.Holds ⟨φ, ψ, Rel.interd, s⟩ = Interd φ ψ := rfl

@[simp] theorem Claim.Holds_nle (φ ψ : PLLFormula) (s : Option (List PLLFormula)) :
    Claim.Holds ⟨φ, ψ, Rel.nle, s⟩ = ¬ Deriv [φ] ψ := rfl

/-! ### The scope obligation -/

/-- **A negative claim must carry its scope.**  `wellScoped` is the one
side condition every entry discharges (`Evidence.Certifies` demands it
in every case), so a scopeless negative entry is unwritable. -/
def Claim.wellScoped (c : Claim) : Prop :=
  c.rel = Rel.nle → c.scope.isSome = true

/-- The Boolean form, for deciding `wellScoped`. -/
def Claim.wellScopedB (c : Claim) : Bool :=
  !decide (c.rel = Rel.nle) || c.scope.isSome

theorem Claim.wellScoped_iff (c : Claim) : c.wellScoped ↔ c.wellScopedB = true := by
  obtain ⟨l, r, rel, sc⟩ := c
  cases rel <;> cases sc <;>
    simp [Claim.wellScoped, Claim.wellScopedB]

instance : DecidablePred Claim.wellScoped := fun c =>
  decidable_of_iff _ (c.wellScoped_iff).symm

/-- A positive claim is well scoped however its scope field is filled. -/
theorem Claim.wellScoped_of_pos {c : Claim} (h : c.rel.IsPositive) : c.wellScoped :=
  fun h' => absurd h' h

/-- A claim that carries a scope is well scoped whatever its relation. -/
theorem Claim.wellScoped_some {φ ψ : PLLFormula} {r : Rel} {R : List PLLFormula} :
    Claim.wellScoped ⟨φ, ψ, r, some R⟩ := fun _ => rfl

/-- The contrapositive, which is the fact the database rests on: from an
entry one can always read off the representative set a negative verdict
was relative to. -/
theorem Claim.scope_isSome_of_nle {c : Claim} (hw : c.wellScoped)
    (h : c.rel = Rel.nle) : c.scope.isSome = true := hw h

/-! ## 3. Evidence

`Evidence` is the PROVENANCE record — which engine spoke, how big the
countermodel was, which entries a derived entry came from.  It is
deliberately not indexed by the claim: provenance is data, and data can
be wrong.  What cannot be wrong is `Evidence.Certifies`, which every
entry must discharge, and which entails the claim in every case
(`Evidence.Certifies.holds`). -/

/-- An entry identifier. -/
abbrev EntryId := String

/-- Which engine produced the evidence.  Provenance only: an engine
label is never part of a truth condition. -/
inductive Engine where
  /-- The finite-countermodel checker: `FinCM.checkB` +
  `FinCM.not_provable_of_check`, kernel-`decide`-checkable. -/
  | finCM
  /-- The FRJ(◯) refutation search. -/
  | frj
  /-- The two-sided engine (LJF◯ focused search + `Reject.certifies`). -/
  | twoSided
  /-- The repaired FRJ(◯) calculus FRJV: the verdict rests on
  `soundnessV` applied to a kernel-checked derivation
  (`FRJ/CalculusV.lean`); the countermodel is extracted from the
  derivation by `FRJ.V.modR`. -/
  | frjv
  /-- Hand-authored; no engine was involved. -/
  | hand
  deriving DecidableEq, Repr, Inhabited

/-- The rules by which one entry may be derived from others already in
the database. -/
inductive DerivRule where
  /-- `a ⊣⊢ b`, `b ⊣⊢ c` ⟹ `a ⊣⊢ c`.  Two parents. -/
  | trans
  /-- `a ⊣⊢ b` ⟹ `b ⊣⊢ a`.  One parent. -/
  | symm
  deriving DecidableEq, Repr, Inhabited

/-- How many parents the rule consumes. -/
def DerivRule.arity : DerivRule → Nat
  | DerivRule.trans => 2
  | DerivRule.symm => 1

/-- Where an entry's warrant comes from. -/
inductive Evidence where
  /-- A proof certificate: a derivation, found by `engine`. -/
  | proof (engine : Engine)
  /-- A countermodel with `worlds` worlds, found by `engine`. -/
  | countermodel (engine : Engine) (worlds : Nat)
  /-- Derived from entries already in the database. -/
  | derived (parents : List EntryId) (rule : DerivRule)
  deriving DecidableEq, Repr, Inhabited

/-- **What it takes for `ev` to establish `c`.**

Every case ends in `c.Holds` — that is the whole point of the field, and
`Evidence.Certifies.holds` extracts it uniformly.  Every case also
demands `c.wellScoped`, which is free on a positive claim and is the
scope obligation on a negative one.

The remaining conjuncts are coherence conditions between the provenance
record and the claim, and they are what stop the record drifting away
from what was actually done:

* a proof certificate may be offered only for a POSITIVE claim — a
  derivation cannot witness a non-entailment;
* a countermodel only for a NEGATIVE one, and only with at least one
  world — a zero-world countermodel is not a countermodel;
* a derived entry must name exactly as many parents as its rule
  consumes. -/
def Evidence.Certifies : Evidence → Claim → Prop
  | Evidence.proof _, c => c.wellScoped ∧ c.rel.IsPositive ∧ c.Holds
  | Evidence.countermodel _ w, c => c.wellScoped ∧ c.rel = Rel.nle ∧ 0 < w ∧ c.Holds
  | Evidence.derived ps r, c => c.wellScoped ∧ ps.length = r.arity ∧ c.Holds

/-- Whatever the evidence kind, certified evidence entails the claim. -/
theorem Evidence.Certifies.holds {ev : Evidence} {c : Claim}
    (h : ev.Certifies c) : c.Holds := by
  cases ev with
  | proof _ => exact h.2.2
  | countermodel _ _ => exact h.2.2.2
  | derived _ _ => exact h.2.2

/-- Whatever the evidence kind, certified evidence is well scoped. -/
theorem Evidence.Certifies.wellScoped {ev : Evidence} {c : Claim}
    (h : ev.Certifies c) : c.wellScoped := by
  cases ev with
  | proof _ => exact h.1
  | countermodel _ _ => exact h.1
  | derived _ _ => exact h.1

/-! ## 4. Entries

The one structure in the file with a proof field. -/

/-- A database entry.  `ok` has no default and no alternative
constructor: an `Entry` whose claim is not proved cannot be written
down. -/
structure Entry where
  /-- Stable identifier, cited by `Evidence.derived`. -/
  id : EntryId
  /-- What is claimed. -/
  claim : Claim
  /-- Where the warrant came from. -/
  ev : Evidence
  /-- **The proof obligation.**  This is the field that makes an
  unproved entry unwritable rather than merely discouraged. -/
  ok : ev.Certifies claim

/-- Every entry's claim is true. -/
theorem Entry.holds (e : Entry) : e.claim.Holds := e.ok.holds

/-- Every entry's claim is well scoped: a negative entry always says
which representative set its verdict is relative to. -/
theorem Entry.wellScoped (e : Entry) : e.claim.wellScoped := e.ok.wellScoped

/-- **The database cannot record an unproved claim.**  Not a property of
any particular list — a property of the type. -/
theorem entries_hold (E : List Entry) : ∀ e ∈ E, e.claim.Holds :=
  fun e _ => e.holds

/-- **Every negative verdict in the database is relative to a recorded
representative set.**  The fault of round 1, closed by construction. -/
theorem neg_entries_scoped (E : List Entry) :
    ∀ e ∈ E, e.claim.rel = Rel.nle → e.claim.scope.isSome = true :=
  fun e _ => e.wellScoped

/-! ## 5. The frontier

An UNSETTLED claim gets no declaration.  It is an element of a list of
`Claim`s — pure data, asserting nothing, and carrying no proof field to
leave empty.  This is the replacement for `theorem c : P := sorry`, and
the difference is that a `Claim` cannot be applied, cited or depended on
as though it were a fact. -/

/-- The open questions: claims that have been posed and not settled.

A list of `Claim`s and nothing else.  There is deliberately no structure
pairing a claim with a status, because a status field is precisely how
"open" and "asserted without proof" come to be written the same way. -/
def Frontier : Type := List Claim


/-! ## 7. Axiom pins

Transcribed verbatim from `lake env lean RNDB/Types.lean`.  Since the
worked examples moved to `RNDB/Examples.lean` (2026-08-24) this module
imports nothing from `wip/`.  Two DIFFERENT properties are in play and
must not be conflated (peer correction, 2026-08-24): REACHABILITY — no
sorry-carrying module in the import closure, which is what
`scripts/core-audit.py` gates — and TAINT — no theorem here depends on a
sorried declaration, which is what the `#guard_msgs` pins check.  The
pins were always what made the entries safe; reachability is what makes
them ADMISSIBLE to the publication branch.  Since the `Deriv`/`Interd`
hoist (`LaxLogic/Interd.lean`) this module's closure carries neither
`wip/` nor the semantic-UI chain, so both properties hold. -/

/-- info: 'RNDB.entries_hold' does not depend on any axioms -/
#guard_msgs in
#print axioms entries_hold

/-- info: 'RNDB.neg_entries_scoped' does not depend on any axioms -/
#guard_msgs in
#print axioms neg_entries_scoped
end RNDB
