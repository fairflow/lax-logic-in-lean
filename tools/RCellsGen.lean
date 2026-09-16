import LaxLogic.PLLG4Term
import LaxLogic.RN.Reps
import LaxLogic.RN.Rho

/-!
# Generator for `wip/rcells.lean` — the R-increment simpset cells

The R-peg loop's promotion step (standing rule, 2026-08-26): every
classed R-table cell involving the nine post-dictionary classes
ρ13–ρ21 becomes a kernel-checked `Interd` theorem, G4c route — the
budgeted `G4cTm.findBounded` searcher runs COMPILED and untrusted, and
the found proof TERMS are printed as Lean source, so the kernel's only
job is type-checking the literals.  No fuel, no `decide` re-search.

Run: `lake build rcellsgen && .lake/build/bin/rcellsgen > wip/rcells.lean`
(progress and skips to stderr; skips also appear as comments in the file).
-/

open PLLFormula PLLND RhoOrder

namespace RCGen

/-! ## Printer machinery, copied from `wip/rnDictGen.lean` (RNGen) —
that module exports a root-level `main`, so it cannot be imported by
another executable.  `ppFN` names the fifteen q-representatives (via
`RNReps`, the same formulas); unknown formulas print as raw
constructors, so naming is compression only, never correctness. -/

def reps : List PLLFormula :=
  [RNReps.q0, RNReps.q1, RNReps.q2, RNReps.q3, RNReps.q4, RNReps.q5,
   RNReps.q6, RNReps.q7, RNReps.q8, RNReps.q9, RNReps.q10, RNReps.q11,
   RNReps.q12, RNReps.q13, RNReps.q14]

def repIdx? (X : PLLFormula) : Option Nat := reps.findIdx? (· = X)

def budget : Nat := 400000

partial def ppFN (n : Nat) (X : PLLFormula) : String :=
  match (repIdx? X).filter (· < n) with
  | some i => s!"q{i}"
  | none =>
    match X with
    | .prop s => s!"(.prop \"{s}\")"
    | .falsePLL => ".falsePLL"
    | .and a b => s!"(.and {ppFN n a} {ppFN n b})"
    | .or a b => s!"(.or {ppFN n a} {ppFN n b})"
    | .ifThen a b => s!"(.ifThen {ppFN n a} {ppFN n b})"
    | .somehow a => s!"(.somehow {ppFN n a})"

def ppF (X : PLLFormula) : String := ppFN 15 X

def memIdx (X : PLLFormula) : List PLLFormula → Nat
  | [] => 0
  | Y :: R => if X = Y then 0 else memIdx X R + 1

def memStrN : Nat → String
  | 0 => "(.head _)"
  | n + 1 => s!"(.tail _ {memStrN n})"

def memS (X : PLLFormula) (Γ : List PLLFormula) : String :=
  memStrN (memIdx X Γ)

partial def emitTm : {Γ : List PLLFormula} → {C : PLLFormula} → G4cTm Γ C → String
  | _, _, @G4cTm.init Γ a _ => s!"(.init {memS (.prop a) Γ})"
  | _, _, @G4cTm.botL Γ _ _ => s!"(.botL {memS .falsePLL Γ})"
  | _, _, @G4cTm.andR _ _ _ t1 t2 => s!"(.andR {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.orR1 _ _ _ t => s!"(.orR1 {emitTm t})"
  | _, _, @G4cTm.orR2 _ _ _ t => s!"(.orR2 {emitTm t})"
  | _, _, @G4cTm.impR _ _ _ t => s!"(.impR {emitTm t})"
  | _, _, @G4cTm.laxR _ _ t => s!"(.laxR {emitTm t})"
  | _, _, @G4cTm.laxL Γ A _ _ t =>
      s!"(.laxL (A := {ppF A}) {memS A.somehow Γ} {emitTm t})"
  | _, _, @G4cTm.andL Γ A B _ _ t =>
      s!"(.andL (A := {ppF A}) (B := {ppF B}) {memS (A.and B) Γ} {emitTm t})"
  | _, _, @G4cTm.orL Γ A B _ _ t1 t2 =>
      s!"(.orL (A := {ppF A}) (B := {ppF B}) {memS (A.or B) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLProp Γ a B _ _ _ t =>
      s!"(.impLProp (a := \"{a}\") (B := {ppF B}) {memS ((PLLFormula.prop a).ifThen B) Γ} {memS (.prop a) Γ} {emitTm t})"
  | _, _, @G4cTm.impLAnd Γ A B D _ _ t =>
      s!"(.impLAnd (A := {ppF A}) (B := {ppF B}) (D := {ppF D}) {memS ((A.and B).ifThen D) Γ} {emitTm t})"
  | _, _, @G4cTm.impLOr Γ A B D _ _ t =>
      s!"(.impLOr (A := {ppF A}) (B := {ppF B}) (D := {ppF D}) {memS ((A.or B).ifThen D) Γ} {emitTm t})"
  | _, _, @G4cTm.impLImp Γ A B D _ _ t1 t2 =>
      s!"(.impLImp (A := {ppF A}) (B := {ppF B}) (D := {ppF D}) {memS ((A.ifThen B).ifThen D) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLLax Γ A B _ _ t1 t2 =>
      s!"(.impLLax (A := {ppF A}) (B := {ppF B}) {memS (A.somehow.ifThen B) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLLaxLax Γ A B X _ _ _ t1 t2 =>
      s!"(.impLLaxLax (A := {ppF A}) (B := {ppF B}) (X := {ppF X}) {memS (A.somehow.ifThen B) Γ} {memS X.somehow Γ} {emitTm t1} {emitTm t2})"

/-- The 445 classed increment cells `(op, i, j, k)`: `ρi ∘ ρj ≡ ρk`,
from the committed R operation tables (`wip/rtable_out.txt`). -/
def cells : List (String × Nat × Nat × Nat) := [
  ("and", 0, 13, 0),
  ("and", 0, 14, 0),
  ("and", 0, 15, 0),
  ("and", 0, 16, 0),
  ("and", 0, 17, 0),
  ("and", 0, 18, 0),
  ("and", 0, 19, 0),
  ("and", 0, 20, 0),
  ("and", 0, 21, 0),
  ("and", 1, 13, 13),
  ("and", 1, 14, 14),
  ("and", 1, 15, 15),
  ("and", 1, 16, 16),
  ("and", 1, 17, 17),
  ("and", 1, 18, 18),
  ("and", 1, 19, 19),
  ("and", 1, 20, 20),
  ("and", 1, 21, 21),
  ("and", 2, 13, 2),
  ("and", 2, 14, 2),
  ("and", 2, 15, 2),
  ("and", 2, 16, 2),
  ("and", 2, 17, 2),
  ("and", 2, 18, 2),
  ("and", 2, 19, 2),
  ("and", 2, 20, 2),
  ("and", 2, 21, 2),
  ("and", 3, 13, 3),
  ("and", 3, 14, 3),
  ("and", 3, 15, 3),
  ("and", 3, 16, 3),
  ("and", 3, 17, 3),
  ("and", 3, 18, 3),
  ("and", 3, 19, 3),
  ("and", 3, 20, 3),
  ("and", 3, 21, 3),
  ("and", 4, 13, 4),
  ("and", 4, 14, 4),
  ("and", 4, 15, 4),
  ("and", 4, 16, 4),
  ("and", 4, 17, 4),
  ("and", 4, 18, 4),
  ("and", 4, 19, 4),
  ("and", 4, 20, 4),
  ("and", 4, 21, 4),
  ("and", 5, 13, 5),
  ("and", 5, 14, 2),
  ("and", 5, 15, 5),
  ("and", 5, 16, 2),
  ("and", 5, 17, 5),
  ("and", 5, 18, 5),
  ("and", 5, 19, 2),
  ("and", 5, 20, 5),
  ("and", 5, 21, 5),
  ("and", 6, 13, 6),
  ("and", 6, 14, 4),
  ("and", 6, 15, 6),
  ("and", 6, 16, 4),
  ("and", 6, 17, 6),
  ("and", 6, 18, 6),
  ("and", 6, 19, 4),
  ("and", 6, 20, 6),
  ("and", 6, 21, 6),
  ("and", 7, 13, 4),
  ("and", 7, 14, 4),
  ("and", 7, 15, 7),
  ("and", 7, 16, 7),
  ("and", 7, 17, 4),
  ("and", 7, 18, 7),
  ("and", 7, 19, 7),
  ("and", 7, 20, 7),
  ("and", 7, 21, 7),
  ("and", 8, 13, 4),
  ("and", 8, 14, 14),
  ("and", 8, 15, 16),
  ("and", 8, 16, 16),
  ("and", 8, 17, 14),
  ("and", 8, 18, 16),
  ("and", 8, 19, 19),
  ("and", 8, 20, 19),
  ("and", 9, 13, 6),
  ("and", 9, 14, 4),
  ("and", 9, 15, 9),
  ("and", 9, 16, 7),
  ("and", 9, 17, 6),
  ("and", 9, 18, 9),
  ("and", 9, 19, 7),
  ("and", 9, 20, 9),
  ("and", 9, 21, 9),
  ("and", 10, 13, 6),
  ("and", 10, 14, 14),
  ("and", 10, 15, 18),
  ("and", 10, 16, 16),
  ("and", 10, 17, 17),
  ("and", 10, 18, 18),
  ("and", 10, 19, 19),
  ("and", 11, 13, 13),
  ("and", 11, 14, 14),
  ("and", 11, 15, 11),
  ("and", 11, 16, 14),
  ("and", 11, 17, 17),
  ("and", 11, 18, 17),
  ("and", 11, 19, 4),
  ("and", 11, 20, 6),
  ("and", 12, 13, 13),
  ("and", 12, 14, 4),
  ("and", 12, 16, 7),
  ("and", 12, 17, 6),
  ("and", 12, 19, 7),
  ("and", 12, 21, 12),
  ("and", 13, 13, 13),
  ("and", 13, 14, 4),
  ("and", 13, 15, 13),
  ("and", 13, 16, 4),
  ("and", 13, 17, 6),
  ("and", 13, 19, 4),
  ("and", 13, 21, 13),
  ("and", 14, 14, 14),
  ("and", 14, 15, 14),
  ("and", 14, 16, 14),
  ("and", 14, 17, 14),
  ("and", 14, 18, 14),
  ("and", 14, 19, 4),
  ("and", 15, 15, 15),
  ("and", 15, 16, 16),
  ("and", 15, 17, 17),
  ("and", 15, 18, 18),
  ("and", 15, 19, 7),
  ("and", 15, 20, 9),
  ("and", 16, 16, 16),
  ("and", 16, 17, 14),
  ("and", 16, 18, 16),
  ("and", 16, 19, 7),
  ("and", 17, 17, 17),
  ("and", 17, 18, 17),
  ("and", 18, 18, 18),
  ("and", 19, 19, 19),
  ("and", 19, 20, 19),
  ("and", 19, 21, 19),
  ("and", 20, 20, 20),
  ("and", 20, 21, 20),
  ("and", 21, 21, 21),
  ("or", 0, 13, 13),
  ("or", 0, 14, 14),
  ("or", 0, 15, 15),
  ("or", 0, 16, 16),
  ("or", 0, 17, 17),
  ("or", 0, 18, 18),
  ("or", 0, 19, 19),
  ("or", 0, 20, 20),
  ("or", 0, 21, 21),
  ("or", 1, 13, 1),
  ("or", 1, 14, 1),
  ("or", 1, 15, 1),
  ("or", 1, 16, 1),
  ("or", 1, 17, 1),
  ("or", 1, 18, 1),
  ("or", 1, 19, 1),
  ("or", 1, 20, 1),
  ("or", 1, 21, 1),
  ("or", 2, 13, 13),
  ("or", 2, 14, 14),
  ("or", 2, 15, 15),
  ("or", 2, 16, 16),
  ("or", 2, 17, 17),
  ("or", 2, 18, 18),
  ("or", 2, 19, 19),
  ("or", 2, 20, 20),
  ("or", 2, 21, 21),
  ("or", 3, 13, 13),
  ("or", 3, 14, 14),
  ("or", 3, 15, 15),
  ("or", 3, 16, 16),
  ("or", 3, 17, 17),
  ("or", 3, 18, 18),
  ("or", 3, 19, 19),
  ("or", 3, 20, 20),
  ("or", 3, 21, 21),
  ("or", 4, 13, 13),
  ("or", 4, 14, 14),
  ("or", 4, 15, 15),
  ("or", 4, 16, 16),
  ("or", 4, 17, 17),
  ("or", 4, 18, 18),
  ("or", 4, 19, 19),
  ("or", 4, 20, 20),
  ("or", 4, 21, 21),
  ("or", 5, 13, 13),
  ("or", 5, 14, 17),
  ("or", 5, 15, 15),
  ("or", 5, 16, 18),
  ("or", 5, 17, 17),
  ("or", 5, 18, 18),
  ("or", 5, 20, 20),
  ("or", 5, 21, 21),
  ("or", 6, 13, 13),
  ("or", 6, 14, 17),
  ("or", 6, 15, 15),
  ("or", 6, 16, 18),
  ("or", 6, 17, 17),
  ("or", 6, 18, 18),
  ("or", 6, 20, 20),
  ("or", 6, 21, 21),
  ("or", 7, 14, 16),
  ("or", 7, 15, 15),
  ("or", 7, 16, 16),
  ("or", 7, 17, 18),
  ("or", 7, 18, 18),
  ("or", 7, 19, 19),
  ("or", 7, 20, 20),
  ("or", 7, 21, 21),
  ("or", 8, 14, 8),
  ("or", 8, 16, 8),
  ("or", 8, 17, 10),
  ("or", 8, 18, 10),
  ("or", 8, 19, 8),
  ("or", 9, 14, 18),
  ("or", 9, 15, 15),
  ("or", 9, 16, 18),
  ("or", 9, 17, 18),
  ("or", 9, 18, 18),
  ("or", 9, 20, 20),
  ("or", 9, 21, 21),
  ("or", 10, 14, 10),
  ("or", 10, 16, 10),
  ("or", 10, 17, 10),
  ("or", 10, 18, 10),
  ("or", 10, 19, 10),
  ("or", 11, 13, 11),
  ("or", 11, 14, 11),
  ("or", 11, 15, 15),
  ("or", 11, 16, 15),
  ("or", 11, 17, 11),
  ("or", 11, 18, 15),
  ("or", 12, 13, 12),
  ("or", 12, 21, 21),
  ("or", 13, 13, 13),
  ("or", 13, 15, 15),
  ("or", 13, 21, 21),
  ("or", 14, 14, 14),
  ("or", 14, 15, 15),
  ("or", 14, 16, 16),
  ("or", 14, 17, 17),
  ("or", 14, 18, 18),
  ("or", 15, 15, 15),
  ("or", 15, 16, 15),
  ("or", 15, 17, 15),
  ("or", 15, 18, 15),
  ("or", 16, 16, 16),
  ("or", 16, 17, 18),
  ("or", 16, 18, 18),
  ("or", 17, 17, 17),
  ("or", 17, 18, 18),
  ("or", 18, 18, 18),
  ("or", 19, 19, 19),
  ("or", 19, 20, 20),
  ("or", 19, 21, 21),
  ("or", 20, 20, 20),
  ("or", 20, 21, 21),
  ("or", 21, 21, 21),
  ("imp", 0, 13, 1),
  ("imp", 0, 14, 1),
  ("imp", 0, 15, 1),
  ("imp", 0, 16, 1),
  ("imp", 0, 17, 1),
  ("imp", 0, 18, 1),
  ("imp", 0, 19, 1),
  ("imp", 0, 20, 1),
  ("imp", 0, 21, 1),
  ("imp", 1, 13, 13),
  ("imp", 1, 14, 14),
  ("imp", 1, 15, 15),
  ("imp", 1, 16, 16),
  ("imp", 1, 17, 17),
  ("imp", 1, 18, 18),
  ("imp", 1, 19, 19),
  ("imp", 1, 20, 20),
  ("imp", 2, 13, 1),
  ("imp", 2, 14, 1),
  ("imp", 2, 15, 1),
  ("imp", 2, 16, 1),
  ("imp", 2, 17, 1),
  ("imp", 2, 18, 1),
  ("imp", 2, 19, 1),
  ("imp", 2, 20, 1),
  ("imp", 2, 21, 1),
  ("imp", 3, 13, 1),
  ("imp", 3, 14, 1),
  ("imp", 3, 15, 1),
  ("imp", 3, 16, 1),
  ("imp", 3, 17, 1),
  ("imp", 3, 18, 1),
  ("imp", 3, 19, 1),
  ("imp", 3, 20, 1),
  ("imp", 3, 21, 1),
  ("imp", 4, 13, 1),
  ("imp", 4, 14, 1),
  ("imp", 4, 15, 1),
  ("imp", 4, 16, 1),
  ("imp", 4, 17, 1),
  ("imp", 4, 18, 1),
  ("imp", 4, 19, 1),
  ("imp", 4, 20, 1),
  ("imp", 4, 21, 1),
  ("imp", 5, 13, 1),
  ("imp", 5, 14, 8),
  ("imp", 5, 15, 1),
  ("imp", 5, 16, 8),
  ("imp", 5, 17, 1),
  ("imp", 5, 18, 1),
  ("imp", 5, 19, 8),
  ("imp", 5, 20, 1),
  ("imp", 5, 21, 1),
  ("imp", 6, 13, 1),
  ("imp", 6, 14, 8),
  ("imp", 6, 15, 1),
  ("imp", 6, 17, 1),
  ("imp", 6, 18, 1),
  ("imp", 6, 20, 1),
  ("imp", 6, 21, 1),
  ("imp", 7, 13, 11),
  ("imp", 7, 14, 11),
  ("imp", 7, 15, 1),
  ("imp", 7, 16, 1),
  ("imp", 7, 17, 11),
  ("imp", 7, 18, 1),
  ("imp", 7, 19, 1),
  ("imp", 7, 20, 1),
  ("imp", 7, 21, 1),
  ("imp", 8, 13, 13),
  ("imp", 8, 14, 11),
  ("imp", 8, 17, 11),
  ("imp", 9, 13, 11),
  ("imp", 9, 14, 14),
  ("imp", 9, 15, 1),
  ("imp", 9, 17, 11),
  ("imp", 9, 18, 1),
  ("imp", 9, 20, 1),
  ("imp", 9, 21, 1),
  ("imp", 10, 13, 13),
  ("imp", 10, 17, 11),
  ("imp", 11, 15, 1),
  ("imp", 12, 13, 11),
  ("imp", 12, 21, 1),
  ("imp", 13, 0, 0),
  ("imp", 13, 1, 1),
  ("imp", 13, 2, 2),
  ("imp", 13, 3, 3),
  ("imp", 13, 4, 8),
  ("imp", 13, 5, 5),
  ("imp", 13, 7, 8),
  ("imp", 13, 8, 8),
  ("imp", 13, 11, 1),
  ("imp", 13, 12, 1),
  ("imp", 13, 13, 1),
  ("imp", 13, 15, 1),
  ("imp", 13, 21, 1),
  ("imp", 14, 0, 0),
  ("imp", 14, 1, 1),
  ("imp", 14, 2, 5),
  ("imp", 14, 3, 3),
  ("imp", 14, 5, 5),
  ("imp", 14, 8, 1),
  ("imp", 14, 10, 1),
  ("imp", 14, 11, 1),
  ("imp", 14, 14, 1),
  ("imp", 14, 15, 1),
  ("imp", 14, 16, 1),
  ("imp", 14, 17, 1),
  ("imp", 14, 18, 1),
  ("imp", 15, 0, 0),
  ("imp", 15, 1, 1),
  ("imp", 15, 2, 2),
  ("imp", 15, 3, 3),
  ("imp", 15, 4, 4),
  ("imp", 15, 5, 5),
  ("imp", 15, 6, 6),
  ("imp", 15, 7, 19),
  ("imp", 15, 8, 8),
  ("imp", 15, 11, 11),
  ("imp", 15, 15, 1),
  ("imp", 16, 0, 0),
  ("imp", 16, 1, 1),
  ("imp", 16, 2, 5),
  ("imp", 16, 3, 3),
  ("imp", 16, 5, 5),
  ("imp", 16, 8, 1),
  ("imp", 16, 10, 1),
  ("imp", 16, 11, 11),
  ("imp", 16, 15, 1),
  ("imp", 16, 16, 1),
  ("imp", 16, 18, 1),
  ("imp", 17, 0, 0),
  ("imp", 17, 1, 1),
  ("imp", 17, 2, 2),
  ("imp", 17, 3, 3),
  ("imp", 17, 5, 5),
  ("imp", 17, 10, 1),
  ("imp", 17, 11, 1),
  ("imp", 17, 15, 1),
  ("imp", 17, 17, 1),
  ("imp", 17, 18, 1),
  ("imp", 18, 0, 0),
  ("imp", 18, 1, 1),
  ("imp", 18, 2, 2),
  ("imp", 18, 3, 3),
  ("imp", 18, 5, 5),
  ("imp", 18, 10, 1),
  ("imp", 18, 15, 1),
  ("imp", 18, 18, 1),
  ("imp", 19, 0, 0),
  ("imp", 19, 1, 1),
  ("imp", 19, 2, 5),
  ("imp", 19, 3, 3),
  ("imp", 19, 4, 11),
  ("imp", 19, 5, 5),
  ("imp", 19, 6, 11),
  ("imp", 19, 8, 1),
  ("imp", 19, 10, 1),
  ("imp", 19, 11, 11),
  ("imp", 19, 13, 11),
  ("imp", 19, 14, 11),
  ("imp", 19, 17, 11),
  ("imp", 19, 19, 1),
  ("imp", 19, 20, 1),
  ("imp", 19, 21, 1),
  ("imp", 20, 0, 0),
  ("imp", 20, 1, 1),
  ("imp", 20, 2, 2),
  ("imp", 20, 3, 3),
  ("imp", 20, 5, 5),
  ("imp", 20, 6, 11),
  ("imp", 20, 8, 8),
  ("imp", 20, 11, 11),
  ("imp", 20, 20, 1),
  ("imp", 20, 21, 1),
  ("imp", 21, 0, 0),
  ("imp", 21, 1, 1),
  ("imp", 21, 2, 2),
  ("imp", 21, 3, 3),
  ("imp", 21, 5, 5),
  ("imp", 21, 8, 8),
  ("imp", 21, 11, 11),
  ("imp", 21, 14, 14),
  ("box", 19, 0, 19)]

def mkOp : String → PLLFormula → PLLFormula → PLLFormula
  | "and", a, b => a.and b
  | "or",  a, b => a.or b
  | "imp", a, b => a.ifThen b
  | _,     a, _ => a.somehow

def opSrc : String → Nat → Nat → String
  | "and", i, j => s!"((rhoF {i}).and (rhoF {j}))"
  | "or",  i, j => s!"((rhoF {i}).or (rhoF {j}))"
  | "imp", i, j => s!"((rhoF {i}).ifThen (rhoF {j}))"
  | _,     i, _ => s!"((rhoF {i}).somehow)"

def main : IO Unit := do
  let err ← IO.getStderr
  IO.println "import wip.rnDict"
  IO.println "import LaxLogic.RN.Rho"
  IO.println "import Rewrite.Core"
  IO.println ""
  IO.println "/-!"
  IO.println "# The R-increment simpset cells — GENERATED by `rcellsgen`"
  IO.println ""
  IO.println "Kernel-checked `Interd` theorems for the classed R-table cells"
  IO.println "involving ρ13–ρ21, each proved by a pair of emitted `G4cTm` proof"
  IO.println "terms through `ofG4` (`wip/rnDictBase.lean`).  The searcher that"
  IO.println "found the terms is untrusted; the kernel type-checks every literal"
  IO.println "at elaboration.  `rcSet` collects the cells as rewrite rules,"
  IO.println "oriented compound → representative.  DO NOT EDIT BY HAND — rerun"
  IO.println "the generator (see tools/RCellsGen.lean)."
  IO.println "-/"
  IO.println ""
  IO.println "open PLLFormula RhoOrder"
  IO.println ""
  IO.println "namespace PLLND"
  IO.println "namespace SemUI"
  IO.println "namespace RCX"
  IO.println ""
  IO.println "export RNReps (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14)"
  IO.println ""
  IO.println "open RND (ofG4)"
  IO.println ""
  let mut names : List String := []
  let mut nSkip := 0
  for (op, i, j, k) in cells do
    let lhs := mkOp op (rhoF i) (rhoF j)
    let rhs := rhoF k
    if lhs == rhs then
      IO.println s!"-- TRIV {op} {i} {j}: lhs is ρ{k} syntactically; no rule"
      continue
    match (G4cTm.findBounded budget [lhs] rhs).1 with
    | none =>
        nSkip := nSkip + 1
        IO.println s!"-- SKIP {op} {i} {j} ≡ ρ{k}: forward direction not settled at budget {budget}"
        err.putStrLn s!"SKIP fwd {op} {i} {j} {k}"
    | some t1 =>
      match (G4cTm.findBounded budget [rhs] lhs).1 with
      | none =>
          nSkip := nSkip + 1
          IO.println s!"-- SKIP {op} {i} {j} ≡ ρ{k}: backward direction not settled at budget {budget}"
          err.putStrLn s!"SKIP bwd {op} {i} {j} {k}"
      | some t2 =>
          let nm := s!"rc_{op}_{i}_{j}"
          names := nm :: names
          IO.println s!"theorem {nm} : Interd {opSrc op i j} (rhoF {k}) :="
          IO.println s!"  ⟨(ofG4 {emitTm t1}),"
          IO.println s!"   (ofG4 {emitTm t2})⟩"
          IO.println ""
          err.putStrLn s!"OK {op} {i} {j} {k}"
  IO.println "/-- The increment rules, oriented compound → representative. -/"
  IO.println "def rcSet : List Rewrite.RwRule :="
  IO.println "  ["
  for nm in names.reverse do
    IO.println s!"  ⟨_, _, {nm}⟩,"
  IO.println "  ]"
  IO.println ""
  IO.println "end RCX"
  IO.println "end SemUI"
  IO.println "end PLLND"
  err.putStrLn s!"RCELLSGEN-DONE ok={names.length} skip={nSkip}"

end RCGen

def main : IO Unit := RCGen.main
