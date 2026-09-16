/-
# The ρ-order catalogue — the 22 representatives, as DATA

Hoisted out of `wip/rho_order.lean` on 2026-08-24 (the Reps-pattern:
formulas and a numbering, NOTHING asserted — no order, no distinctness;
on Matthew's standing rule those are re-derived from evidence-carrying
certificates, never carried over from a withdrawn table).  The probe
machinery stays in `wip/`; this file is what certificates, entries and
the frontier may cite without touching scratch space.

Every definition is definitionally equal to the `wip/` original (both
reduce to the same `PLLFormula` literals), so existing `decide`-checked
certificates recompile unchanged.
-/
import LaxLogic.RN.Reps

open PLLND RNReps

namespace RhoOrder

abbrev F := PLLFormula

def r13 : F := q10.ifThen q4
def w1  : F := q9.ifThen q4   -- the `w16` of the sweep; = `q15`'s formula

def rhos : List (String × F) :=
  [ ("ρ0",  q0),                ("ρ1",  q1),
    ("ρ2",  q2),                ("ρ3",  q3),
    ("ρ4",  q4),                ("ρ5",  q6),
    ("ρ6",  q7),                ("ρ7",  q5),
    ("ρ8",  q10),               ("ρ9",  q9),
    ("ρ10", q11),               ("ρ11", q8),
    ("ρ12", q14),               ("ρ13", r13),
    ("ρ14", w1),                ("ρ15", q8.or q5),
    ("ρ16", w1.or q5),          ("ρ17", q6.or w1),
    ("ρ18", w1.or q9),          ("ρ19", q8.ifThen q5),
    ("ρ20", q8.ifThen q7),      ("ρ21", w1.ifThen q5) ]

/-- The eight sweep discoveries — the classes the catalogue never
placed.  ρ13 is a new SHAPE; ρ15–ρ21 are combinations. -/
def discovered : List Nat := [13, 15, 16, 17, 18, 19, 20, 21]

def rhoF (i : Nat) : F := (rhos.getD i ("", q0)).2
def rhoN (i : Nat) : String := (rhos.getD i ("", q0)).1

def n : Nat := rhos.length

end RhoOrder
