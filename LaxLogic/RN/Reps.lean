/-
# The RN(◯,{}) representatives — the shared dictionary

The variable-free fragment of PLL, `RN(◯,{})`, is PROVED INFINITE
(`closed_lax_infinite`), so no finite dictionary can ever close it.  What
this module holds is therefore not "the classes" but the representatives
DISCOVERED SO FAR, as a stable shared vocabulary that certificates,
probes and screens can all name without transcribing.

Before this module the fifteen definitions were transcribed FIVE times
under `wip/` (`rho_order`, `rnDict`, `rnBank`, `closed_frag`,
`rnc_probe`), all in agreement but with nothing enforcing it, and a
certificate wanting to name `q10` had to choose between importing scratch
space and making a sixth copy.

## The append-only rule

**`qk` never changes meaning.**  A representative, once given an index,
keeps its formula forever.  New classes take new indices at the end.  If
a representative is ever found to be wrong, it is NOT redefined: it gets
a new index and the old one stays, deprecated in place.

That rule is what makes the module safe under concurrent work.  A
certificate pinned against `q10` stays true no matter what anyone else
appends, two sessions can extend the dictionary at the same time without
conflicting anywhere but the append point, and no verdict recorded
against an index can be invalidated by a later edit.

The indices are serial — assigned in discovery order — so they carry no
information and must be looked up here.  A structural naming scheme,
where the index is computed from the formula and needs no registry at
all, is an open thread (`docs/next-session.md`).
-/
import LaxLogic.PLLNDCore

namespace RNReps

open PLLND PLLFormula

/-- `⊥` -/
def q0 : PLLFormula := falsePLL
/-- `⊤`, as `⊥ ⊃ ⊥` -/
def q1 : PLLFormula := ifThen q0 q0
/-- `◯⊥` -/
def q2 : PLLFormula := somehow q0
/-- `¬◯⊥` -/
def q3 : PLLFormula := ifThen q2 q0
/-- `◯⊥ ∨ ¬◯⊥` -/
def q4 : PLLFormula := or q2 q3
/-- `◯¬◯⊥` -/
def q5 : PLLFormula := somehow q3
/-- `¬¬◯⊥` -/
def q6 : PLLFormula := ifThen q3 q0
/-- `¬◯⊥ ∨ ¬¬◯⊥` -/
def q7 : PLLFormula := or q3 q6
/-- `◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥)` -/
def q8 : PLLFormula := ifThen q5 q4
/-- `◯¬◯⊥ ∨ ¬¬◯⊥` -/
def q9 : PLLFormula := or q5 q6
/-- `¬¬◯⊥ ⊃ ◯⊥` -/
def q10 : PLLFormula := ifThen q6 q2
/-- `¬¬◯⊥ ∨ (¬¬◯⊥ ⊃ ◯⊥)` -/
def q11 : PLLFormula := or q6 q10
/-- `◯(¬◯⊥ ∨ ¬¬◯⊥)` -/
def q12 : PLLFormula := somehow q7
/-- `◯(◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥))` -/
def q13 : PLLFormula := somehow q8
/-- `(¬¬◯⊥ ⊃ ◯⊥) ⊃ ◯¬◯⊥` -/
def q14 : PLLFormula := ifThen q10 q5

/-- The representatives in index order.  APPEND ONLY. -/
def reps : List PLLFormula :=
  [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14]

theorem reps_length : reps.length = 15 := rfl

end RNReps
