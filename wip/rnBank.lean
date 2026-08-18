/-
# The RN(◯,{}) oracle bank — GENERATED FILE, do not edit by hand

Produced by `sh tools/rn-bank-gen.sh > wip/rnBank.lean` from the certified
dictionary `wip/rnDict.lean`.

Every cell of the dictionary, as a pair of implications between variable-free
PLL formulas, tagged with what is already known:

* `proved`  — `Interd` is kernel-checked in `rnDict`.  Neither direction is
  refutable, so a countermodel found here is an ENGINE BUG.
* `refuted` — the stated collapse is FALSE, with a certified ≤4-world
  countermodel.  At least one direction MUST be found.
* `open`    — neither proved nor refuted at ≤4 worlds.  These are the
  targets: a refutation closes a `sorry` and moves the ladder.

The bank is deliberately independent of `rnDict` itself (the representatives
are copied, not imported): the dictionary carries megabytes of proof terms
that a search harness has no use for.
-/
import FRJ.Bridge

namespace RNBank

/-! ## The fifteen representatives (copied from `wip/rnDict.lean`) -/

def q0 : PLLFormula := .falsePLL
def q1 : PLLFormula := (.ifThen q0 q0)
def q2 : PLLFormula := (.somehow q0)
def q3 : PLLFormula := (.ifThen q2 q0)
def q4 : PLLFormula := (.or q2 q3)
def q5 : PLLFormula := (.somehow q3)
def q6 : PLLFormula := (.ifThen q3 q0)
def q7 : PLLFormula := (.or q3 q6)
def q8 : PLLFormula := (.ifThen q5 q4)
def q9 : PLLFormula := (.or q5 q6)
def q10 : PLLFormula := (.ifThen q6 q2)
def q11 : PLLFormula := (.or q6 q10)
def q12 : PLLFormula := (.somehow q7)
def q13 : PLLFormula := (.somehow q8)
def q14 : PLLFormula := (.ifThen q10 q5)

def reps : List PLLFormula :=
  [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14]

/-! ## The cells -/

inductive Status where
  | proved
  | refuted
  | «open»
  deriving DecidableEq, Repr

def Status.toString : Status → String
  | .proved  => "proved"
  | .refuted => "refuted"
  | .«open»  => "open"

structure Cell where
  name   : String
  lhs    : PLLFormula
  rhs    : PLLFormula
  status : Status

/-- Every dictionary cell.  `lhs` is the combination, `rhs` the
representative the table assigns to it. -/
def cells : List Cell := [
  ⟨"cAnd_2_3", q2.and q3, q0, .proved⟩,
  ⟨"cAnd_2_4", q2.and q4, q2, .proved⟩,
  ⟨"cAnd_2_5", q2.and q5, q2, .proved⟩,
  ⟨"cAnd_2_6", q2.and q6, q2, .proved⟩,
  ⟨"cAnd_2_7", q2.and q7, q2, .proved⟩,
  ⟨"cAnd_2_8", q2.and q8, q2, .proved⟩,
  ⟨"cAnd_2_9", q2.and q9, q2, .proved⟩,
  ⟨"cAnd_2_10", q2.and q10, q2, .proved⟩,
  ⟨"cAnd_2_11", q2.and q11, q2, .proved⟩,
  ⟨"cAnd_2_12", q2.and q12, q2, .proved⟩,
  ⟨"cAnd_2_13", q2.and q13, q2, .proved⟩,
  ⟨"cAnd_2_14", q2.and q14, q2, .proved⟩,
  ⟨"cAnd_3_4", q3.and q4, q3, .proved⟩,
  ⟨"cAnd_3_5", q3.and q5, q3, .proved⟩,
  ⟨"cAnd_3_6", q3.and q6, q0, .proved⟩,
  ⟨"cAnd_3_7", q3.and q7, q3, .proved⟩,
  ⟨"cAnd_3_8", q3.and q8, q3, .proved⟩,
  ⟨"cAnd_3_9", q3.and q9, q3, .proved⟩,
  ⟨"cAnd_3_10", q3.and q10, q3, .proved⟩,
  ⟨"cAnd_3_11", q3.and q11, q3, .proved⟩,
  ⟨"cAnd_3_12", q3.and q12, q3, .proved⟩,
  ⟨"cAnd_3_13", q3.and q13, q3, .proved⟩,
  ⟨"cAnd_3_14", q3.and q14, q3, .proved⟩,
  ⟨"cAnd_4_5", q4.and q5, q4, .proved⟩,
  ⟨"cAnd_4_6", q4.and q6, q2, .proved⟩,
  ⟨"cAnd_4_7", q4.and q7, q4, .proved⟩,
  ⟨"cAnd_4_8", q4.and q8, q4, .proved⟩,
  ⟨"cAnd_4_9", q4.and q9, q4, .proved⟩,
  ⟨"cAnd_4_10", q4.and q10, q4, .proved⟩,
  ⟨"cAnd_4_11", q4.and q11, q4, .proved⟩,
  ⟨"cAnd_4_12", q4.and q12, q4, .proved⟩,
  ⟨"cAnd_4_13", q4.and q13, q4, .proved⟩,
  ⟨"cAnd_4_14", q4.and q14, q4, .«open»⟩,
  ⟨"cAnd_5_6", q5.and q6, q2, .proved⟩,
  ⟨"cAnd_5_7", q5.and q7, q4, .proved⟩,
  ⟨"cAnd_5_8", q5.and q8, q4, .proved⟩,
  ⟨"cAnd_5_9", q5.and q9, q5, .proved⟩,
  ⟨"cAnd_5_10", q5.and q10, q5, .proved⟩,
  ⟨"cAnd_5_11", q5.and q11, q5, .proved⟩,
  ⟨"cAnd_5_12", q5.and q12, q5, .proved⟩,
  ⟨"cAnd_5_13", q5.and q13, q5, .proved⟩,
  ⟨"cAnd_5_14", q5.and q14, q5, .proved⟩,
  ⟨"cAnd_6_7", q6.and q7, q6, .proved⟩,
  ⟨"cAnd_6_8", q6.and q8, q6, .proved⟩,
  ⟨"cAnd_6_9", q6.and q9, q6, .proved⟩,
  ⟨"cAnd_6_10", q6.and q10, q2, .proved⟩,
  ⟨"cAnd_6_11", q6.and q11, q6, .proved⟩,
  ⟨"cAnd_6_12", q6.and q12, q6, .proved⟩,
  ⟨"cAnd_6_13", q6.and q13, q6, .proved⟩,
  ⟨"cAnd_6_14", q6.and q14, q6, .proved⟩,
  ⟨"cAnd_7_8", q7.and q8, q7, .proved⟩,
  ⟨"cAnd_7_9", q7.and q9, q7, .proved⟩,
  ⟨"cAnd_7_10", q7.and q10, q4, .proved⟩,
  ⟨"cAnd_7_11", q7.and q11, q7, .proved⟩,
  ⟨"cAnd_7_12", q7.and q12, q7, .proved⟩,
  ⟨"cAnd_7_13", q7.and q13, q7, .proved⟩,
  ⟨"cAnd_7_14", q7.and q14, q7, .proved⟩,
  ⟨"cAnd_8_9", q8.and q9, q7, .proved⟩,
  ⟨"cAnd_8_10", q8.and q10, q0, .refuted⟩,
  ⟨"cAnd_8_11", q8.and q11, q8, .«open»⟩,
  ⟨"cAnd_8_12", q8.and q12, q7, .«open»⟩,
  ⟨"cAnd_8_13", q8.and q13, q8, .proved⟩,
  ⟨"cAnd_8_14", q8.and q14, q7, .«open»⟩,
  ⟨"cAnd_9_10", q9.and q10, q5, .proved⟩,
  ⟨"cAnd_9_11", q9.and q11, q9, .proved⟩,
  ⟨"cAnd_9_12", q9.and q12, q9, .proved⟩,
  ⟨"cAnd_9_13", q9.and q13, q9, .«open»⟩,
  ⟨"cAnd_9_14", q9.and q14, q9, .«open»⟩,
  ⟨"cAnd_10_11", q10.and q11, q10, .proved⟩,
  ⟨"cAnd_10_12", q10.and q12, q5, .proved⟩,
  ⟨"cAnd_10_13", q10.and q13, q10, .«open»⟩,
  ⟨"cAnd_10_14", q10.and q14, q5, .«open»⟩,
  ⟨"cAnd_11_12", q11.and q12, q9, .proved⟩,
  ⟨"cAnd_11_13", q11.and q13, q1, .«open»⟩,
  ⟨"cAnd_11_14", q11.and q14, q9, .«open»⟩,
  ⟨"cAnd_12_13", q12.and q13, q9, .«open»⟩,
  ⟨"cAnd_12_14", q12.and q14, q9, .«open»⟩,
  ⟨"cAnd_13_14", q13.and q14, q9, .«open»⟩,
  ⟨"cOr_2_4", q2.or q4, q4, .proved⟩,
  ⟨"cOr_2_5", q2.or q5, q5, .proved⟩,
  ⟨"cOr_2_6", q2.or q6, q6, .proved⟩,
  ⟨"cOr_2_7", q2.or q7, q7, .proved⟩,
  ⟨"cOr_2_8", q2.or q8, q8, .proved⟩,
  ⟨"cOr_2_9", q2.or q9, q9, .proved⟩,
  ⟨"cOr_2_10", q2.or q10, q10, .proved⟩,
  ⟨"cOr_2_11", q2.or q11, q11, .proved⟩,
  ⟨"cOr_2_12", q2.or q12, q12, .proved⟩,
  ⟨"cOr_2_13", q2.or q13, q1, .«open»⟩,
  ⟨"cOr_2_14", q2.or q14, q9, .«open»⟩,
  ⟨"cOr_3_4", q3.or q4, q4, .proved⟩,
  ⟨"cOr_3_5", q3.or q5, q5, .proved⟩,
  ⟨"cOr_3_7", q3.or q7, q7, .proved⟩,
  ⟨"cOr_3_8", q3.or q8, q8, .proved⟩,
  ⟨"cOr_3_9", q3.or q9, q9, .proved⟩,
  ⟨"cOr_3_10", q3.or q10, q10, .proved⟩,
  ⟨"cOr_3_11", q3.or q11, q11, .proved⟩,
  ⟨"cOr_3_12", q3.or q12, q12, .proved⟩,
  ⟨"cOr_3_13", q3.or q13, q1, .«open»⟩,
  ⟨"cOr_3_14", q3.or q14, q9, .«open»⟩,
  ⟨"cOr_4_5", q4.or q5, q5, .proved⟩,
  ⟨"cOr_4_6", q4.or q6, q7, .proved⟩,
  ⟨"cOr_4_7", q4.or q7, q7, .proved⟩,
  ⟨"cOr_4_8", q4.or q8, q8, .proved⟩,
  ⟨"cOr_4_9", q4.or q9, q9, .proved⟩,
  ⟨"cOr_4_10", q4.or q10, q10, .proved⟩,
  ⟨"cOr_4_11", q4.or q11, q11, .proved⟩,
  ⟨"cOr_4_12", q4.or q12, q12, .proved⟩,
  ⟨"cOr_4_13", q4.or q13, q13, .proved⟩,
  ⟨"cOr_4_14", q4.or q14, q9, .«open»⟩,
  ⟨"cOr_5_7", q5.or q7, q9, .proved⟩,
  ⟨"cOr_5_8", q5.or q8, q1, .«open»⟩,
  ⟨"cOr_5_9", q5.or q9, q9, .proved⟩,
  ⟨"cOr_5_10", q5.or q10, q10, .proved⟩,
  ⟨"cOr_5_11", q5.or q11, q11, .proved⟩,
  ⟨"cOr_5_12", q5.or q12, q12, .proved⟩,
  ⟨"cOr_5_13", q5.or q13, q13, .proved⟩,
  ⟨"cOr_5_14", q5.or q14, q9, .«open»⟩,
  ⟨"cOr_6_7", q6.or q7, q7, .proved⟩,
  ⟨"cOr_6_8", q6.or q8, q8, .proved⟩,
  ⟨"cOr_6_9", q6.or q9, q9, .proved⟩,
  ⟨"cOr_6_11", q6.or q11, q11, .proved⟩,
  ⟨"cOr_6_12", q6.or q12, q12, .proved⟩,
  ⟨"cOr_6_13", q6.or q13, q1, .«open»⟩,
  ⟨"cOr_6_14", q6.or q14, q9, .«open»⟩,
  ⟨"cOr_7_8", q7.or q8, q8, .proved⟩,
  ⟨"cOr_7_9", q7.or q9, q9, .proved⟩,
  ⟨"cOr_7_10", q7.or q10, q11, .proved⟩,
  ⟨"cOr_7_11", q7.or q11, q11, .proved⟩,
  ⟨"cOr_7_12", q7.or q12, q12, .proved⟩,
  ⟨"cOr_7_13", q7.or q13, q1, .«open»⟩,
  ⟨"cOr_7_14", q7.or q14, q9, .«open»⟩,
  ⟨"cOr_8_9", q8.or q9, q1, .«open»⟩,
  ⟨"cOr_8_10", q8.or q10, q1, .«open»⟩,
  ⟨"cOr_8_11", q8.or q11, q1, .«open»⟩,
  ⟨"cOr_8_12", q8.or q12, q1, .«open»⟩,
  ⟨"cOr_8_13", q8.or q13, q1, .«open»⟩,
  ⟨"cOr_8_14", q8.or q14, q1, .«open»⟩,
  ⟨"cOr_9_10", q9.or q10, q11, .proved⟩,
  ⟨"cOr_9_11", q9.or q11, q11, .proved⟩,
  ⟨"cOr_9_12", q9.or q12, q12, .proved⟩,
  ⟨"cOr_9_13", q9.or q13, q1, .«open»⟩,
  ⟨"cOr_9_14", q9.or q14, q9, .«open»⟩,
  ⟨"cOr_10_11", q10.or q11, q11, .proved⟩,
  ⟨"cOr_10_12", q10.or q12, q1, .«open»⟩,
  ⟨"cOr_10_13", q10.or q13, q1, .«open»⟩,
  ⟨"cOr_10_14", q10.or q14, q1, .«open»⟩,
  ⟨"cOr_11_12", q11.or q12, q1, .«open»⟩,
  ⟨"cOr_11_13", q11.or q13, q1, .«open»⟩,
  ⟨"cOr_11_14", q11.or q14, q1, .«open»⟩,
  ⟨"cOr_12_13", q12.or q13, q1, .«open»⟩,
  ⟨"cOr_12_14", q12.or q14, q9, .«open»⟩,
  ⟨"cOr_13_14", q13.or q14, q1, .«open»⟩,
  ⟨"cImp_2_3", q2.ifThen q3, q3, .proved⟩,
  ⟨"cImp_2_4", q2.ifThen q4, q1, .proved⟩,
  ⟨"cImp_2_5", q2.ifThen q5, q1, .proved⟩,
  ⟨"cImp_2_6", q2.ifThen q6, q1, .proved⟩,
  ⟨"cImp_2_7", q2.ifThen q7, q1, .proved⟩,
  ⟨"cImp_2_8", q2.ifThen q8, q1, .proved⟩,
  ⟨"cImp_2_9", q2.ifThen q9, q1, .proved⟩,
  ⟨"cImp_2_10", q2.ifThen q10, q1, .proved⟩,
  ⟨"cImp_2_11", q2.ifThen q11, q1, .proved⟩,
  ⟨"cImp_2_12", q2.ifThen q12, q1, .proved⟩,
  ⟨"cImp_2_13", q2.ifThen q13, q1, .proved⟩,
  ⟨"cImp_2_14", q2.ifThen q14, q1, .proved⟩,
  ⟨"cImp_3_2", q3.ifThen q2, q6, .proved⟩,
  ⟨"cImp_3_4", q3.ifThen q4, q1, .proved⟩,
  ⟨"cImp_3_5", q3.ifThen q5, q1, .proved⟩,
  ⟨"cImp_3_6", q3.ifThen q6, q6, .proved⟩,
  ⟨"cImp_3_7", q3.ifThen q7, q1, .proved⟩,
  ⟨"cImp_3_8", q3.ifThen q8, q1, .proved⟩,
  ⟨"cImp_3_9", q3.ifThen q9, q1, .proved⟩,
  ⟨"cImp_3_10", q3.ifThen q10, q1, .proved⟩,
  ⟨"cImp_3_11", q3.ifThen q11, q1, .proved⟩,
  ⟨"cImp_3_12", q3.ifThen q12, q1, .proved⟩,
  ⟨"cImp_3_13", q3.ifThen q13, q1, .proved⟩,
  ⟨"cImp_3_14", q3.ifThen q14, q1, .proved⟩,
  ⟨"cImp_4_0", q4.ifThen q0, q0, .proved⟩,
  ⟨"cImp_4_2", q4.ifThen q2, q6, .proved⟩,
  ⟨"cImp_4_3", q4.ifThen q3, q3, .proved⟩,
  ⟨"cImp_4_5", q4.ifThen q5, q1, .proved⟩,
  ⟨"cImp_4_6", q4.ifThen q6, q6, .proved⟩,
  ⟨"cImp_4_7", q4.ifThen q7, q1, .proved⟩,
  ⟨"cImp_4_8", q4.ifThen q8, q1, .proved⟩,
  ⟨"cImp_4_9", q4.ifThen q9, q1, .proved⟩,
  ⟨"cImp_4_10", q4.ifThen q10, q1, .proved⟩,
  ⟨"cImp_4_11", q4.ifThen q11, q1, .proved⟩,
  ⟨"cImp_4_12", q4.ifThen q12, q1, .proved⟩,
  ⟨"cImp_4_13", q4.ifThen q13, q1, .proved⟩,
  ⟨"cImp_4_14", q4.ifThen q14, q1, .proved⟩,
  ⟨"cImp_5_0", q5.ifThen q0, q0, .proved⟩,
  ⟨"cImp_5_2", q5.ifThen q2, q6, .proved⟩,
  ⟨"cImp_5_3", q5.ifThen q3, q3, .proved⟩,
  ⟨"cImp_5_6", q5.ifThen q6, q6, .proved⟩,
  ⟨"cImp_5_7", q5.ifThen q7, q8, .proved⟩,
  ⟨"cImp_5_8", q5.ifThen q8, q8, .proved⟩,
  ⟨"cImp_5_9", q5.ifThen q9, q1, .proved⟩,
  ⟨"cImp_5_10", q5.ifThen q10, q1, .proved⟩,
  ⟨"cImp_5_11", q5.ifThen q11, q1, .proved⟩,
  ⟨"cImp_5_12", q5.ifThen q12, q1, .proved⟩,
  ⟨"cImp_5_13", q5.ifThen q13, q1, .proved⟩,
  ⟨"cImp_5_14", q5.ifThen q14, q1, .proved⟩,
  ⟨"cImp_6_0", q6.ifThen q0, q3, .proved⟩,
  ⟨"cImp_6_3", q6.ifThen q3, q3, .proved⟩,
  ⟨"cImp_6_4", q6.ifThen q4, q10, .proved⟩,
  ⟨"cImp_6_5", q6.ifThen q5, q10, .proved⟩,
  ⟨"cImp_6_7", q6.ifThen q7, q1, .proved⟩,
  ⟨"cImp_6_8", q6.ifThen q8, q1, .proved⟩,
  ⟨"cImp_6_9", q6.ifThen q9, q1, .proved⟩,
  ⟨"cImp_6_10", q6.ifThen q10, q10, .proved⟩,
  ⟨"cImp_6_11", q6.ifThen q11, q1, .proved⟩,
  ⟨"cImp_6_12", q6.ifThen q12, q1, .proved⟩,
  ⟨"cImp_6_13", q6.ifThen q13, q1, .proved⟩,
  ⟨"cImp_6_14", q6.ifThen q14, q1, .proved⟩,
  ⟨"cImp_7_0", q7.ifThen q0, q0, .proved⟩,
  ⟨"cImp_7_2", q7.ifThen q2, q2, .proved⟩,
  ⟨"cImp_7_3", q7.ifThen q3, q3, .proved⟩,
  ⟨"cImp_7_4", q7.ifThen q4, q10, .proved⟩,
  ⟨"cImp_7_5", q7.ifThen q5, q10, .proved⟩,
  ⟨"cImp_7_6", q7.ifThen q6, q6, .proved⟩,
  ⟨"cImp_7_8", q7.ifThen q8, q1, .proved⟩,
  ⟨"cImp_7_9", q7.ifThen q9, q1, .proved⟩,
  ⟨"cImp_7_10", q7.ifThen q10, q10, .proved⟩,
  ⟨"cImp_7_11", q7.ifThen q11, q1, .proved⟩,
  ⟨"cImp_7_12", q7.ifThen q12, q1, .proved⟩,
  ⟨"cImp_7_13", q7.ifThen q13, q1, .proved⟩,
  ⟨"cImp_7_14", q7.ifThen q14, q1, .proved⟩,
  ⟨"cImp_8_0", q8.ifThen q0, q0, .proved⟩,
  ⟨"cImp_8_2", q8.ifThen q2, q2, .proved⟩,
  ⟨"cImp_8_3", q8.ifThen q3, q3, .proved⟩,
  ⟨"cImp_8_4", q8.ifThen q4, q5, .«open»⟩,
  ⟨"cImp_8_5", q8.ifThen q5, q5, .«open»⟩,
  ⟨"cImp_8_6", q8.ifThen q6, q6, .proved⟩,
  ⟨"cImp_8_7", q8.ifThen q7, q9, .«open»⟩,
  ⟨"cImp_8_9", q8.ifThen q9, q9, .«open»⟩,
  ⟨"cImp_8_10", q8.ifThen q10, q10, .«open»⟩,
  ⟨"cImp_8_11", q8.ifThen q11, q1, .«open»⟩,
  ⟨"cImp_8_12", q8.ifThen q12, q9, .«open»⟩,
  ⟨"cImp_8_13", q8.ifThen q13, q1, .proved⟩,
  ⟨"cImp_8_14", q8.ifThen q14, q9, .«open»⟩,
  ⟨"cImp_9_0", q9.ifThen q0, q0, .proved⟩,
  ⟨"cImp_9_2", q9.ifThen q2, q2, .proved⟩,
  ⟨"cImp_9_3", q9.ifThen q3, q3, .proved⟩,
  ⟨"cImp_9_4", q9.ifThen q4, q0, .refuted⟩,
  ⟨"cImp_9_5", q9.ifThen q5, q10, .proved⟩,
  ⟨"cImp_9_6", q9.ifThen q6, q6, .proved⟩,
  ⟨"cImp_9_7", q9.ifThen q7, q8, .proved⟩,
  ⟨"cImp_9_8", q9.ifThen q8, q8, .«open»⟩,
  ⟨"cImp_9_10", q9.ifThen q10, q10, .proved⟩,
  ⟨"cImp_9_11", q9.ifThen q11, q1, .proved⟩,
  ⟨"cImp_9_12", q9.ifThen q12, q1, .proved⟩,
  ⟨"cImp_9_13", q9.ifThen q13, q1, .proved⟩,
  ⟨"cImp_9_14", q9.ifThen q14, q1, .proved⟩,
  ⟨"cImp_10_0", q10.ifThen q0, q0, .proved⟩,
  ⟨"cImp_10_2", q10.ifThen q2, q6, .proved⟩,
  ⟨"cImp_10_3", q10.ifThen q3, q3, .proved⟩,
  ⟨"cImp_10_4", q10.ifThen q4, q7, .«open»⟩,
  ⟨"cImp_10_6", q10.ifThen q6, q6, .proved⟩,
  ⟨"cImp_10_7", q10.ifThen q7, q7, .«open»⟩,
  ⟨"cImp_10_8", q10.ifThen q8, q8, .«open»⟩,
  ⟨"cImp_10_9", q10.ifThen q9, q9, .«open»⟩,
  ⟨"cImp_10_11", q10.ifThen q11, q1, .proved⟩,
  ⟨"cImp_10_12", q10.ifThen q12, q9, .«open»⟩,
  ⟨"cImp_10_13", q10.ifThen q13, q1, .«open»⟩,
  ⟨"cImp_10_14", q10.ifThen q14, q9, .«open»⟩,
  ⟨"cImp_11_0", q11.ifThen q0, q0, .proved⟩,
  ⟨"cImp_11_2", q11.ifThen q2, q2, .proved⟩,
  ⟨"cImp_11_3", q11.ifThen q3, q3, .proved⟩,
  ⟨"cImp_11_4", q11.ifThen q4, q4, .«open»⟩,
  ⟨"cImp_11_5", q11.ifThen q5, q5, .proved⟩,
  ⟨"cImp_11_6", q11.ifThen q6, q6, .proved⟩,
  ⟨"cImp_11_7", q11.ifThen q7, q7, .«open»⟩,
  ⟨"cImp_11_8", q11.ifThen q8, q8, .«open»⟩,
  ⟨"cImp_11_9", q11.ifThen q9, q9, .«open»⟩,
  ⟨"cImp_11_10", q11.ifThen q10, q10, .proved⟩,
  ⟨"cImp_11_12", q11.ifThen q12, q9, .«open»⟩,
  ⟨"cImp_11_13", q11.ifThen q13, q1, .«open»⟩,
  ⟨"cImp_11_14", q11.ifThen q14, q9, .«open»⟩,
  ⟨"cImp_12_0", q12.ifThen q0, q0, .proved⟩,
  ⟨"cImp_12_2", q12.ifThen q2, q2, .proved⟩,
  ⟨"cImp_12_3", q12.ifThen q3, q3, .proved⟩,
  ⟨"cImp_12_4", q12.ifThen q4, q0, .refuted⟩,
  ⟨"cImp_12_5", q12.ifThen q5, q10, .proved⟩,
  ⟨"cImp_12_6", q12.ifThen q6, q6, .proved⟩,
  ⟨"cImp_12_7", q12.ifThen q7, q8, .«open»⟩,
  ⟨"cImp_12_8", q12.ifThen q8, q8, .«open»⟩,
  ⟨"cImp_12_9", q12.ifThen q9, q1, .«open»⟩,
  ⟨"cImp_12_10", q12.ifThen q10, q10, .proved⟩,
  ⟨"cImp_12_11", q12.ifThen q11, q1, .«open»⟩,
  ⟨"cImp_12_13", q12.ifThen q13, q1, .proved⟩,
  ⟨"cImp_12_14", q12.ifThen q14, q1, .proved⟩,
  ⟨"cImp_13_0", q13.ifThen q0, q0, .proved⟩,
  ⟨"cImp_13_2", q13.ifThen q2, q2, .proved⟩,
  ⟨"cImp_13_3", q13.ifThen q3, q3, .proved⟩,
  ⟨"cImp_13_4", q13.ifThen q4, q4, .proved⟩,
  ⟨"cImp_13_5", q13.ifThen q5, q5, .«open»⟩,
  ⟨"cImp_13_6", q13.ifThen q6, q6, .proved⟩,
  ⟨"cImp_13_7", q13.ifThen q7, q7, .proved⟩,
  ⟨"cImp_13_8", q13.ifThen q8, q8, .«open»⟩,
  ⟨"cImp_13_9", q13.ifThen q9, q9, .«open»⟩,
  ⟨"cImp_13_10", q13.ifThen q10, q10, .proved⟩,
  ⟨"cImp_13_11", q13.ifThen q11, q1, .«open»⟩,
  ⟨"cImp_13_12", q13.ifThen q12, q9, .«open»⟩,
  ⟨"cImp_13_14", q13.ifThen q14, q9, .«open»⟩,
  ⟨"cImp_14_0", q14.ifThen q0, q0, .proved⟩,
  ⟨"cImp_14_2", q14.ifThen q2, q2, .proved⟩,
  ⟨"cImp_14_3", q14.ifThen q3, q3, .proved⟩,
  ⟨"cImp_14_4", q14.ifThen q4, q0, .refuted⟩,
  ⟨"cImp_14_5", q14.ifThen q5, q10, .«open»⟩,
  ⟨"cImp_14_6", q14.ifThen q6, q6, .proved⟩,
  ⟨"cImp_14_7", q14.ifThen q7, q8, .«open»⟩,
  ⟨"cImp_14_8", q14.ifThen q8, q8, .«open»⟩,
  ⟨"cImp_14_9", q14.ifThen q9, q1, .«open»⟩,
  ⟨"cImp_14_10", q14.ifThen q10, q10, .proved⟩,
  ⟨"cImp_14_11", q14.ifThen q11, q1, .«open»⟩,
  ⟨"cImp_14_12", q14.ifThen q12, q1, .«open»⟩,
  ⟨"cImp_14_13", q14.ifThen q13, q1, .«open»⟩,
  ⟨"cBox_1", q1.somehow, q1, .proved⟩,
  ⟨"cBox_4", q4.somehow, q5, .proved⟩,
  ⟨"cBox_6", q6.somehow, q6, .proved⟩,
  ⟨"cBox_9", q9.somehow, q12, .proved⟩,
  ⟨"cBox_10", q10.somehow, q10, .proved⟩,
  ⟨"cBox_11", q11.somehow, q1, .«open»⟩,
  ⟨"cBox_14", q14.somehow, q9, .«open»⟩
  ]

/-- The two search goals a cell gives rise to: refuting either direction
refutes the cell (`FRJ.not_interd_of_provable`, `..._of_provable'`). -/
def Cell.goals (c : Cell) : List (String × PLLFormula) :=
  [(c.name ++ "→", .ifThen c.lhs c.rhs), (c.name ++ "←", .ifThen c.rhs c.lhs)]

def Cell.forms (c : Cell) : List (String × FRJ.Form) :=
  c.goals.map (fun p => (p.1, FRJ.ofPLL p.2))

def count (s : Status) : Nat := (cells.filter (fun c => c.status == s)).length

end RNBank
