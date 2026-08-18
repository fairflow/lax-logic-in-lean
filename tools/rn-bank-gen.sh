#!/bin/sh
# Regenerate wip/rnBank.lean from the certified dictionary wip/rnDict.lean.
#
#   sh tools/rn-bank-gen.sh > wip/rnBank.lean
#
# The bank is the oracle for the FRJ(◯) countermodel search: every RN(◯,{})
# dictionary cell, tagged with what the repository already knows about it.
#
#   proved   — kernel-checked `Interd` in wip/rnDict.lean.  The search must
#              NOT refute either direction; a refutation is an ENGINE BUG.
#   refuted  — `sorry` in rnDict, and eliminated by the exhaustive ≤4-world
#              battery (docs/rn-dictionary-status.md).  At least one
#              direction MUST be refutable; a miss is an incompleteness datum.
#   open     — `sorry` in rnDict, and NOT refuted at ≤4 worlds.  The targets.
#
# Keep the refuted list in step with docs/rn-dictionary-status.md.
set -e
SRC=${1:-wip/rnDict.lean}
REFUTED="cAnd_8_10 cImp_9_4 cImp_12_4 cImp_14_4"

cat <<'HDR'
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

HDR

sed -n '/^def q0 : PLLFormula/,/^def repsL/p' "$SRC" | grep '^def q'

cat <<'MID'

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
MID

grep "^theorem c" "$SRC" | sed 's/^theorem //' | awk -v refuted="$REFUTED" -F' : Interd ' '
BEGIN { n = split(refuted, r, " "); for (i = 1; i <= n; i++) ref[r[i]] = 1 }
{
  name = $1; rest = $2;
  st = (rest ~ /sorry/) ? "«open»" : "proved";
  if (name in ref) st = "refuted";
  sub(/ :=.*$/, "", rest);
  k = split(rest, a, " ");
  tgt = a[k];
  lhs = "";
  for (i = 1; i < k; i++) lhs = lhs (i > 1 ? " " : "") a[i];
  sub(/^\(/, "", lhs); sub(/\)$/, "", lhs);
  printf "  ⟨\"%s\", %s, %s, .%s⟩,\n", name, lhs, tgt, st
}' | sed '$ s/,$//'

cat <<'FTR'
  ]

/-- The two search goals a cell gives rise to: refuting either direction
refutes the cell (`FRJ.not_interd_of_provable`, `..._of_provable'`). -/
def Cell.goals (c : Cell) : List (String × PLLFormula) :=
  [(c.name ++ "→", .ifThen c.lhs c.rhs), (c.name ++ "←", .ifThen c.rhs c.lhs)]

def Cell.forms (c : Cell) : List (String × FRJ.Form) :=
  c.goals.map (fun p => (p.1, FRJ.ofPLL p.2))

def count (s : Status) : Nat := (cells.filter (fun c => c.status == s)).length

end RNBank
FTR
