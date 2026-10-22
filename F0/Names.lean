import LaxLogic.PLL.Syntax.Formula
import Meta.Audit

/-!
# Family names for the classes of RN(◯,∅)

2026-10-22, at Matthew's direction (METHOD-F0 §1 E): the explorer does not
present the classes under the historical ρ-labels; a class is named by
its first membership in a fixed list of formula families.  The families
and the naming rule are Lean definitions; a different scheme is a change
to this module only.  The default scheme, until Matthew rules otherwise:

* the families, each a function `ℕ → PLLFormula`, transcribed from
  definitions in `wip/` (which the F0 library must not import; the
  transcription of `t` is checked against the original in
  `tools/F0/RNSourceGate.lean`, outside the library):
  - `t n`: the Rieger–Nishimura element `rn n` under `p := ◯⊥`.  Original
    `PLLND.RNEmbed.rnSub n := embed (rn n)` (`wip/rnEmbed.lean`, with `rnP`
    and `rn`): `rn 0 = ⊥`, `rnP 0 = (p, ¬p)`,
    `rnP (k+1) = (a ∨ b, (a ∨ b) ↠ a)` where `(a, b) = rnP k`, and
    `rn (n+1)` is the first component of `rnP (n/2)` when `n` is even, the
    second when `n` is odd.  Here `p := ◯⊥` is applied in the recursion.
  - `c k = ◯t(2k+1)`, the ◯-chain (original `chainF`, `wip/chainStrict.lean`);
  - `g k = c k ↠ t(2k+1)`, the gaps (original `gap`, `wip/gapWidth.lean`);
  - `s k = c k ∨ t(2k+2)` (original `sC`, `wip/families.lean`);
  - `r k = t(2k+4) ↠ c k` (original `rC`, `wip/families.lean`);
  - `w k = g k ∧ t(2k+4)`, the zigzag (original `wC`, `wip/wscout.lean`);
  plus `⊥` and `⊤`, which keep their symbols;
* the order of preference `⊥, ⊤, t, c, g, s, r, w` (`Fam.rank`), and
  within a family the smallest index;
* the search domain (`Fam.indices`): `t 0 … t 12`, and `k = 1 … 4` for
  `c, g, s, r, w` (the old explorer indexes these from `k = 1`);
* `nameOf`: of a class's certified memberships, the first in that order;
  `none` when there is none (the class is unnamed; no number is invented).

Membership is certified elsewhere, fact by fact (`F0/Families`, two
tableau facts per membership); this module only defines the terms and
chooses among memberships.  The ρ-indices remain internal ids
(`RhoOrder.rhoF`), shown only as legacy labels.
-/

namespace F0

/-- `◯⊥`, the generator. -/
def ob : PLLFormula := .somehow .falsePLL

/-- The pairs `(t (2k+1), t (2k+2))`: `rnP k` of `wip/rnEmbed.lean` under
`p := ◯⊥`. -/
def tP : Nat → PLLFormula × PLLFormula
  | 0 => (ob, .ifThen ob .falsePLL)
  | k + 1 => ((tP k).1.or (tP k).2, ((tP k).1.or (tP k).2).ifThen (tP k).1)

/-- The Rieger–Nishimura element `rn n` under `p := ◯⊥`
(`PLLND.RNEmbed.rnSub n`, `wip/rnEmbed.lean`). -/
def t : Nat → PLLFormula
  | 0 => .falsePLL
  | n + 1 => if n % 2 = 0 then (tP (n / 2)).1 else (tP (n / 2)).2

/-- `c k = ◯t(2k+1)` (`chainF`). -/
def c (k : Nat) : PLLFormula := (t (2 * k + 1)).somehow

/-- `g k = c k ↠ t(2k+1)` (`gap`). -/
def g (k : Nat) : PLLFormula := (c k).ifThen (t (2 * k + 1))

/-- `s k = c k ∨ t(2k+2)` (`sC`). -/
def s (k : Nat) : PLLFormula := (c k).or (t (2 * k + 2))

/-- `r k = t(2k+4) ↠ c k` (`rC`). -/
def r (k : Nat) : PLLFormula := (t (2 * k + 4)).ifThen (c k)

/-- `w k = g k ∧ t(2k+4)` (`wC`). -/
def w (k : Nat) : PLLFormula := (g k).and (t (2 * k + 4))

/-- The families, in the order of preference. -/
inductive Fam where
  | bot | top | t | c | g | s | r | w
  deriving DecidableEq, Repr

namespace Fam

/-- The order of preference. -/
def rank : Fam → Nat
  | bot => 0 | top => 1 | t => 2 | c => 3 | g => 4 | s => 5 | r => 6 | w => 7

/-- The member of a family at an index (`⊥` and `⊤` ignore it). -/
def term : Fam → Nat → PLLFormula
  | bot, _ => .falsePLL
  | top, _ => .ifThen .falsePLL .falsePLL
  | t, n => F0.t n
  | c, k => F0.c k
  | g, k => F0.g k
  | s, k => F0.s k
  | r, k => F0.r k
  | w, k => F0.w k

/-- The search domain of each family. -/
def indices : Fam → List Nat
  | bot => [0] | top => [0]
  | t => List.range 13
  | _ => List.range' 1 4

/-- All families, in the order of preference. -/
def all : List Fam := [bot, top, t, c, g, s, r, w]

/-- The family letter. -/
def tag : Fam → String
  | bot => "bot" | top => "top" | t => "t" | c => "c" | g => "g"
  | s => "s" | r => "r" | w => "w"

/-- The displayed name of a member: `⊥`, `⊤`, or the letter and the index. -/
def label (f : Fam) (n : Nat) : String :=
  match f with
  | bot => "⊥"
  | top => "⊤"
  | _ => f.tag ++ toString n

/-- The family's word, for display (Matthew, 2026-10-22: letters are hard
to remember); `⊥` and `⊤` keep their symbols. -/
def word : Fam → String
  | bot => "⊥" | top => "⊤"
  | t => "rung" | c => "lax rung" | g => "gap" | s => "lax join" | r => "lax arrow" | w => "zigzag"

/-- The long name of a member: the word and the index, e.g. `lax rung 1`. -/
def long (f : Fam) (n : Nat) : String :=
  match f with
  | bot => "⊥"
  | top => "⊤"
  | _ => f.word ++ " " ++ toString n

/-- The Lean constant of the family. -/
def leanName : Fam → String
  | bot => "PLLFormula.falsePLL" | top => "PLLFormula.truePLL"
  | t => "F0.t" | c => "F0.c" | g => "F0.g" | s => "F0.s" | r => "F0.r" | w => "F0.w"

/-- The definition, in library notation, for display: one row per family,
kept next to the definitions; `F0/NamesGates.lean` states each row as a
theorem (`c_def` … `w_def`, `t_rec`), so the two cannot drift apart
unnoticed. -/
def definition : Fam → String
  | bot => "⊥"
  | top => "⊤ = ⊥ ↠ ⊥"
  | t => "t n = rn n [p := ◯⊥]: t0 = ⊥, t1 = ◯⊥, t2 = ¬◯⊥, t(2k+3) = t(2k+1) ∨ t(2k+2), t(2k+4) = t(2k+1) ∨ t(2k+2) ↠ t(2k+1)"
  | c => "c k = ◯t(2k+1)"
  | g => "g k = c k ↠ t(2k+1)"
  | s => "s k = c k ∨ t(2k+2)"
  | r => "r k = t(2k+4) ↠ c k"
  | w => "w k = g k ∧ t(2k+4)"

/-- Every (family, index) searched, in the order of preference. -/
def domain : List (Fam × Nat) := all.flatMap fun f => (indices f).map (f, ·)

end Fam

/-- `a` is preferred to `b`: earlier family, or the same family and a
smaller index. -/
def prefLt (a b : Fam × Nat) : Bool :=
  a.1.rank < b.1.rank || (a.1.rank == b.1.rank && a.2 < b.2)

/-- The name of a class: of its certified memberships, the preferred one;
`none` when there is none. -/
def nameOf : List (Fam × Nat) → Option (Fam × Nat)
  | [] => none
  | m :: ms => some (ms.foldl (fun best x => if prefLt x best then x else best) m)

/-! ## Compound names, for the classes with no family membership

2026-10-22, at Matthew's request ("give them evocative names").  A class
with no certified family membership is named by the simplest certified
expression `x ∘ y` (or `◯x`) whose operands are classes with family names
and whose operation-table cell lands in the class.  Simplest: a term of a
textbook shape first (`Compound.shaped`, below), then the operation in the
order `◯, ∧, ∨, ↠` (`COp.rank`), then the first operand, then the second,
each in the name order (`prefLt`).  A compound name only
fills a class that `nameOf` leaves unnamed.  The certificate (two tableau
facts, `F0/Compound`) is stated on the family terms, so the name's Lean
term (`Compound.term`) is what is proved. -/

/-- The operations of a compound name. -/
inductive COp where
  | box | and | or | imp
  deriving DecidableEq, Repr

namespace COp

/-- The order of simplicity. -/
def rank : COp → Nat
  | box => 0 | and => 1 | or => 2 | imp => 3

def sym : COp → String
  | box => "◯" | and => "∧" | or => "∨" | imp => "↠"

def tag : COp → String
  | box => "box" | and => "and" | or => "or" | imp => "imp"

end COp

/-- A compound name `x ∘ y`, or `◯x` (then `y` is ignored; by convention
`(bot, 0)`). -/
structure Compound where
  op : COp
  x : Fam × Nat
  y : Fam × Nat
  deriving DecidableEq, Repr

namespace Compound

/-- The formula the name denotes, over the family terms. -/
def term (k : Compound) : PLLFormula :=
  match k.op with
  | .box => (k.x.1.term k.x.2).somehow
  | .and => (k.x.1.term k.x.2).and (k.y.1.term k.y.2)
  | .or => (k.x.1.term k.x.2).or (k.y.1.term k.y.2)
  | .imp => (k.x.1.term k.x.2).ifThen (k.y.1.term k.y.2)

/-- The displayed name, e.g. `c1 ∨ g1`, `◯t5`. -/
def label (k : Compound) : String :=
  match k.op with
  | .box => "◯" ++ k.x.1.label k.x.2
  | o => k.x.1.label k.x.2 ++ " " ++ o.sym ++ " " ++ k.y.1.label k.y.2

/-- The long name, in words, e.g. `lax rung 1 ∨ gap 1`. -/
def long (k : Compound) : String :=
  match k.op with
  | .box => "◯" ++ k.x.1.long k.x.2
  | o => k.x.1.long k.x.2 ++ " " ++ o.sym ++ " " ++ k.y.1.long k.y.2

end Compound

/-! ## Textbook shapes

A fixed table of two shapes, recognised syntactically on a name's term
(its formula, the families unfolded):
* `x ∨ (x ↠ y)`: excluded middle for `x` relative to `y`;
* `(x ↠ y) ↠ x`: Peirce's antecedent. -/

inductive Shape where
  | exclMid (x y : PLLFormula)
  | peirceAnt (x y : PLLFormula)
  deriving DecidableEq, Repr

def shapeOf : PLLFormula → Option Shape
  | .or x (.ifThen x' y) => if x = x' then some (.exclMid x y) else none
  | .ifThen (.ifThen x y) x' => if x = x' then some (.peirceAnt x y) else none
  | _ => none

/-- The family member a formula is, syntactically (the preferred one), if any. -/
def labelOf? (φ : PLLFormula) : Option (Fam × Nat) :=
  Fam.domain.find? fun (f, n) => f.term n == φ

/-- The shape's kind, for display. -/
def Shape.kind : Shape → String
  | .exclMid .. => "excluded_middle"
  | .peirceAnt .. => "peirce_antecedent"

/-- The nickname a shape gives, from the displayed operands; the only
source of nicknames. -/
def Shape.nickname (s : Shape) (x y : String) : String :=
  match s with
  | .exclMid .. => "excluded middle for " ++ x ++ " over " ++ y
  | .peirceAnt .. => "Peirce for " ++ x ++ " over " ++ y

/-! ## The order of compound names

2026-10-22, at Matthew's direction: a compound whose term (the families
unfolded) has a textbook shape (`shapeOf`) comes before every compound
without one; among compounds with the same shape status, the operation
in the order `◯, ∧, ∨, ↠`, then the first operand, then the second, each
in the name order (`prefLt`). -/

/-- The compound's term has a textbook shape. -/
def Compound.shaped (k : Compound) : Bool := (shapeOf k.term).isSome

/-- `a` is simpler than `b`, ignoring shapes. -/
def compoundPlainLt (a b : Compound) : Bool :=
  a.op.rank < b.op.rank ||
    (a.op.rank == b.op.rank && (prefLt a.x b.x || (a.x == b.x && prefLt a.y b.y)))

/-- `a` is preferred to `b`: shaped before unshaped, then `compoundPlainLt`. -/
def compoundLt (a b : Compound) : Bool :=
  (a.shaped && !b.shaped) || (a.shaped == b.shaped && compoundPlainLt a b)

/-- The compound name of a class: of its certified candidates, the
preferred (`compoundLt`); `none` when there is none. -/
def compoundOf : List Compound → Option Compound
  | [] => none
  | m :: ms => some (ms.foldl (fun best x => if compoundLt x best then x else best) m)

end F0

#axioms_within F0.t [propext, Quot.sound]
#axioms_within F0.c [propext, Quot.sound]
#axioms_within F0.g [propext, Quot.sound]
#axioms_within F0.s [propext, Quot.sound]
#axioms_within F0.r [propext, Quot.sound]
#axioms_within F0.w [propext, Quot.sound]
#axioms_within F0.Fam.term [propext, Quot.sound]
#axioms_within F0.Fam.domain [propext, Quot.sound]
#axioms_within F0.nameOf [propext, Quot.sound]
#axioms_within F0.Compound.term [propext, Quot.sound]
#axioms_within F0.compoundOf [propext, Quot.sound]
#axioms_within F0.shapeOf [propext, Quot.sound]
#axioms_within F0.labelOf? [propext, Quot.sound]
