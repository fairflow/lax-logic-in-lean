import wip.f0Structure
import Meta.Audit

/-!
# `↓t6` is infinite: a Rieger–Nishimura ladder in `◯¬◯⊥`, relativised

F0 is the Lindenbaum algebra of the variable-free PLL formulas; `t n = rnSub n`,
`e = t1 = ◯⊥`, and `↓a` is the set of classes below `a`, a PLL algebra under
`∧`, `∨`, `(x ↠ y) ∧ a` and `◯x ∧ a` (the quotient of F0 by the filter of `a`).

## The quotient (`t6_regular`)

    t6 = t5 ↠ t3 = (¬e ∨ ¬¬e) ↠ (e ∨ ¬e)   ⊣⊢   ¬¬e ↠ e,

so `↓t6` is variable-free PLL with `◯⊥` regular (`¬¬◯⊥ = ◯⊥`).

## Fragment first (CLAUDE.md rule 8)

In the ◯-free instance, the Rieger–Nishimura algebra of one variable `p`
divided by `¬¬p = p` has five elements, `⊥, p, ¬p, p ∨ ¬p, ⊤` (equivalently
`↓rn 6 = {rn 0, rn 1, rn 2, rn 3, rn 6}`).  So an infinite family below `t6`
must use `◯` beyond the substitution `p := ◯⊥`.  (Textbook; not mechanised
here.)

## The mechanism

    u = ◯¬◯⊥ = ◯t2 ≥ t3       (`t3_le_u`: `e ⊢ ◯¬e` by `◯`-monotonicity, `¬e ⊢ ◯¬e` by the unit)

lives in the interval `[t3, ⊤]`, a Heyting algebra with bottom `t3`, the same
`∧`, `∨`, `↠`, and relative negation `x ↦ x ↠ t3`.  Relativise the
Rieger–Nishimura rungs: `rel` reads `p` as `u` and `⊥` as `t3`, so

    rel (rn 1) = u,   rel (rn 2) = u ↠ t3,   rel (rn (2k+3)) = rel (rn (2k+1)) ∨ rel (rn (2k+2)), …

The generator's classes of round 3 are these rungs, up to `⊣⊢` and `∧ t6`
(designed cells, kernel-checked): class 6 is `rel (rn 2) ∧ t6` (`cell_m6`),
class 9 is `rel (rn 4) ∧ t6` (`cell_m9`); by the generator's construction
classes 4, 8, 10, 11 are `rel (rn 1)`, `rel (rn 3)`, `rel (rn 6)`,
`rel (rn 5)` (each `∧ t6`).

## The theorem (`t6_chain`, `t6_downset_infinite`)

With `x k = rel (rn (2k+1)) ∧ t6`:

    atomFree (x k),    x k ⊢ t6,    x k ⊢ x (k+1),    x (k+1) ⊬ x k,

an infinite strictly increasing chain below `t6`; so `↓t6` is infinite.  Since
`t6 ⊢ t n` for `n = 6, 7` and every `n ≥ 9` (`t6_le_rung`, rung order through
the substitution), conjecture C1 (`↓t n` finite for every `n`) is REFUTED at
all those `n` (`rung_downset_infinite`).  It holds for `n ≤ 5` (the tables of
`wip/f0Covers.lean`); `n = 8` is OPEN (`t6 ⊬ t8` by the rung order,
`rnSub_deriv_iff`, and `t8` fails on the ladder of `cmU`).

**The countermodel** (`cmU`): the RN ladder `lad n` (`n ∈ ℕ`, the order of
`ladder`) under three top worlds: `nE` (where `¬◯⊥` holds), `oE` (where `◯⊥`
holds, `oE Rₘ fl`) and the fallible `fl`, with the single extra modal edge
`lad 0 Rₘ nE`.  Then `e = {oE, fl}`, `¬e = {nE, fl}`, `t3 = {nE, oE, fl}`,
`t6` holds everywhere, and `u` holds on the ladder exactly at `lad 0`, as `p`
does on the RN ladder.  Every `rel A` (A ◯-free) holds at the three tops, so
the implications at ladder worlds see only the ladder, and
(`rel_transfer`)

    cmU, lad x ⊨ rel A   ⟺   ladder, x ⊨ A.

With `sat_rnP_cf`: `x k` holds at `lad x` iff `x ≤ k`.  Pins `[propext, Quot.sound]`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace T6

open SemUI RNEmbed
open PLLND.LaxInfinite (atomFree)

/-! ## The formulas -/

/-- `t6 = t5 ↠ t3`. -/
def t6F : PLLFormula := .ifThen t5 t3

theorem rnSub_6 : rnSub 6 = t6F := rfl

/-- `u = ◯¬◯⊥`. -/
def uF : PLLFormula := .somehow ne

/-- `¬¬◯⊥`. -/
def nne : PLLFormula := .ifThen ne .falsePLL

/-- `¬¬◯⊥ ↠ ◯⊥`: `◯⊥` is regular. -/
def regE : PLLFormula := .ifThen nne e

/-- The generator's classes 4, 6, 9 (cleaned up: `◯t2` for `◯((◯⊥∧t6 ↠ ⊥)∧t6)`,
`t3` for the join of classes 2 and 3). -/
def m4 : PLLFormula := .and uF t6F
def m6 : PLLFormula := .and (.ifThen m4 t3) t6F
def m9 : PLLFormula := .and (.ifThen m6 m4) t6F

/-- Relativised rungs 2, 3, 4 (`rel (rn 2)`, …). -/
def r2 : PLLFormula := .ifThen uF t3
def r3 : PLLFormula := .or uF r2
def r4 : PLLFormula := .ifThen r3 uF

/-- **Relativisation**: `p ↦ u`, every other atom and `⊥ ↦ t3`. -/
def rel : PLLFormula → PLLFormula
  | .prop a => if a = pv then uF else t3
  | .falsePLL => t3
  | .and A B => .and (rel A) (rel B)
  | .or A B => .or (rel A) (rel B)
  | .ifThen A B => .ifThen (rel A) (rel B)
  | .somehow A => .somehow (rel A)

theorem rel_rn2 : rel (rnP 0).2 = r2 := rfl
theorem rel_rn4 : rel (rnP 1).2 = r4 := rfl

/-! ## Designed cells (closed tableaux, checked by the kernel) -/

theorem t6_regular : Interd t6F regE :=
  interdTab (.impR t6F regE (.impL t5 t3 (.orR t3 t4 (.orR e ne (.impR nne e (.impL t5 t3 (.impL ne bot (.orR t3 t4 (.orR e ne (.boxR bot (.impL t5 t3 (.impL ne bot (.orR t3 t4 (.orR e ne (.boxLoc bot (.impR t3 e (.impL t5 t3 (.impL ne bot (.orL e ne (.impLoc e bot (.orR t3 t4 (.ax t3))) (.impL e bot (.ax ne) .bot)) .bot) (.orL e ne (.impL ne bot (.impLoc e bot (.ax e)) .bot) (.impL e bot (.impL ne bot (.ax ne) .bot) .bot))))))) .bot) (.orL e ne (.boxL bot .bot) (.impL e bot (.impL ne bot (.ax ne) .bot) .bot)))))) .bot) (.orL e ne (.impL ne bot (.impLoc e bot (.ax e)) .bot) (.impL e bot (.impL ne bot (.ax ne) .bot) .bot)))))) (.orL e ne (.impR nne e (.orL e ne (.impL ne bot (.impLoc e bot (.ax e)) .bot) (.impL e bot (.impL ne bot (.ax ne) .bot) .bot))) (.impL e bot (.impR nne e (.impL e bot (.orL e ne (.impL ne bot (.ax ne) .bot) (.impL ne bot (.ax ne) .bot)) .bot)) .bot))))
    (.impR regE t6F (.impL nne e (.impR t5 t3 (.impL nne e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.impLoc ne bot (.ax t3)) .bot)) (.impL t3 e (.orR e ne (.boxR bot (.impL nne e (.impL t3 e (.orL t3 t4 (.orL e ne (.boxL bot .bot) (.impL e bot (.boxLoc bot (.ax t3)) .bot)) (.orR e ne (.boxLoc bot (.impR ne bot (.impL nne e (.impL t3 e (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax t3) .bot)) (.impL e bot (.orR e ne (.ax ne)) .bot)) (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.ax e) .bot))) (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.ax e) .bot))))))) (.boxL bot .bot)) (.boxL bot .bot)))) (.orR e ne (.ax e)))) (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e))))) (.impR t5 t3 (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e))))))
    (by decide +kernel) (by decide +kernel)

theorem t3_le_u : Deriv [t3] uF :=
  derivTab (.impR t3 uF (.orL e ne (.boxR ne (.boxL bot .bot)) (.impL e bot (.boxR ne (.impL e bot (.orL e ne (.boxL bot .bot) (.boxLoc bot (.ax ne))) .bot)) .bot)))
    (by decide +kernel)

theorem cell_m6 : Interd m6 (.and r2 t6F) :=
  interdTab (.impR m6 (.and r2 t6F) (.andL (.ifThen m4 t3) t6F (.impL m4 t3 (.impL t5 t3 (.orR t3 t4 (.orR e ne (.andR uF t6F (.andR r2 t6F (.impR uF t3 (.impL t5 t3 (.impL m4 t3 (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.ax uF) (.ax t6F))) (.orL e ne (.andL (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3))) (.impL e bot (.andL (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3))) .bot))) (.orL e ne (.andL (.ifThen m4 t3) t6F (.ax t3)) (.impL e bot (.andL (.ifThen m4 t3) t6F (.ax t3)) .bot)))) (.ax t6F)) (.ax t6F)))) (.orL e ne (.andR uF t6F (.andR r2 t6F (.boxR ne (.boxL bot .bot)) (.ax t6F)) (.ax t6F)) (.impL e bot (.andR uF t6F (.andR r2 t6F (.boxR ne (.impL e bot (.orL e ne (.boxL bot .bot) (.andL (.ifThen m4 t3) t6F (.boxLoc bot (.ax ne)))) .bot)) (.ax t6F)) (.ax t6F)) .bot))) (.orL e ne (.andR r2 t6F (.impR uF t3 (.orL e ne (.andL (.ifThen m4 t3) t6F (.ax t3)) (.impL e bot (.andL (.ifThen m4 t3) t6F (.ax e)) .bot))) (.ax t6F)) (.impL e bot (.andR r2 t6F (.impR uF t3 (.impL e bot (.orL e ne (.andL (.ifThen m4 t3) t6F (.ax e)) (.andL (.ifThen m4 t3) t6F (.ax t3))) .bot)) (.ax t6F)) .bot)))))
    (.impR (.and r2 t6F) m6 (.andL r2 t6F (.impL uF t3 (.impL t5 t3 (.orR t3 t4 (.orR e ne (.andR (.ifThen m4 t3) t6F (.impR m4 t3 (.impL uF t3 (.impL t5 t3 (.andL r2 t6F (.andL uF t6F (.orR t3 t4 (.orR e ne (.ax uF))))) (.orL e ne (.andL r2 t6F (.andL uF t6F (.ax uF))) (.impL e bot (.andL r2 t6F (.andL uF t6F (.ax uF))) .bot))) (.orL e ne (.andL r2 t6F (.andL uF t6F (.ax t3))) (.impL e bot (.andL r2 t6F (.andL uF t6F (.ax t3))) .bot)))) (.ax t6F)))) (.orL e ne (.andR (.ifThen m4 t3) t6F (.boxR ne (.boxL bot .bot)) (.ax t6F)) (.impL e bot (.andR (.ifThen m4 t3) t6F (.boxR ne (.impL e bot (.orL e ne (.boxL bot .bot) (.andL r2 t6F (.boxLoc bot (.ax ne)))) .bot)) (.ax t6F)) .bot))) (.orL e ne (.andR (.ifThen m4 t3) t6F (.impR m4 t3 (.orL e ne (.andL r2 t6F (.andL uF t6F (.ax t3))) (.impL e bot (.andL r2 t6F (.andL uF t6F (.ax e))) .bot))) (.ax t6F)) (.impL e bot (.andR (.ifThen m4 t3) t6F (.impR m4 t3 (.impL e bot (.orL e ne (.andL r2 t6F (.andL uF t6F (.ax e))) (.andL r2 t6F (.andL uF t6F (.ax t3)))) .bot)) (.ax t6F)) .bot)))))
    (by decide +kernel) (by decide +kernel)

theorem cell_m9 : Interd m9 (.and r4 t6F) :=
  interdTab (.impR m9 (.and r4 t6F) (.andL (.ifThen m6 m4) t6F (.impL m6 m4 (.impL t5 t3 (.orR t3 t4 (.orR e ne (.andR (.ifThen m4 t3) t6F (.andR r4 t6F (.impR r3 uF (.impL t5 t3 (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.andR (.ifThen m4 t3) t6F (.orR t3 t4 (.orR e ne (.ax uF))) (.ax t6F)) (.impL uF t3 (.andR (.ifThen m4 t3) t6F (.orR t3 t4 (.orR e ne (.boxR ne (.impL t5 t3 (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.impL uF t3 (.orL uF r2 (.boxL ne (.impL e bot (.boxLoc bot (.ax uF)) .bot)) (.boxLoc ne (.andR (.ifThen m4 t3) t6F (.orR t3 t4 (.orR e ne (.boxLoc bot (.impR m4 t3 (.impL t5 t3 (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.impL uF t3 (.orL uF r2 (.andL uF t6F (.ax uF)) (.andL uF t6F (.ax uF))) (.orL e ne (.orL uF r2 (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F))) (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F)))) (.impL e bot (.orL uF r2 (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F))) (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F)))) .bot)))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.impL uF t3 (.orL uF r2 (.ax uF) (.ax uF)) (.orL e ne (.orL uF r2 (.orR t3 t4 (.ax t3)) (.orR t3 t4 (.ax t3))) (.impL e bot (.orL uF r2 (.orR t3 t4 (.ax t3)) (.orR t3 t4 (.ax t3))) .bot)))))) (.orL e ne (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F))) (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F))))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.ax t3) (.ax t3))))) (.impL e bot (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F))) (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F))))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.ax t3) (.ax t3))))) .bot))))))) (.ax t6F)))) (.orL e ne (.boxL bot .bot) (.impL e bot (.orL uF r2 (.boxL ne (.boxLoc bot (.andR (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3)) (.ax t6F)))) (.boxLoc bot (.andR (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3)) (.ax t6F)))) .bot)))) (.andL uF t6F (.boxL ne (.impL e bot (.andL (.ifThen m6 m4) t6F (.impL uF t3 (.orL uF r2 (.ax uF) (.ax uF)) (.orL e ne (.boxL bot .bot) (.orL uF r2 (.boxLoc bot (.orR t3 t4 (.ax t3))) (.boxLoc bot (.orR t3 t4 (.ax t3))))))) .bot)))) (.orL e ne (.boxL bot .bot) (.impL e bot (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.boxL ne (.andR (.ifThen m4 t3) t6F (.boxLoc bot (.ax ne)) (.ax t6F))) (.andR (.ifThen m4 t3) t6F (.boxLoc bot (.ax ne)) (.ax t6F)))) (.andL uF t6F (.boxL ne (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.boxLoc bot (.ax ne)) (.boxLoc bot (.ax ne))))))) .bot)))))) (.ax t6F)) (.orL e ne (.andR (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3)) (.ax t6F)) (.impL e bot (.andR (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3)) (.ax t6F)) .bot))))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.orR t3 t4 (.orR e ne (.ax uF))) (.impL uF t3 (.ax uF) (.orL e ne (.orR t3 t4 (.ax t3)) (.impL e bot (.orR t3 t4 (.ax t3)) .bot))))))) (.orL e ne (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.andR (.ifThen m4 t3) t6F (.ax uF) (.ax t6F)) (.andR (.ifThen m4 t3) t6F (.boxR ne (.boxL bot .bot)) (.ax t6F)))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.ax uF) (.ax uF))))) (.impL e bot (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.andR (.ifThen m4 t3) t6F (.ax uF) (.ax t6F)) (.andR (.ifThen m4 t3) t6F (.boxR ne (.impL e bot (.orL e ne (.boxL bot .bot) (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.boxL ne (.andR (.ifThen m4 t3) t6F (.boxLoc bot (.ax ne)) (.ax t6F))) (.andR (.ifThen m4 t3) t6F (.boxLoc bot (.ax ne)) (.ax t6F)))) (.andL uF t6F (.boxL ne (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.boxLoc bot (.ax ne)) (.boxLoc bot (.ax ne)))))))) .bot)) (.ax t6F)))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.ax uF) (.ax uF))))) .bot)))) (.ax t6F)) (.ax t6F)))) (.orL e ne (.andR (.ifThen m4 t3) t6F (.andR r4 t6F (.impR m4 t3 (.orL e ne (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F)))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.ax t3)))) (.impL e bot (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F)))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.ax e)))) .bot))) (.ax t6F)) (.ax t6F)) (.impL e bot (.andR (.ifThen m4 t3) t6F (.andR r4 t6F (.impR m4 t3 (.impL e bot (.orL e ne (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F)))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.ax e)))) (.impL m6 m4 (.andL (.ifThen m6 m4) t6F (.andL uF t6F (.andR (.ifThen m4 t3) t6F (.impLoc m4 t3 (.ax t3)) (.ax t6F)))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.ax t3))))) .bot)) (.ax t6F)) (.ax t6F)) .bot))) (.andL uF t6F (.impL t5 t3 (.orR t3 t4 (.orR e ne (.andR r4 t6F (.impR r3 uF (.impL t5 t3 (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.orR t3 t4 (.orR e ne (.ax uF))) (.impL uF t3 (.ax uF) (.orL e ne (.orR t3 t4 (.ax t3)) (.impL e bot (.orR t3 t4 (.ax t3)) .bot)))))) (.orL e ne (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.ax uF) (.ax uF)))) (.impL e bot (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.ax uF) (.ax uF)))) .bot)))) (.ax t6F)))) (.orL e ne (.andR r4 t6F (.impR r3 uF (.orL e ne (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.ax uF) (.ax uF)))) (.impL e bot (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.ax e) (.ax e)))) .bot))) (.ax t6F)) (.impL e bot (.andR r4 t6F (.impR r3 uF (.impL e bot (.orL e ne (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.ax e) (.ax e)))) (.andL uF t6F (.andL (.ifThen m6 m4) t6F (.orL uF r2 (.ax uF) (.ax uF))))) .bot)) (.ax t6F)) .bot)))))))
    (.impR (.and r4 t6F) m9 (.andL r4 t6F (.impL r3 uF (.impL t5 t3 (.orR t3 t4 (.orR e ne (.orR uF r2 (.andR (.ifThen m6 m4) t6F (.impR m6 m4 (.impL r3 uF (.impL t5 t3 (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.impL m4 t3 (.andR uF t6F (.orR t3 t4 (.orR e ne (.orR uF r2 (.boxR ne (.impL r3 uF (.impL t5 t3 (.andL r4 t6F (.impL m4 t3 (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.boxLoc ne (.orR t3 t4 (.orR e ne (.boxLoc bot (.orR uF r2 (.impR uF t3 (.impL r3 uF (.impL t5 t3 (.andL r4 t6F (.impL m4 t3 (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.ax uF) (.ax t6F))) (.orL e ne (.andL (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3))) (.impL e bot (.andL (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3))) .bot)))) (.orL e ne (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.orR uF r2 (.ax uF)))) (.impL e bot (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.orR uF r2 (.ax uF)))) .bot))) (.impL t5 t3 (.andL r4 t6F (.impL m4 t3 (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.ax uF) (.ax t6F))) (.orL e ne (.andL (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3))) (.impL e bot (.andL (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3))) .bot)))) (.orL e ne (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.ax t3))) (.impL e bot (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.ax t3))) .bot)))))))))) (.ax t6F))) (.orL e ne (.boxL bot .bot) (.impL e bot (.andL (.ifThen m4 t3) t6F (.boxLoc bot (.orR t3 t4 (.ax t3)))) .bot)))) (.orL e ne (.boxL bot .bot) (.impL e bot (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.boxLoc bot (.orR uF r2 (.boxLoc ne (.ax ne)))))) .bot))) (.boxL ne (.impL e bot (.impL t5 t3 (.andL r4 t6F (.impL m4 t3 (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.ax uF) (.ax t6F))) (.orL e ne (.boxL bot .bot) (.andL (.ifThen m4 t3) t6F (.orR t3 t4 (.ax t3)))))) (.orL e ne (.boxL bot .bot) (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.boxLoc bot (.ax ne)))))) .bot))))))) (.ax t6F)) (.orL e ne (.orR t3 t4 (.ax t3)) (.impL e bot (.orR t3 t4 (.ax t3)) .bot))))) (.orL e ne (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.orR uF r2 (.andR uF t6F (.boxR ne (.boxL bot .bot)) (.ax t6F))))) (.impL e bot (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.orR uF r2 (.andR uF t6F (.boxR ne (.impL e bot (.orL e ne (.boxL bot .bot) (.impL r3 uF (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.orR uF r2 (.boxLoc ne (.ax ne))))) (.boxL ne (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.boxLoc bot (.ax ne))))))) .bot)) (.ax t6F))))) .bot))) (.impL t5 t3 (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.impL m4 t3 (.andR uF t6F (.ax uF) (.ax t6F)) (.orL e ne (.orR t3 t4 (.ax t3)) (.impL e bot (.orR t3 t4 (.ax t3)) .bot))))) (.orL e ne (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.ax uF) (.ax t6F)))) (.impL e bot (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.ax uF) (.ax t6F)))) .bot))))) (.ax t6F))))) (.orL e ne (.orR uF r2 (.andR (.ifThen m6 m4) t6F (.boxR ne (.boxL bot .bot)) (.ax t6F))) (.impL e bot (.orR uF r2 (.andR (.ifThen m6 m4) t6F (.boxR ne (.impL e bot (.orL e ne (.boxL bot .bot) (.impL r3 uF (.andL r4 t6F (.orR uF r2 (.boxLoc ne (.ax ne)))) (.boxL ne (.andL r4 t6F (.boxLoc bot (.ax ne)))))) .bot)) (.ax t6F))) .bot))) (.impL t5 t3 (.orR t3 t4 (.orR e ne (.andR (.ifThen m6 m4) t6F (.impR m6 m4 (.impL t5 t3 (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.impL m4 t3 (.andR uF t6F (.ax uF) (.ax t6F)) (.orL e ne (.orR t3 t4 (.ax t3)) (.impL e bot (.orR t3 t4 (.ax t3)) .bot))))) (.orL e ne (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.ax uF) (.ax t6F)))) (.impL e bot (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.ax uF) (.ax t6F)))) .bot)))) (.ax t6F)))) (.orL e ne (.andR (.ifThen m6 m4) t6F (.impR m6 m4 (.orL e ne (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.ax uF) (.ax t6F)))) (.impL e bot (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.ax e))) .bot))) (.ax t6F)) (.impL e bot (.andR (.ifThen m6 m4) t6F (.impR m6 m4 (.impL e bot (.orL e ne (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.ax e))) (.andL r4 t6F (.andL (.ifThen m4 t3) t6F (.andR uF t6F (.ax uF) (.ax t6F))))) .bot)) (.ax t6F)) .bot))))))
    (by decide +kernel) (by decide +kernel)


/-! ## The countermodel -/

/-- Worlds: the Rieger–Nishimura ladder and three tops. -/
inductive UW where
  | lad (n : Nat)
  | nE
  | oE
  | fl

/-- `Rᵢ`: the ladder order, every ladder world below every top, `oE ≤ fl`. -/
def RiU : UW → UW → Prop
  | .lad x, .lad y => ladder.le x y
  | .lad _, .nE => True
  | .lad _, .oE => True
  | .lad _, .fl => True
  | .nE, .nE => True
  | .oE, .oE => True
  | .oE, .fl => True
  | .fl, .fl => True
  | _, _ => False

/-- `Rₘ`: identity, `oE ⇝ fl`, and the one ladder edge `lad 0 ⇝ nE`. -/
def RmU : UW → UW → Prop
  | .lad x, .lad y => x = y
  | .lad x, .nE => x = 0
  | .nE, .nE => True
  | .oE, .oE => True
  | .oE, .fl => True
  | .fl, .fl => True
  | _, _ => False

theorem RiU_refl : ∀ x : UW, RiU x x
  | .lad n => ladder.refl n
  | .nE => trivial
  | .oE => trivial
  | .fl => trivial

theorem RiU_trans {x y z : UW} (h1 : RiU x y) (h2 : RiU y z) : RiU x z := by
  cases x <;> cases y <;> cases z <;>
    first
    | exact trivial
    | exact ladder.trans h1 h2
    | exact False.elim h1
    | exact False.elim h2

theorem RmU_refl : ∀ x : UW, RmU x x
  | .lad _ => rfl
  | .nE => trivial
  | .oE => trivial
  | .fl => trivial

theorem RmU_trans {x y z : UW} (h1 : RmU x y) (h2 : RmU y z) : RmU x z := by
  cases x <;> cases y <;> cases z <;>
    first
    | exact trivial
    | exact Eq.trans h1 h2
    | exact h1
    | exact False.elim h1
    | exact False.elim h2

theorem RmU_sub {x y : UW} (h : RmU x y) : RiU x y := by
  cases x <;> cases y <;>
    first
    | exact trivial
    | exact False.elim h
    | (subst h; exact ladder.refl _)

theorem fl_up {x y : UW} (h : RiU x y) (hx : x = .fl) : y = .fl := by
  subst hx
  cases y <;> first | rfl | exact False.elim h

/-- **The model**: the ladder under `nE`, `oE ≤ fl`; `F = {fl}`; one
ladder edge `lad 0 ⇝ nE`. -/
@[reducible] def cmU : ConstraintModel where
  W := UW
  Ri := RiU
  Rm := RmU
  F := {w | w = .fl}
  V _ := {w | w = .fl}
  refl_i := RiU_refl
  trans_i := RiU_trans
  refl_m := RmU_refl
  trans_m := RmU_trans
  sub_mi := RmU_sub
  hered_F := fun h hx => fl_up h hx
  hered_V := fun h hx => fl_up h hx
  full_F := fun hx => hx

/-- The three tops. -/
def isTop : UW → Prop
  | .lad _ => False
  | _ => True

theorem top_up {x y : UW} (hx : isTop x) (h : RiU x y) : isTop y := by
  cases x <;> cases y <;> first | exact trivial | exact False.elim hx | exact False.elim h

theorem force_fl (φ : PLLFormula) : cmU.force UW.fl φ := cmU.force_of_fallible rfl

/-! ## Truth sets of the base formulas -/

/-- `◯⊥ = {oE, fl}`. -/
theorem force_e (w : UW) : cmU.force w e ↔ (w = .oE ∨ w = .fl) := by
  constructor
  · intro h
    cases w with
    | lad x =>
        obtain ⟨u, hm, hu⟩ := h UW.nE trivial
        have hu' : u = UW.fl := hu
        subst hu'
        exact False.elim hm
    | nE =>
        obtain ⟨u, hm, hu⟩ := h UW.nE trivial
        have hu' : u = UW.fl := hu
        subst hu'
        exact False.elim hm
    | oE => exact Or.inl rfl
    | fl => exact Or.inr rfl
  · rintro (rfl | rfl)
    · intro v hv
      cases v with
      | oE => exact ⟨UW.fl, trivial, rfl⟩
      | fl => exact ⟨UW.fl, trivial, rfl⟩
      | lad _ => exact False.elim hv
      | nE => exact False.elim hv
    · exact force_fl _

/-- `¬◯⊥ = {nE, fl}`. -/
theorem force_ne (w : UW) : cmU.force w ne ↔ (w = .nE ∨ w = .fl) := by
  constructor
  · intro h
    cases w with
    | lad x =>
        have h' : UW.oE = UW.fl := h UW.oE trivial ((force_e UW.oE).mpr (Or.inl rfl))
        cases h'
    | nE => exact Or.inl rfl
    | oE =>
        have h' : UW.oE = UW.fl := h UW.oE trivial ((force_e UW.oE).mpr (Or.inl rfl))
        cases h'
    | fl => exact Or.inr rfl
  · rintro (rfl | rfl)
    · intro v hv hve
      cases v with
      | nE => rcases (force_e UW.nE).mp hve with h' | h' <;> cases h'
      | lad _ => exact False.elim hv
      | oE => exact False.elim hv
      | fl => exact False.elim hv
    · exact force_fl _

/-- `t3 = {nE, oE, fl}`: false on the whole ladder. -/
theorem force_t3 (w : UW) : cmU.force w t3 ↔ isTop w := by
  constructor
  · intro h
    have h' : cmU.force w e ∨ cmU.force w ne := h
    rcases h' with h' | h'
    · rcases (force_e w).mp h' with rfl | rfl <;> trivial
    · rcases (force_ne w).mp h' with rfl | rfl <;> trivial
  · intro h
    cases w with
    | lad _ => exact False.elim h
    | nE => exact Or.inr ((force_ne _).mpr (Or.inl rfl))
    | oE => exact Or.inl ((force_e _).mpr (Or.inl rfl))
    | fl => exact Or.inl ((force_e _).mpr (Or.inr rfl))

theorem force_t4 {w : UW} (h : cmU.force w t4) : w = .oE ∨ w = .fl := by
  cases w with
  | lad x =>
      have h' := h UW.nE trivial ((force_t3 UW.nE).mpr trivial)
      rcases (force_e UW.nE).mp h' with h'' | h'' <;> cases h''
  | nE =>
      have h' := h UW.nE trivial ((force_t3 UW.nE).mpr trivial)
      rcases (force_e UW.nE).mp h' with h'' | h'' <;> cases h''
  | oE => exact Or.inl rfl
  | fl => exact Or.inr rfl

/-- `t6` holds everywhere. -/
theorem force_t6 (w : UW) : cmU.force w t6F := by
  show ∀ v, cmU.Ri w v → cmU.force v t5 → cmU.force v t3
  intro v _ h5
  refine (force_t3 v).mpr ?_
  rcases (h5 : cmU.force v t3 ∨ cmU.force v t4) with h | h
  · exact (force_t3 v).mp h
  · rcases force_t4 h with rfl | rfl <;> trivial

/-- `u = ◯¬◯⊥` holds on the ladder exactly at `lad 0`. -/
theorem force_u_lad (x : Nat) : cmU.force (UW.lad x) uF ↔ x = 0 := by
  constructor
  · intro h
    obtain ⟨y, hm, hy⟩ := h (UW.lad x) (RiU_refl (UW.lad x))
    cases y with
    | lad z =>
        have hz : x = z := hm
        subst hz
        rcases (force_ne (UW.lad x)).mp hy with h' | h' <;> cases h'
    | nE => exact hm
    | oE => exact False.elim hm
    | fl => exact False.elim hm
  · rintro rfl
    show ∀ v, cmU.Ri (UW.lad 0) v → ∃ y, cmU.Rm v y ∧ cmU.force y ne
    intro v hv
    cases v with
    | lad y =>
        have hy : y = 0 := by
          rcases (hv : y = 0 ∨ y + 2 ≤ 0) with h | h
          · exact h
          · omega
        subst hy
        exact ⟨UW.nE, rfl, (force_ne UW.nE).mpr (Or.inl rfl)⟩
    | nE => exact ⟨UW.nE, trivial, (force_ne UW.nE).mpr (Or.inl rfl)⟩
    | oE => exact ⟨UW.fl, trivial, force_fl _⟩
    | fl => exact ⟨UW.fl, trivial, force_fl _⟩

theorem force_u_top {w : UW} (hw : isTop w) : cmU.force w uF := by
  show ∀ v, cmU.Ri w v → ∃ y, cmU.Rm v y ∧ cmU.force y ne
  intro v hv
  have hv' := top_up hw hv
  cases v with
  | lad _ => exact False.elim hv'
  | nE => exact ⟨UW.nE, trivial, (force_ne UW.nE).mpr (Or.inl rfl)⟩
  | oE => exact ⟨UW.fl, trivial, force_fl _⟩
  | fl => exact ⟨UW.fl, trivial, force_fl _⟩

/-! ## The transfer -/

/-- **The transfer**: for ◯-free `A`, `rel A` holds at every top, and at a
ladder world exactly when `A` holds there on the RN ladder. -/
theorem rel_transfer : ∀ {A : PLLFormula}, boxFree A = true →
    (∀ x : Nat, cmU.force (UW.lad x) (rel A) ↔ ladder.sat A x) ∧
    (∀ w : UW, isTop w → cmU.force w (rel A)) := by
  intro A
  induction A with
  | prop a =>
      intro _
      by_cases ha : a = pv
      · have hr : rel (.prop a) = uF := by
          show (if a = pv then uF else t3) = uF
          exact if_pos ha
        rw [hr]
        exact ⟨fun x => ⟨fun h => ⟨ha, (force_u_lad x).mp h⟩,
            fun h => (force_u_lad x).mpr h.2⟩,
          fun w hw => force_u_top hw⟩
      · have hr : rel (.prop a) = t3 := by
          show (if a = pv then uF else t3) = t3
          exact if_neg ha
        rw [hr]
        exact ⟨fun x => ⟨fun h => False.elim ((force_t3 _).mp h), fun h => absurd h.1 ha⟩,
          fun w hw => (force_t3 w).mpr hw⟩
  | falsePLL =>
      intro _
      exact ⟨fun x => ⟨fun h => False.elim ((force_t3 (UW.lad x)).mp h),
          fun h => False.elim h⟩,
        fun w hw => (force_t3 w).mpr hw⟩
  | and A B ihA ihB =>
      intro h
      simp only [boxFree, Bool.and_eq_true] at h
      obtain ⟨hA1, hA2⟩ := ihA h.1
      obtain ⟨hB1, hB2⟩ := ihB h.2
      exact ⟨fun x => and_congr (hA1 x) (hB1 x), fun w hw => ⟨hA2 w hw, hB2 w hw⟩⟩
  | or A B ihA ihB =>
      intro h
      simp only [boxFree, Bool.and_eq_true] at h
      obtain ⟨hA1, hA2⟩ := ihA h.1
      obtain ⟨hB1, hB2⟩ := ihB h.2
      exact ⟨fun x => or_congr (hA1 x) (hB1 x), fun w hw => Or.inl (hA2 w hw)⟩
  | ifThen A B ihA ihB =>
      intro h
      simp only [boxFree, Bool.and_eq_true] at h
      obtain ⟨hA1, hA2⟩ := ihA h.1
      obtain ⟨hB1, hB2⟩ := ihB h.2
      refine ⟨fun x => ⟨fun hf y hle hsA => ?_, fun hs v hv hvA => ?_⟩,
        fun w hw v hv _ => hB2 v (top_up hw hv)⟩
      · exact (hB1 y).mp (hf (UW.lad y) hle ((hA1 y).mpr hsA))
      · cases v with
        | lad y => exact (hB1 y).mpr (hs y hv ((hA1 y).mp hvA))
        | nE => exact hB2 _ trivial
        | oE => exact hB2 _ trivial
        | fl => exact hB2 _ trivial
  | somehow A _ =>
      intro h
      simp only [boxFree] at h
      exact Bool.noConfusion h

/-! ## The chain -/

/-- `x k = rel (rn (2k+1)) ∧ t6`. -/
def xc (k : Nat) : PLLFormula := (rel (rnP k).1).and t6F

theorem rel_odd (k x : Nat) : cmU.force (UW.lad x) (rel (rnP k).1) ↔ x ≤ k :=
  ((rel_transfer (rnP_boxFree k).1).1 x).trans ((sat_rnP_cf k).1 x)

/-- `x k` holds at `lad x` iff `x ≤ k`. -/
theorem xc_force (k x : Nat) : cmU.force (UW.lad x) (xc k) ↔ x ≤ k :=
  ⟨fun h => (rel_odd k x).mp h.1, fun h => ⟨(rel_odd k x).mpr h, force_t6 _⟩⟩

theorem rel_vf : ∀ A : PLLFormula, atomFree (rel A) = true
  | .prop a => by
      show atomFree (if a = pv then uF else t3) = true
      split <;> rfl
  | .falsePLL => rfl
  | .and A B => by
      show (atomFree (rel A) && atomFree (rel B)) = true
      rw [rel_vf A, rel_vf B]
      rfl
  | .or A B => by
      show (atomFree (rel A) && atomFree (rel B)) = true
      rw [rel_vf A, rel_vf B]
      rfl
  | .ifThen A B => by
      show (atomFree (rel A) && atomFree (rel B)) = true
      rw [rel_vf A, rel_vf B]
      rfl
  | .somehow A => rel_vf A

theorem xc_vf (k : Nat) : atomFree (xc k) = true := by
  show (atomFree (rel (rnP k).1) && atomFree t6F) = true
  rw [rel_vf]
  rfl

theorem xc_le_t6 (k : Nat) : Deriv [xc k] (rnSub 6) := by
  rw [rnSub_6]
  exact Deriv.andElim2 (Deriv.iden (.head _))

theorem xc_mono (k : Nat) : Deriv [xc k] (xc (k + 1)) :=
  Deriv.andIntro (Deriv.orIntro1 (Deriv.andElim1 (Deriv.iden (.head _))))
    (Deriv.andElim2 (Deriv.iden (.head _)))

theorem xc_not_le {j k : Nat} (h : j < k) : [xc k] ⊬ xc j := by
  rintro ⟨d⟩
  have hs := soundness d cmU (UW.lad k) (fun ψ hψ => by
    have hψk : ψ = xc k := by
      cases hψ with
      | head => rfl
      | tail _ h' => cases h'
    subst hψk
    exact (xc_force k k).mpr (Nat.le_refl k))
  have := (xc_force j k).mp hs
  omega

/-- **An infinite strictly increasing chain below `t6`**:

    atomFree (x k),   x k ⊢ t6,   x k ⊢ x (k+1),   x (k+1) ⊬ x k. -/
theorem t6_chain (k : Nat) :
    atomFree (xc k) = true ∧ Deriv [xc k] (rnSub 6) ∧
      Deriv [xc k] (xc (k + 1)) ∧ ([xc (k + 1)] ⊬ xc k) :=
  ⟨xc_vf k, xc_le_t6 k, xc_mono k, xc_not_le (Nat.lt_succ_self k)⟩

/-- **`↓t6` is infinite.** -/
theorem t6_downset_infinite :
    ∃ x : Nat → PLLFormula, (∀ k, atomFree (x k) = true) ∧ (∀ k, Deriv [x k] (rnSub 6)) ∧
      (∀ j k, j ≠ k → ¬ Interd (x j) (x k)) :=
  ⟨xc, xc_vf, xc_le_t6, fun j k hjk hi => by
    rcases Nat.lt_or_gt_of_ne hjk with h | h
    · exact xc_not_le h hi.2
    · exact xc_not_le h hi.1⟩

/-! ## Every rung above `t6` -/

theorem even_even_cf {a b : Nat} (h : a + 2 ≤ b) :
    Deriv [rnSub (2 * a + 2)] (rnSub (2 * b + 2)) := by
  rw [rnSub_even_embed, rnSub_even_embed]
  exact deriv_substP (deriv_even_to_even (Or.inr h))

/-- `t6 ⊢ t n` for `n = 6, 7` and every `n ≥ 9`. -/
theorem t6_le_rung {n : Nat} (hn : n = 6 ∨ n = 7 ∨ 9 ≤ n) :
    Deriv [rnSub 6] (rnSub n) := by
  rcases hn with rfl | rfl | hn
  · exact Deriv.iden (.head _)
  · exact even_odd_cf (a := 2) (b := 3) (by decide)
  · obtain ⟨b, rfl | rfl⟩ : ∃ b, n = 2 * b + 1 ∨ n = 2 * b + 2 := ⟨(n - 1) / 2, by omega⟩
    · exact even_odd_cf (a := 2) (b := b) (by omega)
    · exact even_even_cf (a := 2) (b := b) (by omega)

/-- **C1 fails at `n = 6, 7` and every `n ≥ 9`**: `↓t n` is infinite. -/
theorem rung_downset_infinite {n : Nat} (hn : n = 6 ∨ n = 7 ∨ 9 ≤ n) :
    ∃ x : Nat → PLLFormula, (∀ k, atomFree (x k) = true) ∧ (∀ k, Deriv [x k] (rnSub n)) ∧
      (∀ j k, j ≠ k → ¬ Interd (x j) (x k)) :=
  ⟨xc, xc_vf, fun k => Deriv.cutHead (xc_le_t6 k) (t6_le_rung hn), fun j k hjk hi => by
    rcases Nat.lt_or_gt_of_ne hjk with h | h
    · exact xc_not_le h hi.2
    · exact xc_not_le h hi.1⟩

end T6
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.T6.t6_regular [propext, Quot.sound]
#axioms_within PLLND.F0.T6.t3_le_u [propext, Quot.sound]
#axioms_within PLLND.F0.T6.cell_m6 [propext, Quot.sound]
#axioms_within PLLND.F0.T6.cell_m9 [propext, Quot.sound]
#axioms_within PLLND.F0.T6.force_t6 [propext, Quot.sound]
#axioms_within PLLND.F0.T6.force_u_lad [propext, Quot.sound]
#axioms_within PLLND.F0.T6.rel_transfer [propext, Quot.sound]
#axioms_within PLLND.F0.T6.xc_force [propext, Quot.sound]
#axioms_within PLLND.F0.T6.xc_not_le [propext, Quot.sound]
#axioms_within PLLND.F0.T6.t6_chain [propext, Quot.sound]
#axioms_within PLLND.F0.T6.t6_downset_infinite [propext, Quot.sound]
#axioms_within PLLND.F0.T6.t6_le_rung [propext, Quot.sound]
#axioms_within PLLND.F0.T6.rung_downset_infinite [propext, Quot.sound]
