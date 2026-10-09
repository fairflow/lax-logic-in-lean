import LaxLogic.PLL.SemUI.SemUILayered

/-!
# The refutation screen for `amalgamation` — three designed cells

`LaxLogic/PLL/SemUI/SemUILayered.lean:821` carries `amalgamation` as a `sorry`,
labelled in its own docstring "OPEN — the central open problem of the route".
`docs/ui-proof-status-report.md` puts it where it belongs: whether PLL has
uniform interpolation is open in the literature, and the algebraic form
(amalgamation for nuclear Heyting algebras) is recorded as open too.  So before
any attempt to close it, CLAUDE.md rules 7 and 9: test the statement, with a few
DESIGNED cells and no sweep.

## The attack this screen tests, and why it looked promising

    amalgamation (X) (hX : SubClosed X) (p) (K M) (k₀ m₀)
      (B : LayeredBisim (· ≠ p) K M) (hB : B.Z (2 * nu X + 1) k₀ m₀) :
      ∃ N (C : PBisim p M N) n₀, C.Z m₀ n₀ ∧ ∀ φ ∈ X, (N.force n₀ φ ↔ K.force k₀ φ)

`PBisim p M N` is `ABisim (· ≠ p)` — an **unbounded** bisimulation protecting
every atom but `p` — so by `force_iff_of_bisim` the `N` the conclusion produces
must agree with `M` on every **p-free** formula, at every rank.  The hypothesis,
by contrast, links `K` to `M` only up to the **finite level** `2 * nu X + 1`.
A bounded hypothesis is asked for an unbounded conclusion, and the docstring
flags the asymmetry itself: "a p-VARIANT of M (unbounded bisimulation!)".

So the cheap counterexample would be: a p-free `φ ∈ X` whose `crank` EXCEEDS
`2 * nu X + 1`, on which `K` and `M` disagree.  `N` would then have to agree
with `M` on `φ` (p-free, unbounded) and with `K` on `φ` (the conclusion), and
there is no such `N`.

## What the cells show: the attack is CLOSED, and not by accident

`nu X` counts the members of `X` with `isBudget = true`, and
`isBudget` is `true` for exactly `.prop`, `.ifThen` and `.somehow`
(`SemUILayered.lean:97`) — which are exactly the nodes that GENERATE crank
(`:87`: `.ifThen` is `max + 1`, `.somehow` is `max + 2`, everything else is
`max` or `0`).  Each unit of crank is therefore financed by a distinct
subformula that `nu` counts, and for a `SubClosed` `X` every such subformula is
present.  The level is `2 * nu X + 1`; the worst ratio is `.somehow`, which buys
2 crank per 1 budget — and the factor 2 is there to pay for it.

The three cells below are chosen to make the margin as small as it can be.  The
`#guard`s are the screen: each asserts `crank φ < 2 * nu X + 1`, so each is a
cell on which the cheap attack provably CANNOT be mounted.  A cell that failed
would be a counterexample seed.
-/

namespace SemUIAmalgProbe

open PLLFormula PLLND PLLND.SemUI

/-- The subformula closure as a `Finset`, which is `SubClosed` by construction
(`PLLND.subF`, `LaxLogic/PLL/Semantics/FiniteModel.lean:26`), with `⊥` added so
the `bot` field holds. -/
def X (φ : PLLFormula) : Finset PLLFormula := insert .falsePLL (subF φ)

/-- The level the hypothesis of `amalgamation` supplies for `X φ`. -/
def level (φ : PLLFormula) : Nat := 2 * nu (X φ) + 1

/-! ## Cell 1 — the ◯-tower, where the budget is tightest

`.somehow` is the only constructor that buys 2 crank for 1 budget unit, so a
tower of them is the worst case for the `2 *` factor.  `q`, `◯q`, `◯◯q`, `◯◯◯q`
are four subformulas: one `.prop` and three `.somehow`, so `nu = 4` and the
level is 9, against `crank = 6`.  The margin is 3 and does NOT shrink with
depth: each extra `◯` adds 2 to crank and 2 to the level. -/
def tower : PLLFormula := .somehow (.somehow (.somehow (.prop "q")))

#guard crank tower = 6
#guard nu (X tower) = 4
#guard level tower = 9
#guard crank tower < level tower

/-! ## Cell 2 — the ⊃-chain over ONE atom, where `nu` is smallest

Sharing the atom keeps `nu` as low as an implication chain can make it, which is
the other way to squeeze the budget.  `q`, `q ⊃ q`, `(q ⊃ q) ⊃ q`,
`((q ⊃ q) ⊃ q) ⊃ q`: `nu = 4` again, but `.ifThen` buys only 1 crank per unit,
so `crank = 3` against a level of 9.  Implications are a worse attack than ◯. -/
def chain : PLLFormula :=
  .ifThen (.ifThen (.ifThen (.prop "q") (.prop "q")) (.prop "q")) (.prop "q")

#guard crank chain = 3
#guard nu (X chain) = 4
#guard level chain = 9
#guard crank chain < level chain

/-! ## Cell 3 — the fallibility cell, where pillar 2 actually died

`layered_of_frag_agree_refuted` (`SemUILayered.lean:789`) kills the route's
pillar 2 with two worlds and the `fall` clause, at crank ≤ 1.  So this cell asks
whether the same shape threatens `amalgamation`: `◯⊥` is the formula the
fallibility clause turns on, and `∧` and `⊥` are the two constructors that
generate NO budget at all.  `⊥`, `◯⊥`, `◯⊥ ∧ ◯⊥`: `nu = 1` — the single
`.somehow` — so the level is 3, against `crank = 2`.  Still positive, and this
is the tightest of the three in absolute terms. -/
def fallCell : PLLFormula := .and (.somehow .falsePLL) (.somehow .falsePLL)

#guard crank fallCell = 2
#guard nu (X fallCell) = 1
#guard level fallCell = 3
#guard crank fallCell < level fallCell

/-! ## Verdict

**The cheap attack is REFUTED on all three cells**, and the mechanism says why:
`isBudget` is precisely the set of crank-generating constructors, so for
`SubClosed X` the level `2 * nu X + 1` always strictly dominates the crank of
any member.  The bounded/unbounded asymmetry in the statement is real but it is
not exploitable through the p-FREE formulas of `X`, because those are exactly
the ones the rank budget was designed to cover.

This is a screen, not a proof: `#guard` settles these three cells and says
nothing about the general inequality `∀ φ, crank φ < level φ`, which is stated
below and left OPEN rather than asserted.  It looks provable by induction and
would be worth having, because it is the sufficiency claim the rank definition
is making and nothing currently checks it.

**Where the content actually is, therefore.**  Not here.  The conclusion must
produce an `N` agreeing with `K` on the members of `X` that CONTAIN `p` — where
the `PBisim` gives no constraint, because `p` is the unprotected atom — and that
freedom is Visser's construction, the part `docs/ui-proof-status-report.md`
records as assembled down to two "modal zigzag" holes with one genuine
obstruction inside them (the forward ◯-case at a same-value-trace successor,
whose natural repair was itself REFUTED by a machine probe, the obstruction
decoded as a "rigid dead-end" world forcing `q ∧ ¬◯⊥` at crank 3).

Two or three cells cannot settle that, and this screen does not claim to. -/

/-- The sufficiency of the rank budget, as a statement.  OPEN: carried as a
proposition, not a sorried theorem, per CLAUDE.md rule 1. -/
def RankBudgetSuffices : Prop :=
  ∀ (φ : PLLFormula), crank φ < 2 * nu (insert PLLFormula.falsePLL (subF φ)) + 1

end SemUIAmalgProbe
