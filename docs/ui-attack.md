# The UI attack: goal, method, objects, status

*2026-08-03.  Fixes the names and the architecture of the campaign to
prove that uniform interpolation fails for PLL.  Everything cited as
PROVED is sorry-free Lean on `origin/ui-confluence`; all derivability
is PLL (`Deriv` = `LaxND`).*

## Goal

Prove that **PLL does not have uniform interpolation** (or discover
that this attack cannot work, which would be evidence the other way).
It suffices to refute the LAST-variable case: interpolants that
eliminate the only variable of a one-variable formula, which must be
**variable-free** — elements of RN(◯,{}), the algebra this whole
campaign has been charting.

## The four named objects

For a one-variable formula φ (atoms ⊆ {p}):

| name | definition | order structure |
|---|---|---|
| **consequence filter** `F(φ)` | `{χ variable-free : φ ⊢ χ}` | up-closed, ∧-closed |
| **antecedent ideal** `I(φ)` | `{χ variable-free : χ ⊢ φ}` | down-closed, ∨-closed |
| **post-interpolant** `∃p.φ` | the MINIMUM of `F(φ)`, if it exists | Lean: `IsPostInterp` |
| **pre-interpolant** `∀p.φ` | the MAXIMUM of `I(φ)`, if it exists | Lean: `IsPreInterp` |

UI for this fragment = both exist for EVERY φ.  To refute UI we need
ONE φ for which one of them fails to exist.

A fifth, fixed landmark of the algebra (not attached to any φ):

* **the landing ideal `L`** `:= {χ variable-free : ∀k ≥ 1, χ ⊢ g k}`
  — the common lower bounds of the gap antichain.  Down-closed and
  ∨-closed (an ideal).  Any post-interpolant of any gap-entailing φ
  must lie in `F(φ) ∩ L`.  PROVED about `L`: it contains `t3`, `t4`,
  `t5` and `w15`, with `t3 < w15` strictly and `t5, w15`
  incomparable (so `L` has width ≥ 2); `t6, t7 ∉ L`.

## Method: the S4 mechanism, transplanted

For S4-like modal logics UI fails (Ghilardi–Zawadowski).  The
semantic mechanism: some φ's consequence filter is **non-principal**
— it contains a strictly descending meet-chain with no floor inside
the filter, so no single formula can be the least consequence.  Our
plan is the same mechanism with RN(◯,{}) as the target fragment,
powered by the proved families:

* **descending engine** (∃-side): the partial meets of the gap
  antichain, `Gmeet n = g 1 ∧ … ∧ g (n+1)`, descend strictly forever
  (`Gmeet_strict`, `Gmeet_desc_strict`).
* **ascending engine** (∀-side): the chain `c 1 < c 2 < …`
  (`chain_lt_strict`), with no known upper bound but `⊤`.

## The architecture is TWO-step — the engine does not build φ

Step 1 (DONE): the engines exist.  Step 2 (OPEN): the **witness** — a
specific one-variable φ whose filter/ideal the engine breaks.  The
descending chain lives in the ambient algebra; a UI failure needs it
to be cofinal (downward) inside `F(φ)` for a single φ, with nothing of
`F(φ)` below it.  There is no general recipe that extracts φ from the
chain — in the S4 literature the witness is constructed by hand and
its filter computed.  The Lean reduction theorems make the two-step
shape exact (`no_post_interp_schema`, `no_pre_interp_schema`):

* ∀-side witness conditions: `hc : ∀ k, c k ⊢ φ` and
  `hU`: no variable-free bound of the whole c-chain entails φ.
* ∃-side witness conditions: `hg : ∀ k, φ ⊢ g k` and
  `hL`: no member of `L` is a consequence of φ.

## On ∃p vs ∀p (clearing a confusion)

Nothing has ever been PROVED about the existence of either quantifier
for all φ.  What happened earlier (July's rank-bounded probes) was the
computation of candidate VALUES for specific instances — e.g. the
approximants of `∀p.◯p` stabilising at `◯⊥` — which are consistent
with those particular interpolants existing.  Some certainly exist
(`∃p.p = ⊤`).  The attack needs one φ WITHOUT one; both sides are
live, and currently the ∀-side is further along:

* `phi1 := ◯p ⊃ ◯(p ∧ t3)` is a NEAR-witness: `c 1 ⊢ phi1` but
  `c 2 ⊬ phi1` (so `hc` fails), while its `hU` is PROVED outright via
  the substitution lever (`bound_collapse`: any variable-free
  `χ ⊢ phi1` entails `c 1` by the `p ↦ ⊤` instance, so a chain-bound
  entailing φ₁ would collapse `c 2 ⊢ c 1`).
* Within the image of `p ↦ ◯⊥` the ∀-side is CLOSED:
  `inimage_chain_bound_top` — only `⊤` bounds the c-chain there; and
  every known off-image family is separately excluded.

## The current fork, and what is running

(a) Find a one-variable bound of the RUNG chain
(`∀k, rnSub (2k+1) ⊢ φ`, φ not a theorem): the bind mechanism turns
any such φ into `◯φ`-material above the c-chain — the missing `hc`.
This is being probed now (enumeration + certificate search +
countermodel filtering, delegated).  The regress observation — bind
reduces c-chain bounds to rung-chain bounds, one ◯ down — suggests
the answer may be NO.

(b) If (a) is refuted: prove the off-image version of "only ⊤ bounds
the c-chain", completing `hU`-side impossibility — which would DEFEAT
the c-chain attack on UI and shift all weight to the ∃-side (where
`L`'s structure — does it have maximal elements? — becomes the
question).

Either outcome of (a) is progress: a witness kills UI; a refutation
redirects the attack with the search space halved.
