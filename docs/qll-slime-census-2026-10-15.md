# Green-slime census of `LaxLogic/QLL`, 2026-10-15

*Run on branch `clp-presentation` at `2518be0` (the CLP paper at version
0.5), with `#slime` (`Meta/Slime.lean`).  The previous census
(`docs/slime-census.md`, 2026-08-18) did not cover `LaxLogic/QLL`, which
was written afterwards.*

Green slime (McBride): a **computed index in a constructor's return
type**.  The unifier cannot invert it, so `cases` and dependent pattern
matching either fail on the family or survive only by substituting into
whatever variable stands opposite.  Computation in a premise is harmless.
See `.claude/skills/calculus-adoption/reference/green-slime.md`.

Reproduce with a scratch file (not part of the library):

    import Meta.Slime
    import LaxLogic.PLL.ND.NDCore
    import LaxLogic.QLL
    #slime PLLND.LaxND                         -- the control: 0 of 12
    #slime LaxLogic.QLL.Prv LaxLogic.QLL.Step  -- and so on, one per family below

The families checked are **every inductive family with at least one
index defined in a `LaxLogic.QLL` module** (23 families, listed from the
environment, not by hand).  The 38 non-indexed inductive types of those
modules (`Form`, `Tm`, `CProof`, `AProof`, `PTree`, `ATree`, the
structures, ...) have no indices and so cannot carry slime.

## Control

| family | file | slimed / constructors |
|---|---|---|
| `PLLND.LaxND` | `LaxLogic/PLL/ND/NDCore.lean` | 0 / 12 |

## Result before desliming

| family | file | slimed / constructors | computed index (constructor: index) | computed by |
|---|---|---|---|---|
| **`Prv`** | `Prov.lean` | **1 / 17** | `allE`: `Form.openAt 0 t A` | `Form.openAt` |
| **`PrvC`** | `Bridge.lean` | **1 / 17** | `allE`: `Form.openAt 0 t A` | `Form.openAt` |
| `Derives` | `Deriv.lean` | 0 / 17 | (its `allE` already carries `B = A.openAt 0 t` as an equation field) | |
| `PEnv` | `Denote.lean` | 0 / 2 | | |
| `CtxRefines` | `Sound.lean` | 0 / 2 | | |
| `IsSigma` | `LLP.lean` | 0 / 5 | | |
| `IsPP` | `Horn.lean` | 0 / 4 | | |
| **`Holds`** | `Herbrand.lean` | **1 / 5** | `fire`: `Form.pred h.head (Tm.instAllList ts h.args)` | `Horn.head`, `Tm.instAllList` |
| **`CTyped`** | `CLPCore.lean` | **1 / 7** | `clause`: `Form.pred c.head (Tm.instAllList ts (headVars c.arity))` | `Clause.head`, `Tm.instAllList` |
| **`Step`** | `CLPOper.lean` | **7 / 7** | every rule, both goals: `⟨c, l ++ φ :: r⟩` and its successor, e.g. `cstr`: `⟨c, l ++ B(t̃) :: r⟩` to `⟨c ∧ B(t̃), l ++ r⟩` | `HAppend.hAppend` (and `Form.openAt`, `Form.instAll`, `Clause.head` inside) |
| `Steps` | `CLPOper.lean` | 0 / 2 | | |
| `Forest` | `CLPOper.lean` | 0 / 2 | | |
| **`ATyped`** | `CLPAbstract.lean` | **1 / 6** | `impC`: `Form.pred c.head (Tm.instAllList ts (headVars c.arity))` | `Clause.head`, `Tm.instAllList` |
| **`SLD.Expand`** | `CLPMachine.lean` | **2 / 13** | `ex`: `.exI t (.hole (A.openAt 0 t))`; `clause`: `.hole (.pred cl.head …)` and `.clause w ts (.hole (Form.instAll ts cl.body))` | `Form.openAt`; `Clause.head`, `Form.instAll` |
| **`SLD.SLDStep`** | `CLPMachine.lean` | **1 / 1** | `mk`: `⟨c, l ++ p :: r⟩` and `⟨c', l ++ p' :: r⟩` | `HAppend.hAppend` |
| `SLD.SLDSteps` | `CLPMachine.lean` | 0 / 2 | | |
| **`SLD.PTyped`** | `CLPMachine.lean` | **1 / 8** | `clause`: `Form.pred c.head (Tm.instAllList ts (headVars c.arity))` | `Clause.head`, `Tm.instAllList` |
| **`SLD.ExpandA`** | `CLPMachine.lean` | **2 / 12** | `ex`: `.exC t (.hole (A.openAt 0 t))`; `clause`: `.hole (.pred cl.head …)` and `.impC w ts (.hole (Form.instAll ts cl.body))` | `Form.openAt`; `Clause.head`, `Form.instAll` |
| **`SLD.SLDCStep`** | `CLPMachine.lean` | **1 / 1** | `mk`: `l ++ p :: r` and `l ++ p' :: r` | `HAppend.hAppend` |
| `SLD.SLDCSteps` | `CLPMachine.lean` | 0 / 2 | | |
| **`SLD.PTypedA`** | `CLPMachine.lean` | **1 / 7** | `impC`: `Form.pred c.head (Tm.instAllList ts (headVars c.arity))` | `Clause.head`, `Tm.instAllList` |
| **`SLD.Base`** | `CLPMachine.lean` | **2 / 7** | `ex`: `[A.openAt 0 t]`; `clause`: `.pred cl.head …` and `[Form.instAll ts cl.body]` | `Form.openAt`; `Clause.head`, `Form.instAll` |
| **`SLD.ExpandAt`** | `CLPMachine.lean` | **3 / 13** (tool: 8) | `ex`, `clause`: as `Expand`; `andR`: the leaf position `p.opens.length + i` | `Form.openAt`, `Clause.head`, `Form.instAll`; `HAdd.hAdd` |

**14 of 23 indexed families carry slime: 25 constructors of 159.**

`Prv.exI` concludes `Γ ⊢ ∃A` from a premise `Γ ⊢ A.openAt 0 t`: the
computation is in the premise, so `exI` is clean; only `allE` is slimed.

### One false positive of the tool

On `SLD.ExpandAt` the tool reports 8 constructors.  Five of them (`top`,
`cstr`, `and`, `orL`, `orR`) and one index of each of `ex` and `clause`
are the numeral `0` in the position index, which elaborates to
`OfNat.ofNat 0` and is reported as "computed by `OfNat.ofNat`".  A `Nat`
literal is inert (it is `Nat.zero`, a constructor, and the unifier handles
literals natively), so these are not slime.  The genuine slime of
`ExpandAt` is in 3 constructors: `ex` and `clause` (as in `Expand`) and
`andR`, whose position `p.opens.length + i` is an addition of two terms,
not a literal offset.  The tool's literal check (`isOffset?`) recognises
`n + k` for a literal `k > 0` but not the bare literal `0`; that is a
one-line fix to `Meta/Slime.lean`, not made here.

## What the slime is, family by family

* **The `∀`-elimination rule** (`Prv`, `PrvC`): the conclusion is the
  instance `A[t/0]`.  `Derives`, the proof-term judgment of the same
  logic, already states it with an equation field; `Prv` and `PrvC` did
  not.
* **Clause application** (`Holds.fire`, `CTyped.clause`, `ATyped.impC`,
  `PTyped.clause`, `PTypedA.impC`, and the `clause` rules of the
  machines): the conclusion is the clause head instantiated at the
  recorded terms, computed by the projection `head` and by `instAllList`.
* **Position in a list** (`Step`, `SLDStep`, `SLDCStep`): the goal list
  is written `l ++ φ :: r`, an append.  Every rule of Table 2 carries it,
  so all 7 of `Step` are slimed.
* **Position in a tree** (`ExpandAt.andR`): the index of the expanded leaf
  in the right subtree is offset by the number of open leaves on the
  left.

None of this makes anything unsound; it bears on how the families can be
case-analysed and on whether a statement was bent to fit.  The deslime
below replaces each computed index by a fresh variable and an equation
field, behaviour-preserving, one family per commit.

## After desliming

*Same branch, commits `fcbd0e6` (`Prv`) to `36c281c` (`ExpandAt`), one
commit per family.*

Every computed index was replaced by a fresh variable and an equation
field, behaviour-preserving: each new equation is discharged by `rfl` at
the constructions, and taken apart by `subst` (or passed on unchanged) in
the case analyses.  No proof needed anything else.

| family | before | after | commit | lines changed |
|---|---|---|---|---|
| `Prv` | 1 / 17 | 0 / 17 | `fcbd0e6` | 9 files, +30 -26 |
| `PrvC` | 1 / 17 | 0 / 17 | `67de18a` | 1 file, +5 -4 |
| `Holds` | 1 / 5 | 0 / 5 | `a5e402d` | 4 files, +28 -19 |
| `CTyped` | 1 / 7 | 0 / 7 | `e5cb52c` | 5 files, +19 -12 |
| `Step` | 7 / 7 | 0 / 7 | `4d6dd46` | 3 files, +53 -42 |
| `ATyped` | 1 / 6 | 0 / 6 | `74193dc` | 2 files, +10 -6 |
| `SLD.PTyped` | 1 / 8 | 0 / 8 | `11565ca` | 1 file, +10 -7 |
| `SLD.Expand` | 2 / 13 | 0 / 13 | `999f188` | 1 file, +26 -21 |
| `SLD.SLDStep` | 1 / 1 | 0 / 1 | `ef37e65` | 1 file, +11 -8 |
| `SLD.PTypedA` | 1 / 7 | 0 / 7 | `91dbf43` | 1 file, +9 -6 |
| `SLD.ExpandA` | 2 / 12 | 0 / 12 | `c70388e` | 1 file, +10 -8 |
| `SLD.SLDCStep` | 1 / 1 | 0 / 1 | `ac2eb6a` | 1 file, +4 -3 |
| `SLD.Base` | 2 / 7 | 0 / 7 | `967f287` | 1 file, +10 -9 |
| `SLD.ExpandAt` | 3 / 13 | 0 / 13 (tool: 7, the literal `0`) | `36c281c` | 1 file, +35 -32 |

**0 slimed constructors in 23 indexed families** (the tool's literal-`0`
report on `ExpandAt` aside).  Net diff against `2518be0` over
`LaxLogic/`: 16 files, +244 -187 lines.  Every module of `LaxLogic/QLL`
that built before builds (54 of 55, including `ProvFresh`, `Saturate`,
the test modules and `CLPBench`; `CLPWolfram` needs the Wolfram bridge
and was not built before either), as does `LaxLogic.Util.TurnstileTests`; every `#guard_msgs`-pinned axiom set
is unchanged (the build checks them), no pin line was edited, and no
`sorry` was introduced.  `#print axioms` of all 112 declarations the CLP
paper prints is identical before and after.

The equation fields follow the shape already used by `Derives.allE`:

* the instance of a `∀` is `B = A.openAt 0 t`;
* an instantiated clause head `.pred c.head (Tm.instAllList ts …)` is
  `.pred P us` with `P = c.head` and `us = Tm.instAllList ts …`, the same
  two equations as the immediate consequence operator `Tp`, so the head
  stays a constructor and a case analysis on a non-atomic goal still
  rules the clause case out by itself;
* a goal or forest at a position, `l ++ φ :: r`, is a variable with
  `gs = l ++ φ :: r`;
* the position `p.opens.length + i` of `ExpandAt.andR` is a variable `j`
  with `j = p.opens.length + i`.

What this shows about fidelity: no theorem statement changed (the 14
family definitions changed only by the equation fields), and no proof
needed more than `rfl` or `subst`.  So no statement had been bent to fit
the slime: the computed indices were only ever used where a `subst` on
the equation recovers them.
