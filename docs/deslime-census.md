# Green-slime census of the development

*Run 2026-08-18 on `frj-lax` at the merge `bd93d09`, with `#deslime`
(`Meta/Deslime.lean`, written the same day). This is the first time the
check has ever been run in this repository.*

Green slime (McBride): a **computed index in a constructor's return
type**. The unifier cannot invert it, so `cases`, `injection` and
dependent pattern matching cannot decompose the family. Computation in a
*premise* is harmless; only the conclusion matters.

Reproduce with:

    import Meta
    import LaxLogic.PLLNDCore
    #deslime PLLND.LaxND        -- the control: 0 of 12

## Result

| family | file | slimed / constructors |
|---|---|---|
| `PLLND.LaxND` | `PLLNDCore.lean` | 0 / 12 |
| `PLLND.IPLND` | `PLLNDCore.lean` | 0 / 10 |
| `PLLND.G4` | `PLLG4.lean` | 0 / 17 |
| `PLLND.G4p` | `PLLG4P.lean` | 0 / 17 |
| `PLLND.G4h` | `PLLG4H.lean` | 0 / 17 |
| `PLLND.G4sh` | `PLLG4Set.lean` | 0 / 16 |
| `PLLND.G4cTm` | `PLLG4Term.lean` | 0 / 16 |
| `PLLND.PD` | `PLLJudgmental.lean` | 0 / 13 |
| `LJFO.Stab` `RFocus` `LFoc` `Inv` | `LJFOCore.lean` | 0 / 3, 4, 5, 8 |
| `LJFO.StabH` `RFocusH` `LFocH` `InvH` | `LJFOHeight.lean` | 0 / 3, 4, 5, 8 |
| `IPC.Stab` `RFocus` `LFoc` `Inv` | `IPCFocused.lean` | 0 / 2, 4, 4, 7 |
| `PLLND.Focused.*` | `PLLFocused.lean` | 0 / 2, 4, 5, 8 |
| `LJF.*` | `LJF.lean` | 0 / 2, 4, 4, 7 |
| **`FRJ.FRJr`** | `FRJ/Calculus.lean` | **9 / 13** |
| **`FRJ.FRJi`** | `FRJ/Calculus.lean` | **4 / 8** |

**Zero slimed constructors in ~210, across eleven families written over
two years. Thirteen of twenty-one in the one family transcribed in a
week.**

## Where FRJ is slimed

`FRJr` — every axiom and **every join**; clean are `andR1`, `andR2`,
`impIn`, `circIn`:

| constructor | computed index | by |
|---|---|---|
| `axR` | `rm (gAt G) F` | `FRJ.rm` |
| `joinAt` / `joinAtP` / `joinAtF` | `joinCtxAt…` | `FRJ.joinCtxAt*` |
| `joinOr` / `joinOrP` / `joinOrF` | `joinCtxOr…` | `FRJ.joinCtxOr*` |
| `joinCirc` / `joinCircP` | `joinCtxOr…` | `FRJ.joinCtxOr*` |

`FRJi` — clean are `andI1`, `andI2`, `impNotIn`, `circNotIn`:

| constructor | computed index | by |
|---|---|---|
| `axI` | Θ = `nf G (rm (gAt G) F ++ gImp G ++ gCirc G)` | `FRJ.nf` |
| `orI` | Σ = `St₁ ++ St₂`, Θ = `nf G (cap Th₁ Th₂)` | `++`, `FRJ.nf` |
| `impInI` | Σ = `nf G (St ++ Lam)`, Θ = `nf G Th` | `FRJ.nf` |
| `axIC` | Θ = `vacZoneA G ats` | `FRJ.vacZoneA` |

## What this does and does not put in doubt

It does **not** make anything unsound. `FRJ.soundness` and
`FRJ.completeness` are sorry-free and pinned at `[propext, Quot.sound]`,
`#guard_msgs`-guarded in `FRJ/Audit.lean`, and the merged tree builds
green (8572 jobs).

What is in doubt is **fidelity of the statement**. The `Finset → List`
conversion introduced `nf` — a canonicalising normaliser — and welded it
into the indices of `axI`, `orI` and `impInI`, precisely so the computed
forms would come out syntactically equal and `cases` would go through.
The Lean judgment `FRJi G Σ Θ C` is therefore a statement about
*normalised* contexts. Whether that relation is the paper's relation has
not been checked. Three possibilities remain open:

1. the normalisation is conservative and the theorems are the paper's;
2. it is not, and completeness holds of a weaker judgment than claimed;
3. the calculus is genuinely incomplete and the slime hid the fact.

Distinguishing them needs the family re-stated slime-free — every
computed index replaced by a variable plus an equation field — and the
proofs re-run against it. Until then, FRJ's completeness should be read
as *proved of the Lean judgment as written*, which is the only thing a
kernel check ever certifies.

## Consequence for method

The rule is now constraint 5 of the `calculus-adoption` skill, checked at
stage 2 (transcription) rather than discovered at stage 3 (proof). See
`.claude/skills/calculus-adoption/reference/green-slime.md` for the fix
pattern and the reason the check needs a control.
