# Round D, refuted as written and repaired — the p-fire eliminator families

*2026-09-18. `docs/ljf-simp-round1.md` §"Round D — designed, not yet executed
(§2.1)" is the only simplification the LJF campaign designed and never ran.
This file is what happened when it was picked up: the design as written cannot
be implemented, the obstruction is a real one and not a tooling defect, a
different design reaching the same goal compiles and was carried out for one
pair — and then the measurement said the prize the round was estimating is not
there. Every verdict below carries a certificate anyone can paste and run.*

## What Round D asks for

Fourteen families — `TInv`/`UInvG`, `TStab`/`UStab`, `TRF`/`URF`, `TLF`/`ULF`,
`TpElim`/`UpElim`, `TpLF`/`UpLF`, `TpInv`/`UpInvG` — have the same clause
skeleton in each pair. The E-side emits conjunct fires through the `∃p`
interpolant; the A-side emits attack disjuncts into the `∀p` aggregate. Round D:

> one family parametrised by an emission record (the two fire continuations
> plus the result-type flavour), instantiated twice.

Measured today, so the prize is known:

| file | E-side | A-side | total |
|---|--:|--:|--:|
| `LaxLogic/Focusing/LJF.lean` | 258 | 397 | **655** |
| `LJF/O.lean` | 293 | 547 | **840** |

`LJF/O.lean` is untouched. In `LaxLogic/Focusing/LJF.lean` one pair —
`TLF`/`ULF` — has since been unified; see the last two sections for what that
cost, what it bought, and why the other six are not worth doing.

## Refuted as written: an emission RECORD cannot carry the recursive calls

The families are well-founded recursions inside a mega-mutual —
`termination_by … sizeOf s`, discharged by the farms `ljf_dec_e` and
`ljf_dec_a`. Parametrising by a record of *functions* means passing a mutual
sibling as a function argument, and that is refused for a reason that belongs
to termination, not to Lean's implementation:

```lean
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree

def viaArg (f : Tree → Nat) : Tree → Nat
  | .leaf => 0
  | .node a b => f a + viaArg f b

mutual
def A : Tree → Nat
  | .leaf => 0
  | .node a b => viaArg B a + A b
termination_by t => sizeOf t

def B : Tree → Nat
  | .leaf => 1
  | .node a b => A a + B b
termination_by t => sizeOf t
end
```

```
error: failed to prove termination
a b a✝ : Tree
⊢ sizeOf a✝ < 1 + sizeOf a + sizeOf b
```

**Read the goal.** `a✝` is an *arbitrary* tree. Handing `B` to `viaArg` throws
away the call site, so the checker must bound the recursion at every possible
argument, and a syntactic measure cannot. This is the sharpest statement yet of
the mechanism behind two of this campaign's standing refusals — the `OCore`
station factoring, and the second half of the `aSound` triple — and it explains
the one case where the same move *succeeded*: in `LJF/OFuelSound.lean` and
`OFuelPSound.lean` the measure is the **fuel**, and `f < f + 1` holds for every
argument, so throwing away the call site costs nothing. **A recursive call
passed under a lambda survives a fuel measure and not a syntactic one.**

## Repaired: index the family by a MODE, not by functions

Every recursive call must stay a syntactic call the equation compiler can see.
So the two sides become one family indexed by a mode, dispatching with
`match m`, with **both the result type and the measure computed from the
mode** — which is precisely what lets the E and A measures, whose first
components differ (`sum3 done` against `sum3 done + 3 ^ wPos P₀ + 2`), live in
one definition:

```lean
inductive Mode where | E | A

abbrev Res : Mode → Type
  | .E => Nat
  | .A => List Nat

mutual
def F : (m : Mode) → Tree → Res m
  | .E, .leaf => 0
  | .A, .leaf => []
  | .E, .node a b => G a + (F .E b)
  | .A, .node a b => G a :: (F .A b)
termination_by m t => ((match m with | .E => 0 | .A => 1), sizeOf t)

def G : Tree → Nat
  | .leaf => 1
  | .node a b => (F .E a) + G b
termination_by t => (0, sizeOf t)
end
```

Accepted, and `#print axioms F` reads `[propext, Quot.sound]`.

**One trap, and it cost a compile.** With `Res` written as a plain `def` the
same file fails with

```
failed to synthesize  OfNat (Res Mode.E) 0
```

A computed result type must be **reducible** — `abbrev`, or `@[reducible] def`
— or instance synthesis will not see through it. Worth carrying: this is the
first time in the campaign that a *type-level* function's reducibility, rather
than a term's, decided whether a design compiles.

## What the real refactor therefore has to be

* **A mode carrying the A-side's extra data.** `ULF`, `UInvG`, `UpElim` and
  their siblings take `{L : List Neg}` plus `hV : interp p [] done (some …) =
  nOrAll L` and the two membership oracles `qmem`/`dmem`; the E-side takes
  none of them. Those become *fields of the `A` constructor of the mode*, so
  the unified family has one parameter where today there are four on one side
  and zero on the other.
* **A computed target.** `TLF`/`ULF` are the easy pair: both return
  `LFoc (interp p [] done none :: K) H _`, differing only in the target
  positive (`P` against `orChain L`). They unify over a `target` parameter
  with no computed result type at all. `TpElim`/`UpElim` are the hard pair —
  `Stab … P₀` against `Inv … [] (nOrAll L)`, genuinely different heads, so
  they need the `abbrev` above.
* **One farm, or a mode-split farm.** `ljf_dec_e` and `ljf_dec_a` are written
  against different first components. Unified, the obligations are
  mode-dependent; the farms merge or the `decreasing_by` splits on the mode
  first.
* **Do the pairs in this order**, cheapest first, compiling each:
  `TLF`/`ULF` (48 lines, one target parameter), `TRF`/`URF`, `TpLF`/`UpLF`,
  `TInv`/`UInvG`, `TStab`/`UStab`, `TpInv`/`UpInvG`, `TpElim`/`UpElim` last.
  `LaxLogic/Focusing/LJF.lean` first, because it is the zero-import IPC
  control and its failure is cheapest to read; `LJF/O.lean` second, where the
  same shapes carry the lax flag.

## Executed: `TLF`/`ULF`, and then measured — the prize is not there

The repair was carried out on `LaxLogic/Focusing/LJF.lean` for the one pair the
design fits best. `TLF` and `ULF` are gone; in their place is `XLF` over
`LFMode`, with the two call sites (inside `TStab` and `UStab`) passing `.E hp`
and `.A _ hV qmem dmem`. The removed bodies are kept verbatim in
`Archive/ljf-round-d-superseded.lean`, per round 1's rule.

**It compiles, and the axioms are unchanged** — every `#guard_msgs`-guarded
`#print axioms` at the foot of the file passes untouched, and `lake build` is
green at 8,748 jobs.

Four things had to be got right, and each is worth carrying:

1. **`set_option maxHeartbeats 8000000 in` governs the `mutual` that follows
   it.** Inserting the mode declaration between the two silently dropped the
   block to the default 200,000 and the farm timed out in `whnf`. The symptom
   (a `simp` timeout in an unrelated member) points nowhere near the cause.
2. **The measure must be written inline, not as a named function.** With
   `termination_by … => (m.rank, sizeOf lf)` the obligations read
   `sum3 done < (LFMode.E hp).rank` — the farms' `simp only [sum3, …]` has no
   clause for `LFMode.rank`, so nothing reduces. Written as a `match m with …`
   in the measure itself, it iota-reduces per obligation.
3. **The mode-polymorphic arms leave `m` a variable**, so even inline the match
   is stuck for the calls that do not mention the mode. `decreasing_by` opens
   with `all_goals (try cases m)`.
4. A computed *result* type must be `abbrev` (above).

**And then the measurement, which is the real result.** Round D justified
itself by "the *same* clause skeleton" across all seven pairs. That is true of
the clause *patterns* and false of the bodies:

| pair | E lines | A lines | similarity | identical lines |
|---|--:|--:|--:|--:|
| `TpElim`/`UpElim` | 63 | 83 | 0.47 | 34 |
| `TInv`/`UInvG` | 39 | 47 | 0.33 | 14 |
| `TpInv`/`UpInvG` | 39 | 56 | 0.27 | 13 |
| `TStab`/`UStab` | 45 | 105 | 0.24 | 18 |
| `TpLF`/`UpLF` | 20 | 33 | 0.08 | 2 |
| `TRF`/`URF` | 21 | 32 | 0.04 | 1 |

The A-side runs 1.5–2.3× longer and a quarter to a half of the lines coincide.
`TRF`/`URF` share **one** line: their `.init` arms do different mathematics —
`TRF` assembles an atom conjunct through `atomAssemble`, `URF` rewrites by
`interpA_atom_eq` and introduces into the aggregate. **Round D's estimate of
350–500 lines is not supported**, and the one pair that did fit cost
**+23 lines**, because the mode declaration is a fixed overhead of about fifty
that only amortises over pairs that genuinely share.

This is the campaign's standing lesson arriving for the fifth time, now about a
*skeleton* rather than a text: **similarity of the clause patterns overstates
what can be shared; the number that matters is how much of the body is common.**

## Why the change was kept anyway

Not for lines. For time. Measured on this machine, same imports, same day:

| | wall clock |
|---|--:|
| `LaxLogic/Focusing/LJF.lean` at `HEAD` | **11 min 27 s** |
| the same file with `XLF` | **9 min 42 s** |

**−1 min 45 s, −15%**, on the slowest single file in the repository. Round 1
made compile time a first-class metric (its Rule 4) and attributed what
remained to "the mega-mutual's WF-compilation and the farms'
failing-alternative search". That is exactly what one fewer member in the
mutual, and one fewer farm to search, buys. The +23 lines are the price of the
mode; the mode is also the "single carrier for the lax flag" that round 1
wanted for the ◯ extension, so the next pair costs nothing to declare.

**Recommendation for the remaining six pairs: do not.** On the measurement
above, only `TpElim`/`UpElim` (34 shared lines of 63/83) could repay the work,
and it is the pair with the most delicate termination indices — the one round 1
itself called "the deepest refactor". The rest would add mode machinery to
bodies that do not coincide.

## What is NOT changed by any of this

Round D's own warning stands and is reinforced: the `interpA_*_eq` equation
family stays as the safety net, the result types really do differ, and the
membership-oracle parameters on the `UStab` side are content, not noise. And
§2's "what should NOT be simplified" list — the E-guards, the E-res conjunct,
the parkedness hypothesis, the lexicographic offset pattern — is untouched:
every one of them is mathematical content forced by the minimality induction.
