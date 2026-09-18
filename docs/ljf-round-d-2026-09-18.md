# Round D, refuted as written and repaired — the p-fire eliminator families

*2026-09-18. `docs/ljf-simp-round1.md` §"Round D — designed, not yet executed
(§2.1)" is the only simplification the LJF campaign designed and never ran. It
is still unexecuted, and this file is what happened when it was picked up: the
design as written cannot be implemented, the obstruction is a real one and not
a tooling defect, and a different design reaching the same goal compiles. Both
verdicts carry a nine-line certificate anyone can paste and run.*

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

Both copies are still in the tree; neither has been touched.

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

## What is NOT changed by any of this

Round D's own warning stands and is reinforced: the `interpA_*_eq` equation
family stays as the safety net, the result types really do differ, and the
membership-oracle parameters on the `UStab` side are content, not noise. And
§2's "what should NOT be simplified" list — the E-guards, the E-res conjunct,
the parkedness hypothesis, the lexicographic offset pattern — is untouched:
every one of them is mathematical content forced by the minimality induction.
