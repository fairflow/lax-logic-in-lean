# N4 on ◯-free stations: the refutation, the theorem, and the bounded form

Route (B), node N4 — *stabilisation of the interpolant chains at every
saturated parked station* — restricted to ◯-FREE stations (`CLAUDE.md` rule 8:
the IPC instance first).  Written 2026-09-06.  Every claim below is either
PROVED (named Lean declaration, pin measured), REFUTED (kernel-checked
counterexample), or OPEN — kept rigidly distinct.

Modules: `wip/ui_routeB_n4_lit.lean` (the refutation),
`wip/ui_routeB_n4.lean` (the theorem), `wip/ui_routeB_n4_cells.lean` (the
remaining structural features and the dividing line).

---

## 1 · What was refuted

`wip/ui_routeB_n3.lean` states N1 in two forms:

    EStabEq   p done    := Σ′ f₀, ∀ f ≥ f₀,  E_f = E_{f₀}          (LITERAL)
    AStabEq   p done G  := Σ′ f₀, ∀ f ≥ f₀,  A_f(G) = A_{f₀}(G)    (LITERAL)
    EStabilises / AStabilises                                       (INTERDERIVABLE)

and N3 forward (`hasUI_of_stabEq`) consumes the literal pair.

**The structural reason it cannot hold.**  `interpP`'s attack row for a parked
implication `Q ⊃ N ∈ done` at a goal `↑G` is (`LJF/OFuelPMin.lean`,
`truStationRowsP`)

    A_f(done ⇒ ↑Q)  ∧  A_f(N :: rest ⇒ ↑G)

— the guard at the FULL station `done`, which is route (B)'s retention
principle (`LJF/OFuelP.lean` (b), (c)).  When the goal `↑G` IS the antecedent's
own goal `↑Q`, that row contains the SAME call one fuel lower, so

    A_{f+1}(done ⇒ ↑Q)  ⊋  A_f(done ⇒ ↑Q)     as a formula,

and the chain is strictly ascending in `sizeNeg`.  The ∃p row of the same shape
(`eConjRowsP`) carries the same guard, so `E_{f+1}` DETERMINES `A_f`
(`guardOf`, `guard1`, `guard3`, `guard4`) and the ∃p chain is not constant
either.

**REFUTED, kernel-checked** (`wip/ui_routeB_n4_lit.lean`,
`wip/ui_routeB_n4_cells.lean`), on six designed cells — no enumeration, no
sweep (`CLAUDE.md` rule 9):

| cell | station | goal | feature | verdict |
|------|---------|------|---------|---------|
| (i)   | `[(a∨b) ⊃ ↑c]` | `↑(a∨b)` | the self-attack (`oimp` row) | `not_aStabEq1`, `not_eStabEq1` |
| (ii)  | `[(a∨b) ⊃ ↑c, (c∨d) ⊃ ↑a]` | `↑(a∨b)` | a 2-cycle, no self-attack used | `not_aStabEq2`, `not_aStabEq2cd` |
| (iii) | `[↓(a ⊃ ↑b) ⊃ ↑c]` | `↑↓(a ⊃ ↑b)` | the Dyckhoff shape's guard | `not_aStabEq3`, `not_eStabEq3` |
| (iv)  | `[↓↑a ⊃ ↑b]` | `↑↓↑a` | the shift shape (`simp` row) | `not_aStabEq4`, `not_eStabEq4` |
| (v)   | `[p ⊃ ↑c, ↑p]` | `↑c` | eliminated atom present, `pGuard` fires | **HOLDS** (`aStabEq5`, `eStabEq5`) |
| (vi)  | `[(a∨b) ⊃ ↑c, ↓↑c ⊃ ↑d]` | `↑d` | two parked implications, nested guards | `not_aStabEq6ab`, `not_aStabEq6d` |

Cell (ii) is refuted through its CROSS guards alone (`cross2_ab`,
`cross2_cd`), so pruning rows whose guard goal equals the aggregate's goal
would not rescue the literal form.  Cell (vi)'s outer goal `↑d` is neither
antecedent's own goal, and is refuted through the NESTED guard alone: the outer
aggregate determines the inner one one fuel down (`guardAtom`, `guard6`), and
that one ascends.

**The dividing line is SATURATION, not weight.**  Cell (v) is the only one that
stabilises literally, and it is the only one that is not saturated: the parked
implication's atom has arrived, `findFire` fires it, and the recursion leaves
for a residual station retaining no compound implication.  From fuel 3 the ∀p
aggregate is literally `⊤` (`a5_eq`) and the ∃p aggregate is literally
`⊤ ∧ ↑c ∧ ↑p`'s guarded form (`e5_eq`).  So the refutation is exactly
co-extensive with `Saturated done` plus a retained compound implication —
which is precisely the hypothesis `hasUI_of_stabEq` was stated under.
`hasUI_of_stabEq` has no instance of that shape.

**`FuelIrrelevance` is moot.**  Its consumer `eStabEq_of_fuelStep` needs a fuel
at which the recursion repeats.  There is none:

    not_fuelStep1A : ¬ FuelStep p [] cell1 (some goal1) f     (every f)
    not_fuelStep1E : ¬ FuelStep p [] cell1 none f             (every f)

so N4's LITERAL (termination-of-the-recursion) reading is false, and
`FuelIrrelevance` — whatever its truth value — cannot be used.

**The measured chains** (`chainSizes`, `decide +kernel`, `p := "p"`), `sizeNeg`
at fuels 0–5:

| chain | 0 | 1 | 2 | 3 | 4 | 5 | ratio |
|-------|---|---|---|---|---|---|-------|
| (i) `E_f` | 4 | 18 | 39 | 93 | 204 | 465 | ≈ 2.2× |
| (i) `A_f(↑(a∨b))` | 2 | 23 | 74 | 185 | 446 | 929 | ≈ 2.1× |
| (iii) `A_f(↑↓(a ⊃ ↑b))` | 2 | 17 | 43 | 81 | 168 | 297 | ≈ 1.8× |
| (iv) `A_f(↑↓↑a)` | 2 | 17 | 47 | 104 | 215 | 383 | ≈ 1.8× |
| (v) `A_f(↑c)` | 2 | 2 | 2 | 4 | 4 | 4 | **constant** |
| (vi) `A_f(↑d)` | 2 | 26 | 80 | 283 | 922 | 3033 | ≈ 3.3× |

Geometric in every saturated cell; the ratio rises with the number of retained
implications, since each contributes a guard at the full station.

---

## 2 · What is PROVED

### 2.1 N3 forward, interderivably

    hasUI_of_stabilises : SatE2P p → SatA2P p → Saturated done → ParkedCtxP done →
                          EStabilises p done → AStabilises p done G → HasUI p done G

`[propext, Classical.choice, Quot.sound]`, `wip/ui_routeB_n4.lean`.  Where
`hasUI_of_stabEq` REWROTE with the literal equation, this COMPOSES, and
composition in LJF◯ is `cutInv` (`LJF/OPolInv.lean`, proved 2026-09-06).
`cutInv` enters four times: once in `minE` (bring `E_e` down to `E_{f₀}`),
three times in `minA` (bring `E_e` down; compose `A_k` with the ∀p
stabilisation; discharge the residual `E_k` that the previous cut leaves beside
`Δ`).  Contraction is free from `Inv.wk`.

### 2.2 N4 on ◯-free stations

Uniform interpolation for IPC is PROVED in this repository —
`LJFIPC.uniform_interpolation_IPC` (`LJF/Complete.lean`), unconditional,
`[propext, Classical.choice, Quot.sound]`, with the ∀p half E-relativised
(`exI p Γ :: Δ ⊢ allI p Γ φ`), which is literally `IsUIPair.minA`'s shape.  So
on ◯-free stations N4 follows by TRANSPORT, and it does:

    hasUICF_circFree   : CircFreeCtx done → CircFreeN G → HasUICF p done G
    n4_circFree_uncond : SatE2P p → SatA2P p → Saturated done → ParkedCtxP done →
                         CircFreeCtx done → CircFreeN G →
                         EStabilises p done × AStabilises p done G

both `[propext, Classical.choice, Quot.sound]`.

The pair is `E := negOfO (∃p ⌊done⌋)`, `A := negOfO (∀p (⌊done⌋ ⇒ ⌊G⌋))`
(`uiE`, `uiA`).  Erase the polarised derivation (`Inv.sound`), apply the IPC
property, re-focalise (`polInvT` at `tru`, `polInvL` at `lax`).  `polInvT` holds
at EVERY polarised context, so `done` need not be a `negOfO`-image.  Three
transfer families were needed and are proved: `isIPL_erasePos`/`isIPL_eraseNeg`
(a ◯-free polarised formula erases to IPL), `pfree_erasePos`/`pfree_eraseNeg`,
`pfreeP_posOfO`/`pfreeN_negOfO`.

**`minE` holds at EVERY judgment.**  At `lax`, `laxImpEmpty` and `laxAndEmpty`
empty the `⊃` and `∧` goals and `CircFreeN` excludes the box, so the goal is a
shift `↑P`; the erasure lands on `◯⌊P⌋`, `LaxND.erased` brings it down to `⌊P⌋`
(context and goal are `isIPL`, so `erase` is the identity on them), `exI_min`
applies, and `polInvL` re-focalises.  No `tru`-only variant was needed on that
account.

**One restriction, and it is not an artefact.**  `IsUIPair.minE`/`minA` quantify
over p-free `Δ`, `ψ` that may CARRY `◯`.  Pitts's theorem cannot supply that:
`exI_min` requires `isIPL` of the test formula, and `⌊ψ⌋ ⊢ erase ⌊ψ⌋` fails for
a `◯` under an antecedent.  A pair against ◯-carrying test data at a ◯-free
station IS uniform interpolation for PLL on ◯-free cells — what route (B) is
being built to prove — so the transported pair is `IsUIPairCF` (`Δ`, `ψ`
additionally ◯-free) and N3 backward is re-derived for it
(`stabilises_of_hasUICF`).  Nothing is lost for N4, because

    interpP_circFreeN : CircFreeCtx todo → CircFreeCtx done → OptCircFree g →
                        CircFreeN (interpP p f todo done g)     [propext, Quot.sound]

certifies the only test data `stabilises_of_hasUI` uses.

---

## 3 · The bounded form — statement, weight design, verdict

`n4_circFree_uncond` gives a threshold but no closed form for it: the
`EStabilises`/`AStabilises` witnesses are `n + m`, where `n` and `m` are the
cofinality thresholds `SatE2P`/`SatA2P` return for two specific derivations
(`u.soundE`, `u.soundA`).  Both derivations are determined by `done` and `G`, so
the least stabilisation fuel IS a function of the station and the goal alone.
The bounded statement asks for it in closed form:

    N4circFree p := ∀ done G, Saturated done → ParkedCtxP done →
        CircFreeCtx done → CircFreeN G →
        (∀ f ≥ W done,     E_f ⟛ E_{W done}) ×
        (∀ f ≥ W′ done G,  E_f, A_f ⟛ E_f, A_{W′ done G})     (A-side E-relativised)

with `W`, `W′` read off the recursion.

### 3.1 The weight, designed from the rows

`interpP`'s cost at a saturated station is a sum over `splits done`, one row per
member.  Writing `w` for Dyckhoff's G4ip weight of a formula:

| member | ∃p row | fuel demand |
|--------|--------|-------------|
| `↑a` | `pGuard p a ⊤ ↑a` | 0 — a leaf |
| `a ⊃ N` | `pGuard p a ⊤ (a ⊃ E(N :: rest))` | `1 + W(N :: rest)` |
| `Q ⊃ N` compound | `(↓A(done ⇒ ↑Q) ⊃ E(N :: rest)) ∧ E(rest)` | `1 + max(W′(done, ↑Q), W(N :: rest), W(rest))` |

and at a goal `G` the ∀p aggregate adds the goal-inversion prefix, costing
`1 + W′` at each immediate subformula of `G` (`invertPos` branches for `⊃`,
the two disjuncts for `↑(P₁∨P₂)`, the body for `↑↓M`).

The recursion for `W` therefore descends on the station EXCEPT at the guard
`W′(done, ↑Q)`, which is at the FULL station.  That is the same non-descent
that stopped the cofinality proof at the founding (§4.11) and the height-first
founding (§4.13), now localised to one entry of the weight table.  A candidate
that closes it must bound `W′(done, ↑Q)` in terms of `done` alone; the natural
attempt, `W′(done, ↑Q) ≤ 3 · (Σ_{X ∈ done} w X + w Q)` with the constant from
§4.12's measured "fuel ≈ 3 × derivation height", is the one to test.

### 3.2 Verdict, and what the cells say

The bounded statement is **OPEN**, and the cells do not refute it — they
constrain it:

* The chains ascend without bound as FORMULAS (§1), so `W` bounds an
  INTERDERIVABILITY threshold and can never be read off a fixed point of the
  recursion.  Any candidate proof must exhibit the derivations, not an equality.
* Cell (v) shows `W` is not monotone in the station's weight: adding `↑p` to
  `[p ⊃ ↑c]` makes the station heavier and the threshold SMALLER (3, and the
  chain literally constant).  A weight that is a plain sum over `done` is
  therefore refuted as a candidate; `W` must see saturation.
* Cell (vi) shows `W` is not a function of the goal's own subformulas: the
  chain at `↑d` is driven by the guard chains at `↑(a∨b)` and `↑↓↑c`, neither of
  which is a subformula of the goal.  So `W′ done G` must range over the
  antecedents of `done`, not over `G`.
* Cell (ii) shows the guard graph can CYCLE (`↑(a∨b) → ↑(c∨d) → ↑(a∨b)`), so a
  recursion on "the guard of the guard" is not well-founded either.  `W` must be
  founded on something that decreases around a cycle — the natural candidate is
  the ∃p interpolant's own strength, i.e. the descending chain `E_0 ⊇ E_1 ⊇ …`,
  not a syntactic weight.

**No cell refutes N4 itself**, and none could: N4's ◯-free instance is now
PROVED (§2.2), so a cell whose chain failed to stabilise up to interderivability
would contradict a machine-checked theorem, and the error would be in the cell.

### 3.3 What the proof build should be

For the bounded form: induction on `μ = (number of retained compound
implications in `done`, station weight, `sizeOf`)` — the first component is what
the guard rows do NOT increase (the guard is at the same station, so the same
count) and what the fire and residual rows strictly decrease.  The guard entry
is then handled not by descent but by the ALREADY-PROVED interderivable
stabilisation at that station and goal, i.e. `n4_circFree_uncond` used as an
inner hypothesis — which is legitimate because the guard's goal `↑Q` is
strictly smaller than the aggregate's when the aggregate's goal is not `↑Q`, and
when it IS `↑Q` the row is the self-attack, whose disjunct is implied by the
aggregate above it and so contributes nothing.  That last observation — the
self-attack disjunct is redundant up to interderivability — is the lemma to
prove first; it is what makes the interderivable chain stabilise while the
literal one does not, and it is stated but not proved anywhere yet.

For the MODAL case (rule 8's second half): the transport of §2.2 does not
survive — there is no PLL analogue of `uniform_interpolation_IPC` to transport
from; that is the open problem.  What does survive is the technique: `polInvT`
and `polInvL` cross every polarised sequent in both directions, so any PLL-side
uniform interpolation result transports to LJF◯ cells verbatim, and
`interpP_circFreeN`'s pattern (thread the invariant, kill the unreachable arms
on the hypotheses) is the shape of every such preservation proof.

---

## 4 · Declarations, with pins

| declaration | module | pin |
|---|---|---|
| `not_aStabEq1`, `not_eStabEq1` | `n4_lit` | `[propext, Quot.sound]` |
| `not_aStabEq2`, `not_aStabEq2cd` | `n4_lit` | `[propext, Quot.sound]` |
| `not_aStabEq3`, `not_eStabEq3` | `n4_lit` | `[propext, Quot.sound]` |
| `not_fuelStep1A`, `not_fuelStep1E` | `n4_lit` | `[propext, Quot.sound]` |
| `not_aStabEq4`, `not_eStabEq4` | `n4_cells` | `[propext, Quot.sound]` |
| `aStabEq5`, `eStabEq5` | `n4_cells` | `[propext]` |
| `not_aStabEq6ab`, `not_aStabEq6d` | `n4_cells` | `[propext, Quot.sound]` |
| `chainSizes` | `n4_cells` | `[propext]` |
| `hasUI_of_stabilises` | `n4` | `[propext, Classical.choice, Quot.sound]` |
| `hasUICF_circFree` | `n4` | `[propext, Classical.choice, Quot.sound]` |
| `interpP_circFreeN`, `circFreeInterpP` | `n4` | `[propext, Quot.sound]` |
| `stabilises_of_hasUICF` | `n4` | `[propext, Classical.choice, Quot.sound]` |
| `n4_circFree`, `n4_circFree_uncond` | `n4` | `[propext, Classical.choice, Quot.sound]` |

`Classical.choice` is inherited from `cutInv`'s `Type`-valued packaging
(`LJF/OPolInv.lean` §4b) and from `uniform_interpolation_IPC`; from nowhere
else.  Every refutation and every erasure transfer is at `[propext,
Quot.sound]` or below.
