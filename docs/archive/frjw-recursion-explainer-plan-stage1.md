# Plan for an FRJW/GBUW recursion explainer

> **Status against HEAD `0cbb206` (2026-09-02, Fable).**  This plan was
> written by an Opus subagent against the stage-1 commit `637dfcd`
> (search file 1093 lines).  Two later commits overtook parts of it
> before it landed; the body is kept verbatim (archive convention) and
> the deltas are recorded here so nobody re-does settled work.
>
> * **Stage 2 (`dd88424`)** stripped the chase: `QD`, `hstuck`, the
>   pair-`V` chase branch, `wgW_chase`, and `decRP` are gone; the corner
>   runs `findCMT → R₀ → certificate test → refutedCleanly_circ_certs |
>   totalityW → L⊃ᵢ by size-drop`.  Consequences for the text below:
>   §A.1's measure component 2 (`vRem`) is now paid by nothing (only
>   two `IHW` sites remain, both passing `V := []`); §B.1 stages
>   S5a-i/ii/iv no longer exist; §B.5's free-standing "chase cell"
>   cannot be traced (there is no chase); the §A.1 paragraph "The chase,
>   and why pairs" is history.  Search file now 939 lines.
> * **Stage 3 (PROPOSED, dry-run compiles at 852 lines)** retires the
>   pair-`V` measure altogether (`wgW`/`WgLtW`/`vRem`/`sfPairs` and the
>   `hVsf`/`hregV` plumbing), reverting to `wgC = (unclosed, tpC,
>   seqSize)`.  If it lands, §C.2 (`IHi`/`IHr`, retiring the `hregV`
>   payloads) is subsumed entirely, and §C.5's `wfFixMeasure` wrapper
>   would be extracted from the reverted form.
> * **The bare decision (`055f621`)** did what §D.3 flags as UNCERTAIN:
>   `decideGbuWData G : GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)` exists,
>   pinned `[propext, Quot.sound]`, obtained without touching the
>   abstract `Prop`-valued interface (root scan `rootDisproof?` over the
>   instantiated store, `decideOfStore`).  It was small.  §D.3's
>   "asymmetry" paragraph is therefore resolved, not open.
> * Line numbers in the body refer to `637dfcd` throughout, as the
>   provenance paragraph says.
>
> Still live and unaffected: §A.2–A.7, §B.2–B.4 and the primary
> example in §B.5, §C.1, §C.3, §C.4, §C.6–C.10, §D.1–D.2, §D.4–D.5.

**This document is a PLAN, not the explainer.**  It sets out, in four
commissionable parts, what an explainer of the `decideGbuW` chain would
have to contain, how the proof states could be made inspectable, which
compaction combinators the proof text actually supports, and how to
present the `⊕'` framing.  Each part is separable; the menu at the end
gives effort estimates so parts can be commissioned individually.

**Provenance of every line number below.**  Branch
`claude/frjw-w1-w2-lean-5aabff` at `637dfcd` ("compaction stage 1 —
invariant stripped, T-B monos archived").  File sizes at that commit:
`wip/gbu_frjw_dichotomy.lean` 132, `wip/gbu_frjw_search.lean` 1093,
`wip/gbu_frjw_closure.lean` 1805, `wip/gbu_frjw_saturate.lean` 2471,
`wip/gbu_frjw_corner.lean` 654, `wip/gbu_frjw_circdb.lean` 544,
`wip/gbu_frjw_exclusion.lean` 47.  Line numbers move if the compaction
proceeds; the explainer should be regenerated against a pinned hash and
say which.

Everything cited here is PROVED, sorry-free, `#guard_msgs`-pinned
`[propext, Quot.sound]` (some lighter: `pledge_of_le` and
`impInI_mono_sub` at `[propext]`).  Where I am uncertain I say so
explicitly; those places are marked **UNCERTAIN**.

---

## PART A — What is being recursed on, exactly

### A.0 The four objects the recursions move between

Stated once, so the rest can be terse.

    WSeq            = .reg (t : Tag) (Γ : List Form) (C : Form)
                    | .irr (St Th : List Form) (C : Form)
                                            (dichotomy 58–60)

    WDerivable G s  : Prop   — `Nonempty (FRJWr …)` / `Nonempty (FRJWi …)`
                                            (dichotomy 63–66)

    WSaturated G D  = (∀ s, D s → WDerivable G s)
                    ∧ (∀ s, WDerivable G s → ∃ s', D s' ∧ WSubsumes s s')
                                            (dichotomy 78–80)

    WSearchOk G D : Bool × List Form × Form → Type
      | (true,  Ψ, C) => (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G →
                         ¬ WEvalR D Ψ C → GbuRC G Ψ C
      | (false, Ω, C) => (∀ X ∈ Ω, X ∈ sfL G) →
                         (C.isCirc = false → ∀ X ∈ Ω, X ∈ gHat G) →
                         C ∈ sfR G →
                         WUnrefutedBelow G D Ω C → GbuIC G Ω C
                                            (dichotomy 121–131)

A *cell* is the triple `(reg?, Ψ, C)`; the searcher additionally carries
a *visited-pair list* `V : List (Form × Form)` which is **not** part of
the cell (it does not appear in `WSearchOk`) but is part of the measure.

There are six genuine recursions in the chain, plus a handful of
list-scanning ones.  Each is treated below in the order the chain uses
them.

---

### A.1 `searchW`'s `main` — well-founded on the 4-lex measure

**File**: `wip/gbu_frjw_search.lean:368–1056`.

**Recursion principle.**  `wgLtW_wf.fix` (search:376), where

    wgLtW_wf : WellFounded WgLtW                      (search:237)
    WgLtW x y = x.1 < y.1 ∨ (x.1 = y.1 ∧ WgLt x.2 y.2)  (search:234)

`WgLtW` is proved well-founded by rewriting it to `Prod.Lex (· < ·) WgLt`
and appealing to `WellFounded.prod_lex Nat.lt_wfRel.wf wgLt_wf`
(search:237–254).  `WgLt` is the pre-existing 3-lex order of
`wip/gbu.lean:305`; so the new measure is the old one with a second
coordinate spliced in.

**The measure.**

    wgW G reg Ψ C V = (unclosed G Ψ, vRem G V, tpC reg C, seqSize Ψ C)
                                            (search:229–231)

    sfPairs G = (sfR G).flatMap (fun A => (sfR G).map (fun C => (A, C)))
    vRem G V  = ((sfPairs G).filter (fun q => decide (q ∉ V))).length
                                            (search:223–227)

with, from elsewhere in the development,

    unclosed G Ψ = (sfL G).countP (fun X => !cloB Ψ X)   (gbu.lean:262)
    seqSize Ψ C  = (Ψ.map Form.size).sum + C.size        (gbu.lean:292)
    tpC reg C    = if reg then 2 else if C.hasCirc then 1 else 0
                                                        (gbu_circ.lean:1631)

**Motive, as it literally appears.**  The `fix` is applied to the motive
of `main`, whose statement is (search:372–375):

```lean
have main : ∀ x : Nat × Nat × Nat × Nat, ∀ p : Bool × List Form × Form,
    ∀ V : List (Form × Form), (∀ q ∈ V, q.1 ∈ sfR G ∧ q.2 ∈ sfR G) →
    (p.1 = true → V = []) →
    wgW G p.1 p.2.1 p.2.2 V = x → WSearchOk G D p
```

so the motive handed to `wgLtW_wf.fix` is

    fun x => ∀ p V, (∀ q ∈ V, …) → (p.1 = true → V = []) →
             wgW G p.1 p.2.1 p.2.2 V = x → WSearchOk G D p

Three things to say about this in the explainer:

1. The `wgW … = x` equation is the standard device for turning a
   well-founded fixpoint over *measure values* into one over *cells*:
   the recursive call supplies its own cell and proves its measure drops
   below `x`, and `hx ▸` (search:383) transports.
2. The motive is **Type-valued** (`WSearchOk … : Type`), so this is a
   `def`-shaped recursion producing terms, not a `theorem`.  That is the
   whole point: the positive side returns the `Gbu◯` derivation.
3. The two extra parameters `hVsf : ∀ q ∈ V, q.1 ∈ sfR G ∧ q.2 ∈ sfR G`
   and `hregV : p.1 = true → V = []` are side conditions on `V`, carried
   by every recursive call.  They are **not** the stripped goal-set
   invariant (docs/frjw-compaction.md:14 records this explicitly); they
   are what makes `vRem` a legitimate measure (`hVsf`) and what confines
   the chase to irregular mode (`hregV`).

**The two induction hypotheses.**  Immediately after the `fix`, two
derived hypotheses are installed:

```lean
have IHW : ∀ (q : Bool × List Form × Form) (V' : List (Form × Form)),
    (∀ q' ∈ V', q'.1 ∈ sfR G ∧ q'.2 ∈ sfR G) →
    (q.1 = true → V' = []) →
    WgLtW (wgW G q.1 q.2.1 q.2.2 V') (wgW G reg Ψ C V) →
    WSearchOk G D q                                      (search:378–383)

have IH : ∀ q : Bool × List Form × Form,
    WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G reg Ψ C) →
    (q.1 = true → V = []) →
    WSearchOk G D q                                      (search:384–388)
```

`IHW` is the full 4-lex hypothesis: it lets the callee *change* `V`, and
demands the `V`-side conditions back.  `IH` is the convenience form for
the overwhelming majority of steps, which keep `V` fixed: it takes only
the OLD 3-lex `WgLt` on `wgC` and lifts it by

    wgW_of_wgC : WgLt (wgC G r' Ψ' C') (wgC G r Ψ C) →
                 WgLtW (wgW G r' Ψ' C' V) (wgW G r Ψ C V)   (search:259–265)

Only three call sites use `IHW`: search:445 (the irregular `R⊃ₙᵢ`),
search:533 (totalityW's callback into the regular stratum), search:673
(the chase).  27 call sites use `IH`.  In the explainer this is the
cleanest way to say what the innovation costs: *one* of thirty steps
needs the new coordinate.

**What one step consumes and produces.**  A step consumes a cell
`(reg, Ψ, C)`, the hypotheses `hΨ` (context ⊆ `Sf^L G`), `hC` (goal ∈
`Sf^R G`), the mode-specific `hΩc` / nothing, and the negative database
fact (`¬ WEvalR D Ψ C` regular, `WUnrefutedBelow G D Ψ C` irregular).
It produces a `Gbu◯` derivation `GbuRC G Ψ C` or `GbuIC G Ψ C` — a
*term*, built by applying one `Gbu◯` constructor to the terms returned
by the recursive calls.  Every branch ends in either such a constructor
application or `absurd (…) hne`: the negative fact is contradicted
because the database would have had a row.

**Why each measure component is needed, and which steps drop it.**

| # | component | dropped by | sites |
|---|---|---|---|
| 1 | `unclosed G Ψ` | the two `R⊃ₙ` rules — adding an antecedent not yet in `Cl(Ψ)`, via `unclosed_lt` | irregular `rimpNII` search:448; regular `rimpNI` search:909; totalityW's regular-stratum callback search:536 |
| 2 | `vRem G V` | the chase only, via `wgW_chase` | search:681 (one site) |
| 3 | `tpC reg C` | mode release regular → irregular (`wgFocus`, `tpC_false_lt_true`) and the `◯`-free antecedent (`wgTpLt` + `tpC_free_lt_circ`) | search:827, 927, 932, 952 (`wgFocus`); search:644 (`wgTpLt`) |
| 4 | `seqSize Ψ C` | every structural descent (`wgKeep`) | 20 sites |

Component 1 must come first because `R⊃ₙ` *grows* the context, so
neither 3 nor 4 can pay for it; and because an `unclosed` drop resets
both `V` (`wgW_drop`, search:291–295) and the rest for free.
Component 4 cannot pay for the chase because a chase step goes from goal
`◯Z` into antecedent `A` whose size the goal does not bound — the code
names the licence cell in a comment: "`A = ◯p` against goal `◯r`"
(search:214).  Component 3 is graded by whether the goal *contains* a
`◯`, not whether it *is* one (gbu_circ.lean:1622–1629 gives the reason:
`R∧ᵢ` at `C₁ ∧ ◯C₂` would raise the latter).

`wgKeep` (search:143–152) carries an auto-param for the `tpC`
side-condition trying, in order, `Nat.le_refl`, `tpC_false_mono orL'`,
`tpC_false_mono orR'`, `tpC_le_circ` — worth one sentence in the
explainer, because it is why 9 of the 20 descent sites need no `tpC`
argument at all.

**The chase, and why pairs.**  The chase is the single site search:660–682.
Its guard is:

```lean
have hAnotV : (A, Form.circ Z) ∉ V := by
  intro hmem
  refine hnQ (Or.inr ⟨?_, ?_, ?_⟩)                       (search:662–672)
```

i.e. the branch is reached only when `(A, ◯Z)` is *not* already visited,
because otherwise the earlier decidable test `QD` (search:479–485) would
have classified `A` as chase-blocked.  The payment is

```lean
theorem wgW_chase (hun : unclosed G Ψ' = unclosed G Ψ)
    (hA : A ∈ sfR G) (hC₀ : C₀ ∈ sfR G) (hAV : (A, C₀) ∉ V) :
    WgLtW (wgW G r' Ψ' C' ((A, C₀) :: V)) (wgW G r Ψ C V)   (search:269–273)
```

Pairs rather than antecedents: `vRem` counts the complement of `V` in
`Sf^R(G) × Sf^R(G)`, so re-chasing the same antecedent `A` under a
*different* goal still strictly drops the count.  Only the exact
`(A, ◯Z)` revisit is blocked.  With antecedents alone the searcher would
be forbidden from re-entering `A` under a new goal, and — this is the
part the architecture note (§4) records as analysis rather than as a
theorem — a `V`-membership at a cell certifies that the search sits
inside the still-pending chase of that very pair, since resolved chases
pop off with their `limpLI`.  **The explainer should mark that last
sentence as analysis, not as a mechanised claim**; nothing in the file
proves it, and nothing needs it — the measure argument is complete
without it.

---

### A.2 `totalityW` — structural induction on the goal formula

**File**: `wip/gbu_frjw_search.lean:318–361`.  A `private def`, so again
term-producing.

**Recursion principle**: structural on `X : Form` (the equation
compiler's own recursion; the recursive calls at 335–336, 341–342, 352,
359 are all at immediate subformulas).

**Motive, literally**:

```lean
private def totalityW (hsat : WSaturated G D)
    (decI : ∀ Ω C, Decidable (WEvalI D Ω C))
    {Ψ : List Form} {Z : Form} {R₀ : List Form}
    (hg : ∀ X ∈ Ψ, X ∈ gHat G)
    (hR₀mem : ∀ X, X ∈ sfR G → WEvalI D Ψ X → X ∈ R₀)
    (reccall : ∀ A' B', Form.imp A' B' ∈ sfR G → ¬ Clo Ψ A' →
      ¬ WEvalR D (A' :: Ψ) B' → GbuRC G (A' :: Ψ) B') :
    ∀ X, X ∈ sfR G → RefAt true (Z :: R₀) Ψ X ⊕' GbuIC G Ψ X
```

so the motive is `fun X => X ∈ sfR G → RefAt true (Z :: R₀) Ψ X ⊕'
GbuIC G Ψ X`: for every right-subformula, a refutation certificate over
the context `Ψ` with `Υ = Z :: R₀`, **or** a `Gbu◯` irregular
derivation.  `R₀` is instantiated by the caller as the decidable list of
*all* refuted `Sf^R`-forms (search:504–505).

**What a step consumes and produces.**  Per constructor of `Form`:

- `.bot` → `.inl .bot`; no recursion.
- `.atom a` → two decidable tests: is `a` refuted (`decI`), is `a ∈ Ψ`.
  The `absurd` at search:333 is the *dilemma* that closed the corner: an
  atom absent from the context is refuted by the `axI` row
  (`evalI_axI_gHat`), an atom present is derivable by `ax`.
- `.and`, `.or` → both children recursed; the results are combined by
  the De Morgan pairing (`∧`: one refuted side vs both derivable sides;
  `∨`: both refuted vs one derivable), search:334–345.
- `.imp A' B'` → refuted-as-a-form (`.ups`), else split on `Clo Ψ A'`:
  if closed, recurse on `B'`; if not, call `reccall`, which is the
  *non-structural* step (search:355–357).
- `.circ V` → recurse on the body; `.circ rfl r` or `.rcircI d hX`.

**The one non-structural step.**  `reccall` is supplied by the caller
as a closure over `IHW` (search:533–543), and it is paid for by measure
component 1, not by structure: `wgW_drop (unclosed_lt (sfR_imp hXsf).1 hncl)`.
So `totalityW` is structurally recursive *given a callback whose
termination is the enclosing well-founded recursion's business*.  This
two-level arrangement is the single most important architectural point
in the whole chain and deserves its own diagram in the explainer.

---

### A.3 `tCr` / `tCi` — mutual structural induction on FRJW derivations

**File**: `wip/gbu_frjw_closure.lean:1453–1678` (a `mutual` block).

**Recursion principle**: structural, on the FRJW derivation term,
mutually (a regular derivation's premises can be irregular and vice
versa).  These are `theorem`s: the conclusion is a `Prop` (`∃ r ∈ db, …`),
so no data escapes.

**Motives, literally**:

```lean
theorem tCr (hcl : DBClosed G db) :
    ∀ {t : Tag} {Γ : List Form} {C : Form},
      FRJWr G t Γ C → ∃ r ∈ db, WSubsumes (.reg t Γ C) r.s   (closure:1455–1457)

theorem tCi (hcl : DBClosed G db) :
    ∀ {St Th : List Form} {C : Form},
      FRJWi G St Th C → ∃ r ∈ db, WSubsumes (.irr St Th C) r.s (closure:1606–1608)
```

Together they give `tC_of_closed` (closure:1682–1685), which is exactly
`WSaturated.2` for the membership predicate of a `DBClosed` database.

**Case count**: `tCr` has 13 cases (axR, andR1, andR2, impIn, circIn,
joinAt, joinAtP, joinAtF, joinOr, joinOrP, joinOrF, joinCirc,
joinCircP); `tCi` has 8 (axI, andI1, andI2, orI, impInI, lift,
circNotIn, axIC).  21 in all — matching the 21 fields of `DBClosed`
(closure:1180–1339) one for one.

**What one step consumes and produces.**  Uniformly, three moves:

1. *Recurse* on each premise, getting a stored subsumer as a `Prop`-level
   existential.
2. *Extract the shape*: `reg_shape` / `irr_shape`
   (closure:1359–1376) turn `WSubsumes (.reg t Γ C) s` into
   `s = .reg (tagOf s) (ctxOf s) C ∧ tagLeB t (tagOf s) ∧ Γ ⊆ ctxOf s`.
   For the join rules, where the premises form a *family* indexed by
   `Fin (n+1)`, the per-premise existentials are turned into functions
   without choice by `irrPick` / `regPick` (closure:1394–1436), which
   skolemise through `List.find?` over the decidable subsumption test
   `subsumesB` (closure:1106–1147).
3. *Refire and close*: apply the matching `DBClosed` clause at the
   subsumers' shapes, transferring the rule's side conditions across the
   premise swap with the `_of_swap` lemmas (`hJ1_of_swap`,
   `hJ2_strict_of_swap`, `hJ5_of_swap`, `hJ7s_of_swap`,
   closure:181–201, 747–768), then compose with `wSubsumes_trans`.

The **T-B monotonicity** direction — "the rule applied to stored
subsumers of its premises yields a conclusion subsuming the original's" —
is what makes step 3 sound, and its nine standalone statements
(`joinCirc_mono` etc.) are archived-in-place with no code consumer
(closure:42–50, docs/frjw-compaction.md:32–46).  The *live* content is
the transfer lemmas plus the context-inclusion lemmas
(`joinOr_ctx_sub`, `joinAt_ctx_sub`, `joinCtx*_mono`) and
`subset_of_ctxEq_left`, used 8 times to close a join case.

---

### A.4 `sat` — fuel recursion, terminated by a pigeonhole

**File**: `wip/gbu_frjw_saturate.lean:1301–1390`.

**Recursion principle**: structural on a `Nat` fuel argument.  `sat` is
*not* well-founded recursion; the mathematical termination argument is a
separate theorem saying the supplied fuel suffices.

```lean
def sat (G : Form) : Nat → List (WRow G) → List (WRow G)
  | 0, db => db
  | fuel + 1, db =>
      let new := stepNew G db
      if new.isEmpty then db else sat G fuel (insertNew G new db)   (saturate:1304–1308)

def closureDB (G : Form) : List (WRow G) :=
  sat G ((univList G).length + 1) []                                (saturate:1364–1365)
```

**What one round consumes and produces.**  `stepAll G db`
(saturate:1206–1213) fires all 19 emitters at every stored premise
combination — families range over `(irrTs db).sublists` /
`(regTs db).sublists`, parameters over `goalPool G` and
`(gAt G).sublists` — each emission guarded by a `dite` on the rule's own
decidable hypotheses, so every emitted `WRow` carries its derivation by
the corresponding FRJW constructor.  `stepNew` filters to rows whose
*canonical key* is new; `insertNew` prepends them.

**The pigeonhole.**  Four lemmas:

```lean
insertNew_length_lt : (∃ r ∈ new, keyOf G r ∉ keysOf G db) →
    db.length < (insertNew G new db).length                    (saturate:1266–1269)
insertNew_nodup    : (keysOf G db).Nodup →
    (keysOf G (insertNew G new db)).Nodup                      (saturate:1286–1288)
keys_sub_univ      : ∀ k ∈ keysOf G db, k ∈ univList G         (saturate:1324–1325)
sat_fixed          : (keysOf G db).Nodup →
    (univList G).length + 1 ≤ db.length + fuel →
    (stepNew G (sat G fuel db)).isEmpty = true                 (saturate:1331–1334)
```

`sat_fixed` is by induction on `fuel`: at `fuel = 0` the store's
key-list is nodup and inside `univList G`, so `db.length ≤
(univList G).length`, contradicting the arithmetic hypothesis; at
`fuel+1` a non-empty round produces a fresh key, `db.length` strictly
grows, and the hypothesis is re-established.  The finiteness of
`univList G` (saturate:114–120) rests on the wellformedness theorems
`wfR`/`wfI` (banked earlier) plus `goalWr`/`goalWi`/`tagWr`
(closure:879–934): every derivable row has `Ĝ`-bounded zones, an
`Sf^R`-goal, and an `Sf^R`-pledged tag.

**Canonical keying** is what makes the pigeonhole finite despite rows
being stored in former-shaped (non-canonical) contexts:
`canonSeq G` filters each zone through the deduplicated pool
(saturate:109–111), `canonCtx_congr` (saturate:67) says `≐`-equal
contexts have *equal* canonical lists, and `subsumes_of_canonSeq_eq`
(saturate:159–161) converts equal keys back into mutual subsumption.
The bridge to the clauses is

```lean
theorem stored_of_emitted (h : r ∈ stepAll G (closureDB G)) :
    ∃ e ∈ closureDB G, WSubsumes r.s e.s                       (saturate:1385–1387)
```

used 26 times, once per coverage lemma (21 clauses; five of them use it
twice through a `by_cases`).

A note for the explainer: `dedupF` (saturate:76–78) is a hand-rolled
deduplication, present because mathlib's `List.mem_dedup` drags in
`Classical.choice` (saturate:74–75).  Three such choice leaks were
driven out at this stage (architecture note §12); the point is worth
making, because a decidability theorem that secretly used choice would
be worthless — *decidability is never assumed*.

---

### A.5 The T-A chain argument — `keptChain_sub_keptOf_of_le`

**File**: `wip/gbu_frjw_closure.lean:67–89`.

**Recursion principle**: induction on the inductive family
`KeptChain Υ base pool kept` (FRJ/RefAt.lean:144–150), whose `cons` case
carries a `RefAt true Υ (base ++ rest) Y` certificate over the base plus
*the earlier links only*.

```lean
theorem keptChain_sub_keptOf_of_le
    (hu : Υ ⊆ Υ') (hb : base ⊆ base') (hp : pool ⊆ pool')
    (h : KeptChain Υ base pool kept) :
    ∀ Y ∈ kept, Y ∈ keptOf Υ' base' pool'                     (closure:67–71)
```

**What one step consumes and produces.**  At `cons Y B rest`: the IH
places `rest` inside `keptOf Υ' base' pool'`; then
`refAt_mono hu (…)` lifts the link's certificate from `base ++ rest` to
`base' ++ keptOf …`, and `keptOf_saturated` (FRJ/RefAt.lean:374) absorbs
the link into the greedy fixpoint.  The parameter-growth form (`hu`,
`hb`, `hp`) is what absorbs zone growth under premise swap — it is the
reason a *single* lemma serves both T-A and the join monotonicity cases.

The order-sensitivity worry — a link's certificate may cite `Clo Ψ`-facts
routed through *other* stuck implications — is dissolved elsewhere, by
`clo_sf_support` / `refutedCleanly_circ_certs`
(corner:331, 470): a certificate's `Clo`-leaves are subformulas of its
target, hence strictly smaller, so a level-by-level construction on link
size always finds every leaf in place.  The explainer should present
T-A and that size argument together; separately they look like magic.

---

### A.6 The minor recursions (one table, for completeness)

| definition | file:line | principle | why it exists |
|---|---|---|---|
| `findNotT` | search:34–44 | structural on the list | constructive `findNot`: a total scan returning `(∀ a ∈ l, P a) ⊕' (Σ' a, a ∈ l ∧ ¬ P a)`; 11 call sites in `searchW` |
| `splitOfMem` | search:47–55 | structural on the list | constructive split at a member, `Σ' s t, l = s ++ a :: t`; 6 call sites |
| `findCMT` | search:197–208 | via `findNotT` over `(gAt G).sublists` | the classical countermodel scan for the `Ax^I◯` manufacture; `Decidable.of_not_not` is what keeps it choice-free |
| `dedupF` | saturate:76–78 | structural | choice-free deduplication |
| `decForallFin` / `decExistsFin` | saturate:688–711 | structural on `n` | `∀`/`∃` over `Fin` without `finRange` and without mathlib's `Fin` order instances (the recurring `Classical.choice` trap) |
| `growChain` / `keptOf` | RefAt.lean:~250–256 | fuel = pool length | the greedy kept chain |
| `classForce_congr` | saturate:1688–1700 | structural on `Form` | `classForce` sees only atom membership |

### A.7 The chain, end to end

```
  wgLtW_wf.fix ──> searchW ──> dichotomyW        (cell level, Type-valued)
        ↑              │
    totalityW ─────────┘        (structural on Form, with one callback)

  KeptChain-induction ──> T-A ──┐
  derivation-induction ──> tCr/tCi ──> tC_of_closed ──> decideGbuW_of_dbClosed
                                                              ↑
  fuel-recursion + pigeonhole ──> closureDB ──> closureDB_closed

  decideGbuW G : ProvableGbuC G ⊕' DisprovableW G      (saturate:2387–2388)
     └─> frjw_complete, gbuw_complete, provableGbuC_iff_pll,
         disprovableW_iff_not_pll, decidePLL          (saturate:2402–2431)
```

---

## PART B — State previews at each main stage

### B.0 What "state" should mean here

Two different things are worth previewing, and the explainer should not
conflate them:

- **The proof state**: the Lean goal plus the named hypotheses in scope
  at a chosen point of `searchW`'s tactic block.  This is what makes the
  proof enterable — it is the thing that has been asked for before, and
  it is what a reviewer needs to check a branch without reading the
  whole file.
- **The search state**: the cell `(reg?, Ψ, C)`, the visited list `V`,
  and the measure value `wgW G reg Ψ C V`, at each step of a concrete
  run.  This is what makes the *algorithm* legible, and it is
  independently checkable by `#eval`.

I recommend producing both, with the search-state trace first: it is
cheap, mechanically checkable, and it gives the vocabulary for reading
the proof states.

### B.1 The stage map — where to cut, and what is in scope

All references `wip/gbu_frjw_search.lean` @ `637dfcd`.

| stage | lines | new hypotheses at that point (as named in the code) |
|---|---|---|
| **S0** fixpoint set-up | 368–388 | `hsat`, `decI`, `decRP`; then `x`, `ihW`; `reg`, `Ψ`, `C`, `V`, `hVsf`, `hregV`, `hx`; `IHW`, `IH` |
| **S1** mode split | 389 | `cases reg` |
| **S2** irregular preamble | 390–399 | `hΨ`, `hΩc`, `hC`, `hnb`, `hne`, `hax` |
| **S3** irregular `∧`/`∨`/`⊃` | 400–455 | per case: `h₁`,`h₂` / `hg` / `he₁`,`he₂` / `hA`,`hB`,`hcl` |
| **S4** `◯`-goal dispatcher | 456–463 | `hZsf`; then `hg` (all of `Ψ` in `Ĝ`) or `⟨X,hXΨ,hXn⟩`; then `hnoc` or `⟨Y,hYΨ,hYc⟩` |
| **S5** the CRITICAL modal cell | 464–474 | `hΩai`, `upsToImp` |
| **S5a** `Z` refuted → row manufacture | 475–681 | `heZ`; `hnocm` (476–478); `QD` (479–485); `hallQ`/`⟨Y,hY,hnQ⟩` (486) |
| **S5a-i** all antecedents refuted → `Lift` | 488–493 | `hallI` |
| **S5a-ii** kept-chain manufacture | 494–518 | `hstuck`, `hnrp`, `R₀`, `hR₀def`, `hR₀ok`, `hallK` |
| **S5a-iii** **THE CORNER** (`totalityW`) | 519–581 | `⟨Y₂,hY₂,hnK⟩`, `hY₂i`, `hY₂Ψ`, `hA₂sf`, `hB₂sf`, `hRef`/`hDer`, `l₂`,`r₂`,`hsplit₂`, `hΓ₂`, `hclB₂`, `hmemsub₂`, `d₂` |
| **S5a-iv** the `L⊃ᵢ` chase | 582–682 | `hnA`, `hYi`, `hYΨ`, `lY`,`rY`,`hYsplit`, `hAsf`,`hBsf`, `hΓ`, `hmemsub`, `hclA`, `hsfC`, `hgC`, `hub`, `finish`; then `hfree` (640) / `hlt` (647) / `hAnotV` (662) |
| **S5b** `Z` unrefuted → `R◯ᵢ` | 683–689 | `heZ` (negative), `d` |
| **S6** modal member → `L◯ᵢ` | 690–724 | `hYc'`, `lY`,`rY`,`hYsplit`, `hΓ`, `hmemsub`, `hY'sf`, `hcov`, `d` |
| **S7** non-`Ĝ` member → `⊥`/`∧`/`∨` left | 725–805 | `lX`,`rX`,`hXsplit`, `hΓ`, `hmemsub`; per case `hA`,`hB`,`hcov`/`hcovL`,`hcovR`,`hszo` |
| **S8** REGULAR preamble | 806–816 | `hΨ`, `hC`, `hne`, `hV0`, `hax`; `hall`/`⟨l,r,X,hsplit,hX⟩`; `hΩ` |
| **S8a** regular critical helpers | 817–875 | `limpStep`, `fromImp`, `upsToImp` |
| **S8b** regular goal cases | 876–986 | atom/bot 877–886, `∧` 887–899, `⊃` 900–917, `∨` 918–935, `◯` 936–986 |
| **S9** non-critical invertible left rule | 987–1054 | `hXmem`, `hΓ`, `hmemsub` |
| **S10** the base call | 1055–1056 | `main _ p [] … rfl` |

The **release to regular mode** the brief asks about is S5a-iv's
`reccall`-free counterpart in two places: the irregular `R⊃ₙᵢ`
(search:445–455, `IHW (true, A :: Ψ, B) []` — note the `V := []` reset,
justified by `hregV`), and `totalityW`'s callback (search:533–543).
Both pay by `unclosed`, both reset `V`.  The **regular → irregular**
release is `wgFocus` at search:827, 927, 932, 952.

### B.2 Mechanism 1 (recommended): the `#eval`-checked cell/measure trace

Write a scratch file `wip/frjw_trace.lean` (a *new* file; nothing
existing is touched) that

1. fixes the example formula `G` and the cells of the trace as literal
   `Bool × List Form × Form × List (Form × Form)` data;
2. `#eval`s, for each cell, the tuple
   `(unclosed G Ψ, vRem G V, tpC reg C, seqSize Ψ C)` — i.e. exactly
   `wgW G reg Ψ C V`, all four components computable;
3. `#eval`s the guards the searcher actually branches on, so the trace
   says *why* each branch fires: `cloB Ψ A`, `isHat X`, `impPart Ψ`,
   `X.hasCirc`, `Form.size`, membership in `sfL G` / `sfR G` / `gHat G`;
4. `#guard`s the strict-decrease claim `WgLtW (wgW …) (wgW …)` between
   consecutive cells by evaluating the two tuples and comparing
   lexicographically.

The database-dependent tests (`decI`, `decRP`) cannot be evaluated
without the concrete `closureDB G`, which is only feasible for the very
smallest formulas (see B.4).  So the trace table should have a column
"database verdict" whose entries are *assumed* and labelled as such, with
the semantic justification given in prose (a `◯`-free goal not derivable
from the context is refuted; a context atom is not).  This is the honest
form: everything arithmetic is machine-checked, everything
database-level is stated as an assumption of the walkthrough.

Deliverable: one markdown table per cell, of the form

    step  rule fired   cell (reg?, Ψ, C)                 V        wgW            drops
    0     —            (true,  [],            G)         []       (u₀,p₀,2,s₀)   —
    1     R⊃ₙ          (true,  [p⊃◯q],        ◯p⊃◯q)     []       (u₁,…)         #1
    …

with the `wgW` column produced by `#eval` and pasted verbatim.

### B.3 Mechanism 2: `trace_state` in a shadow copy

`searchW`'s body is a tactic block, so proof states are directly
printable.  Method: copy `wip/gbu_frjw_search.lean` to
`wip/gbu_frjw_search_traced.lean` (a new file — the original is not
modified), insert `trace_state` at the ten stage boundaries of B.1, and
build that file alone.  Notes and caveats:

- `set_option maxHeartbeats 3200000 in` (search:365) is already needed
  for the untraced file; the traced copy will be slower still.  Budget a
  single build, not an edit-rebuild loop.
- `trace_state` output at S5a-iii is large (roughly 40 hypotheses).  The
  useful artefact is a *curated* transcript: the goal, plus the
  hypotheses named in B.1 for that stage, with the rest elided and the
  elision marked.
- An alternative with less output: `set_option pp.maxSteps`/`pp.deepTerms
  false` plus `show` statements asserting the expected goal at each
  stage.  A `show` that elaborates is itself a check that the stage
  description is right, and it survives in the file as documentation.
  **I recommend the `show`-assertion variant over raw `trace_state`**:
  it produces the same information, is self-checking, and does not
  depend on transcribing tool output.
- **UNCERTAIN**: I have not built the traced copy, so I cannot promise
  the `show` forms elaborate without `change`/`conv` massaging at every
  stage.  Budget accordingly (see the menu).

### B.4 Mechanism 3: end-to-end `#eval` of `decidePLL` — what already exists

This is already built and its limits are already known.
`wip/decidepll_smoke.lean` (added at `b2f338d`) runs
`@decide (PLL G) (decidePLL G)` on five cells, one per invocation:

    lake env lean --run wip/decidepll_smoke.lean impid

and `wip/decidepll_smoke_out.txt` records 5/5 PASS — `atom`, `bot`,
`circbot` false; `p ⊃ p` and `p ⊃ ◯p` true — with the gate watched
failing and restored.  This is `#eval`-level evidence only; it taints
nothing (the `#guard_msgs` pins are the kernel gates), and a timeout is
a FLAG, never a verdict.

For the explainer this is worth one paragraph and no more: it shows the
whole chain computes at the bottom of the scale, and it is **not** a
tracing mechanism, because `closureDB G` saturates the entire wellformed
universe of `G` before any cell is searched.  Anything with two
connectives and a modality is out of interpreter reach.
**UNCERTAIN**: I have not measured where the wall is; the five passing
cells have `|sfR G| ≤ 3`.

### B.5 The worked example

**Primary: `G₁ = (p ⊃ ◯q) ⊃ (◯p ⊃ ◯q)`.**  PLL-valid (it is the strength
law of the lax modality), so `¬ WEvalR D [] G₁` holds by soundness and
`searchW` genuinely runs and returns a derivation.  Traced stages:

- S8 regular preamble at the root cell `(true, [], G₁)`;
- S8b `⊃` case, `¬ Clo [] (p ⊃ ◯q)` → `R⊃ₙ`, `rimpNI` (search:909):
  **component 1 drops**;
- S8b `⊃` again at `(true, [p⊃◯q], ◯p ⊃ ◯q)` → `R⊃ₙ` again:
  **component 1 drops again**;
- S8b `◯` case at `(true, [◯p, p⊃◯q], ◯q)`: the `findNotT` for
  `isCirc = false` finds `◯p`, so the `L◯` branch (search:957–986) fires:
  **component 4 drops**;
- S8b `◯` case at `(true, [p, p⊃◯q], ◯q)`, now with no modal member: the
  critical branch (search:940–956).  `decI Ψ q` says `q` is refuted, so
  the scan over `impPart Ψ = [p⊃◯q]` runs; `p ∈ Ψ` so `p` is *not*
  refuted, and `fromImp` → `limpStep` fires (search:817–864);
- `limpStep`'s `d₁ = IH (false, p⊃◯q :: rest, p)` — the **release to
  irregular mode**, `wgFocus`: **component 3 drops** (2 → 0);
- the irregular cell closes at S2 by `ax` (`p ∈ Ψ`);
- `limpStep`'s `d₂ = IH (true, ◯q :: rest, ◯q)` closes by `ax`.

That covers S0, S2, S8, S8a, S8b (`⊃`, `◯`, both sub-branches), S9's
sibling `L◯`, and three of the four measure components.

**It does not reach the corner or the chase**, which live in *irregular*
mode with a `◯` goal and a stuck modal antecedent.  I recommend
presenting those from a **cell**, not from a root formula: `WSearchOk` is
a per-cell statement, so exhibiting

    (false, Ψ = [◯p ⊃ ◯r, s], C = ◯r, V = [])

and walking S4 → S5 → S5a → S5a-iv (the chase, since `(◯p).hasCirc =
true` and `¬ (◯p).size < (◯r).size`) → the `V = [(◯p, ◯r)]` re-entry, is
legitimate and far clearer than manufacturing a root formula that
reaches it.  **UNCERTAIN**: I have not verified that this particular
cell is reachable from any root formula, nor that its `decI` verdicts
come out as the walkthrough needs; both should be checked before the
explainer is written, and the cell adjusted if not.  The corner (S5a-iii)
should be presented the same way, from a cell whose stuck antecedent
fails the `RefAt` test.

**On the formulas the brief suggested.**  `◯p ⊃ p` and `◯(◯p ⊃ p)` are
both PLL-*invalid*, so `dichotomyW` (search:1068–1080) decides
`WEvalR D [] G` positively and takes the `.inl` branch: `searchW` is
never entered.  They are the right examples for the *disproof* side —
"the database already has the row" — and the wrong examples for tracing
the search.  Worth one explicit sentence in the explainer, because the
asymmetry is easy to miss.

### B.6 Recommendation and effort

Recommended package: **B.2 (the `#eval`-checked trace) + B.3 in its
`show`-assertion variant, on the primary example `G₁` plus two
free-standing cells for the corner and the chase.**

| item | effort |
|---|---|
| B.2 trace file + table for `G₁` | 2–3 h |
| B.2 extended to the two free-standing cells (incl. checking they behave as claimed) | 2 h |
| B.3 `show`-assertions at the ten stage boundaries, one build | 3–4 h, plus one long build |
| B.3 raw `trace_state` transcripts instead | 2 h + a long build, but the artefact is worse |
| B.4 write-up of the existing smoke evidence | 20 min |

---

## PART C — Reusable tactics and combinators

Every candidate below is backed by at least two occurrences with line
numbers.  Savings are line counts, estimated by hand from the quoted
text; they are approximate and should be re-measured after each change.
The list is ranked at C.10.

### C.1 `byDecNeg` — the "decide, and the positive side is impossible" shape

`byDec` (search:21–25) already gives decide-then-branch, and is used 19
times.  What it does not give is the *dominant* use of it: a test whose
positive branch immediately contradicts the standing negative database
hypothesis.

Pattern, quoted:

```lean
· refine byDec (decI Ψ C₂) (fun he₂ => ?_) (fun he₂ => ?_)
  · exact absurd (gbuInv10 hsat hC he₁ he₂) hne                (search:420–421)
```
```lean
refine byDec (decI Ψ Z) (fun heZ => ?_) (fun heZ => ?_)
· rcases findNotT (fun Y => decI Ψ (ante Y)) (impPart Ψ) with
    hallI | ⟨Y, hY, hnY⟩
  · exact absurd (gbuSuccCirc hsat hΩai hC (upsToImp hallI) heZ) hne
                                                              (search:946–949)
```

Further occurrences of the `exact absurd (…) hne` closer: search:398,
399, 478, 500, 880, 885, 924.  Proposed:

```lean
private def byDecNeg {p r : Prop} (d : Decidable p) {q : Sort _}
    (hnr : ¬ r) (h1 : p → r) (h2 : ¬ p → q) : q :=
  byDec d (fun hp => absurd (h1 hp) hnr) h2
```

Saving: ~9 lines, and — the larger gain — every such branch then *reads*
as "impossible: the database would have had a row", which is the
mathematical content.

### C.2 `IHi` / `IHr` — retire the `hregV` payload

Every one of the 30 `IH`/`IHW` call sites carries a one-line proof of
the `V`-mode side condition `p.1 = true → V = []`, always one of exactly
three terms:

```lean
              (fun h => Bool.noConfusion h)          -- irregular target: 19 sites
                                       (search:406, 412, 425, 431, 441, 572, 628,
                                        645, 658, 680, 687, 716, 756, 787, 797,
                                        828, 928, 933, 953)
```
```lean
                         (fun _ => hV0)              -- regular target: 9 sites
                                       (search:857, 892, 897, 906, 910, 979,
                                        1011, 1034, 1047)
```
```lean
                    (fun _ => rfl)                   -- the two `V := []` resets
                                       (search:447, 535)
```

A *separate* payload of the same shape discharges the `hΩc` clause
`C.isCirc = false → ∀ X ∈ Ω, X ∈ gHat G` of `WSearchOk` at a `◯`-shaped
goal — six sites, distinguishable in the file by the trailing `hC`
(search:578, 634, 722, 764, 793, 803).  Those are eliminable too, by a
companion introduction helper for the irregular clause at a `circ` goal;
count them separately when measuring.

Proposed: split `IH` at the point of definition into two specialised
forms whose targets have a known first component, so the side condition
is discharged once:

```lean
have IHi : ∀ (Ω : List Form) (C' : Form),
    WgLt (wgC G false Ω C') (wgC G reg Ψ C) → WSearchOk G D (false, Ω, C') :=
  fun Ω C' h => IH (false, Ω, C') h (fun e => Bool.noConfusion e)
have IHr : ∀ (Ω : List Form) (C' : Form),
    WgLt (wgC G true Ω C') (wgC G reg Ψ C) → WSearchOk G D (true, Ω, C') :=
  fun Ω C' h => IH (true, Ω, C') h (fun _ => hV0)   -- regular branch only
```

Saving: ~28 lines from the `hregV` payloads (plus ~6 more if the `hΩc`
helper is added), plus the tuple noise `(false, Ψ, C₁)` → `Ψ C₁` at 30
sites.  Caveat: `hV0 : V = []` is introduced at search:810, *inside* the
regular branch, so `IHr` must be defined there and `IHi` twice (once per
mode branch), or both `have`s placed after the `cases reg`.  That is a
five-minute rearrangement, not an obstacle.

### C.3 `focusCtx`, `clo_focus`, `sfL_cons` — the principal-formula step

The most repeated block in `searchW` is: split the context at the
principal formula, build the `≐`, derive the three consequences
(membership, `Clo`-coverage, `Sf^L`-preservation), and do the `seqSize`
arithmetic.

Quoted, twice (of nine occurrences — search:547–559, 589–606, 697–707,
726–730, 820–825, 963–967, plus the `∧`/`∨` variants at 739–746,
767–784, 998–1006, 1021–1046):

```lean
obtain ⟨lY, rY, hYsplit⟩ := splitOfMem hYΨ
have hΓ : Ψ ≐ .circ Y' :: (lY ++ rY) := by
  rw [hYsplit]; exact ctxEq_split
have hmemsub : ∀ V ∈ lY ++ rY, V ∈ Ψ :=
  fun V hV => (hΓ V).mpr (List.mem_cons_of_mem _ hV)          (search:697–701)
```
```lean
obtain ⟨lY, rY, hYsplit⟩ := splitOfMem hYΨ
have hΓ : Ψ ≐ .imp A B :: (lY ++ rY) := by
  rw [hYsplit]; exact ctxEq_split
have hmemsub : ∀ W ∈ lY ++ rY, W ∈ Ψ :=
  fun W hW => (hΓ W).mpr (List.mem_cons_of_mem _ hW)          (search:820–825)
```

and the arithmetic, six times identically (search:624, 655, 713, 773,
853, 976):

```lean
rw [hYsplit, seqSize_split, seqSize_cons]
```

Proposed, one structure packaging the split with its four consequences:

```lean
private structure Focus (Ψ : List Form) (X : Form) where
  rest   : List Form
  ctxEq  : Ψ ≐ X :: rest
  memsub : ∀ W ∈ rest, W ∈ Ψ
  size   : ∀ C, seqSize Ψ C = seqSize rest C + X.size

private def focusCtx {Ψ : List Form} {X : Form} (hX : X ∈ Ψ) : Focus Ψ X
```

with two companions:

```lean
private theorem clo_focus {Ψ rest : List Form} {X Y : Form}
    (hΓ : Ψ ≐ X :: rest) (hX : Clo (Y :: rest) X) :
    ∀ W ∈ Ψ, Clo (Y :: rest) W

private theorem sfL_cons {G : Form} {rest : List Form} {X : Form}
    (hX : X ∈ sfL G) (h : ∀ W ∈ rest, W ∈ sfL G) :
    ∀ W ∈ X :: rest, W ∈ sfL G
```

`clo_focus` collapses eleven four-line blocks (search:550–556, 614–618,
703–707, 741–746, 775–779, 780–784, 848–851, 971–974, 1002–1006,
1029–1032, 1042–1045) to one-liners such as
`clo_focus hΓ (.imp (.base List.mem_cons_self))`.  `sfL_cons` collapses
roughly twelve `intro W hW; rcases List.mem_cons.mp hW with rfl | hW'`
blocks (there are 37 `rcases List.mem_cons.mp` occurrences in the file;
not all are of this shape).

Saving: ~40 (`focusCtx` + the six `seqSize` blocks) + ~44 (`clo_focus`)
+ ~30 (`sfL_cons`) ≈ **110 lines**, the single largest item in this
survey, and the one that most improves legibility: each rule step
becomes "focus, cover, descend, apply the constructor".

### C.4 `wgGoal` — the pure goal-descent measure step

Nine of the twenty `wgKeep` sites are the same two-line incantation
(search:404, 410, 423, 429, 439, 685, 890, 895, 904):

```lean
(wgKeep (fun _ h => .base h) (seqSize_goal
  (Nat.lt_succ_of_le (Nat.le_add_right _ _))))
```

Proposed:

```lean
private theorem wgGoal {G : Form} {r : Bool} {Ψ : List Form} {C C' : Form}
    (h : C'.size < C.size)
    (htp : tpC r C' ≤ tpC r C := by first | exact Nat.le_refl _ | …) :
    WgLt (wgC G r Ψ C') (wgC G r Ψ C) :=
  wgKeep (fun _ h => .base h) (seqSize_goal h) htp
```

Saving: ~18 lines.  Low risk; the auto-param already exists on `wgKeep`.

### C.5 `wfFixMeasure` — the measure-fixpoint wrapper

The `∀ x, … → wgW … = x → …` device plus the `hx ▸` transport
(search:372–388) is boilerplate for "well-founded recursion on a
measure, with side conditions on an auxiliary parameter".  It is already
instantiated **twice** in the repository — here and in `searchO`
(`wip/gbu_search_circ.lean`, the retired `◯`-free predecessor) — so
extracting it is not speculative.

```lean
def wfFixMeasure {α : Sort u} {β : Sort v} {ρ : β → β → Prop}
    (hwf : WellFounded ρ) (m : α → β) {C : α → Sort w}
    (step : ∀ a, (∀ a', ρ (m a') (m a) → C a') → C a) : ∀ a, C a
```

Saving here: ~12 lines.  The case for it is reuse, not size: it is the
piece a *third* calculus would want first.

### C.6 `regUp` / `irrUp` and the closers — the T-C unary shape

Quoted twice (of eleven unary cases in `tCr`/`tCi`):

```lean
| _, _, _, .impIn (A := A) (B := B) d hA hg => by
    obtain ⟨r, hr, hsub⟩ := tCr hcl d
    obtain ⟨hshape, hle, hΓ⟩ := reg_shape hsub
    obtain ⟨r₂, hr₂, hsub₂⟩ := hcl.impIn (tagOf r.s) (ctxOf r.s) A B
      (by rw [← hshape]; exact List.mem_map.mpr ⟨r, hr, rfl⟩)
      (clo_mono hΓ hA) hg
    exact ⟨r₂, hr₂, wSubsumes_trans (wSubsumes_reg hle hΓ) hsub₂⟩   (closure:1473–1479)
```
```lean
| _, _, _, .andI1 (A₁ := A₁) (A₂ := A₂) d hg => by
    obtain ⟨r, hr, hsub⟩ := tCi hcl d
    obtain ⟨hshape, hst, hth⟩ := irr_shape hsub
    obtain ⟨r₂, hr₂, hsub₂⟩ := hcl.andI1 (stabOf r.s) (thOf r.s) A₁ A₂
      (by rw [← hshape]; exact List.mem_map.mpr ⟨r, hr, rfl⟩) hg
    exact ⟨r₂, hr₂, wSubsumes_trans (wSubsumes_irr hst.symm hth) hsub₂⟩ (closure:1612–1617)
```

The incantation `by rw [← hshape]; exact List.mem_map.mpr ⟨r, hr, rfl⟩`
appears 9 times.  Proposed:

```lean
private theorem regUp (h : ∃ r ∈ db, WSubsumes (.reg t Γ C) r.s) :
    ∃ t' Γ', (WSeq.reg t' Γ' C) ∈ db.map (·.s) ∧
             tagLeB t t' = true ∧ Γ ⊆ Γ'
private theorem irrUp (h : ∃ r ∈ db, WSubsumes (.irr St Th C) r.s) :
    ∃ St' Th', (WSeq.irr St' Th' C) ∈ db.map (·.s) ∧ St' ≐ St ∧ Th ⊆ Th'
private theorem downReg (hle : tagLeB t₁ t₂ = true) (hΓ : Γ₁ ⊆ Γ₂) :
    (∃ r ∈ db, WSubsumes (.reg t₂ Γ₂ C) r.s) →
    (∃ r ∈ db, WSubsumes (.reg t₁ Γ₁ C) r.s)
private theorem downIrr (hq : St₁ ≐ St₂) (hTh : Th₁ ⊆ Th₂) : …
```

Each unary case then reads

```lean
obtain ⟨t', Γ', hmem, hle, hΓ⟩ := regUp (tCr hcl d)
exact downReg hle hΓ (hcl.impIn t' Γ' A B hmem (clo_mono hΓ hA) hg)
```

Saving: ~3 lines × 11 sites ≈ **33 lines**, plus the disappearance of the
`r₂`/`hr₂` scaffolding.  For the nine join cases, `downReg` alone
absorbs the closer (`subset_of_ctxEq_left` appears 8 times inside it):
another ~16 lines.

### C.7 `stepAll` as a flatten — retire the nineteen `sub_stepAll_*`

`stepAll` is a 19-fold `++` (saturate:1206–1213), and membership in it is
proved by nineteen near-identical theorems (saturate:1423–1535, ~114
lines) whose payloads are nested `Or.inl` chains up to eighteen deep:

```lean
theorem sub_stepAll_AxR {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitAxR G, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inl hx)))))))))))))))))                          (saturate:1423–1427)
```
```lean
theorem sub_stepAll_JoinCircP {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitJoinCircP G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inr hx                                        (saturate:1531–1535)
```

Proposed: define the emitters as a list and `stepAll` as its flatten,

```lean
def emitters (G : Form) (db : List (WRow G)) : List (List (WRow G)) :=
  [emitAxR G, emitAxI G, emitAxIC G, emitAndR G db, …, emitJoinCircP G db]

def stepAll (G : Form) (db : List (WRow G)) : List (WRow G) :=
  (emitters G db).flatten

theorem sub_stepAll {G : Form} {db : List (WRow G)} {l : List (WRow G)}
    (hl : l ∈ emitters G db) : ∀ x ∈ l, x ∈ stepAll G db :=
  fun x hx => List.mem_flatten.mpr ⟨l, hl, hx⟩
```

with the 19 call sites in the coverage layer becoming
`sub_stepAll (by simp [emitters]) hemit` or 19 one-line abbreviations.
Saving: ~**95 lines**, and it removes the most brittle text in the file
(an `Or.inl` chain that must be recounted whenever an emitter is added).

### C.8 The coverage skeleton — a macro, with a caveat

26 sites share the shape

```lean
have hemit : (⟨.reg .barren (rm (gAt G) F) F,
    .axR F hF hg (CtxEq.refl _)⟩ : WRow G) ∈ emitAxR G := by
  refine List.mem_filterMap.mpr ⟨F, mem_goalPool.mpr hg, ?_⟩
  exact dif_pos ⟨hF, hg⟩
exact stored_of_emitted (sub_stepAll_AxR _ hemit)          (saturate:1671–1675)
```
```lean
have hemit : (⟨.reg tr.t tr.Γ (.and tr.C A₂),
    .andR1 tr.d hg⟩ : WRow G) ∈ emitAndR G (closureDB G) := by
  refine List.mem_flatMap.mpr ⟨tr, htr, ?_⟩
  refine List.mem_filterMap.mpr ⟨.and tr.C A₂, mem_goalPool.mpr hg, ?_⟩
  exact dif_pos ⟨rfl, hg⟩
exact stored_of_emitted (sub_stepAll_AndR _ hemit)         (saturate:1737–1743)
```

(`stored_of_emitted` 26×, `List.mem_filterMap.mpr` 26×,
`mem_goalPool.mpr` 26×, `dif_pos` 24×.)

A `macro "cover" …` taking the emitter lemma, the goal-pool witness and
the `dite` payload would save ~2 lines × 26 ≈ 50 lines.  **My honest
assessment is that this one is marginal**: the shapes differ in arity
(one, two or three `mem_flatMap` layers) and in whether a `by_cases`
precedes, and a macro that has to take all of that as parameters is not
obviously more readable than the explicit text.  Rank it below C.7,
which achieves a comparable saving with no loss of explicitness.

### C.9 The `_of_swap` / `SameIrr` congruence layer — verdict: leave it

`SameIrr` / `SameReg` (saturate:214–231) with their ~25 congruence
lemmas, and the four `_of_swap` transfers (closure:181–201, 747–768), are
already the factored form of "a join depends on its family only through
the row set".  The individual lemmas are one-liners over
`mem_unionAll` / `List.mem_filter`; there is no further common factor I
can see that is not just `simp`.  **Recommend: no change.**  The one
observation worth making in the explainer is structural rather than
compactive: `SameIrr` is exactly the statement that the join rules
factor through the *set* of premise rows, which is why arbitrary-arity
families can be reindexed to stored sublists at all (`reindex_irr`,
saturate:1540–1611).

### C.10 Could the MAIN induction be a reusable combinator?

The brief asks whether the `A ⊕' B`-shaped target invites a generic
"decide-or-recurse for dual calculi".  My assessment, stated plainly:

**What such a combinator would buy: the fixpoint plumbing only, i.e.
exactly C.5.**  The abstraction would need four parameters — the cell
type, the measure, the rule set of the proof calculus, and the query
interface of the refutation database — and the entire content of
`searchW` sits in the last two.  Concretely:

- The branch structure is not generic.  Every `byDec` in `searchW` is on
  a query whose meaning is FRJW-specific (`WEvalI`, `WEvalRP`, `Clo`,
  `∈ Ψ`), and each positive branch is closed by a *named inversion
  lemma* of the Gbu◯/FRJW pair (`gbuInv1`–`gbuInv14`, `gbuSuccAtF`,
  `gbuSuccOrF`, `gbuSuccCirc`, `gbuInvLift`, `refutedCleanly_circ*`).
  There is no calculus-independent statement of "the positive branch is
  impossible" — that IS the duality, proved rule by rule.
- The measure is not generic either: `unclosed` is defined from `Cl(Γ)`,
  which is a Gbu-specific closure operator, and `tpC`'s grading by
  `hasCirc` is a fact about *this* modality's `L⊃ᵢ` licence.
- The `⊕'` shape at the target is genuinely generic, but it is one
  line of type, not an argument.

So: **`byDec` already gives everything a generic decide-or-recurse
combinator would give at the branch level; `wfFixMeasure` (C.5) gives
everything it would give at the recursion level; and there is nothing in
between.**  I would not build the abstract combinator.  What I *would*
extract, if the intention is to make the technique reusable for a third
calculus, is not a combinator but a **checklist**: the four measure
components and what each pays for, the two-level arrangement of §A.2
(structural totality with a measure-paid callback), and the
canonical-key + pigeonhole saturation of §A.4.  Those transfer; the code
does not.

### C.11 Ranked summary

| # | item | est. saving | risk | note |
|---|---|---|---|---|
| C.3 | `focusCtx` / `clo_focus` / `sfL_cons` | ~110 | low | biggest legibility gain |
| C.7 | `stepAll` as flatten, one `sub_stepAll` | ~95 | low | also removes the brittlest text |
| C.6 | `regUp`/`irrUp` + `downReg`/`downIrr` | ~50 | low | 11 unary + 9 join closers |
| C.2 | `IHi` / `IHr` | ~28 (+6) | low | needs `hV0` placement care |
| C.8 | coverage macro | ~50 | medium | marginal; readability cost |
| C.4 | `wgGoal` | ~18 | low | |
| C.5 | `wfFixMeasure` | ~12 | low | value is reuse, not size |
| C.1 | `byDecNeg` | ~9 | low | value is legibility |
| C.9 | `SameIrr` layer | 0 | — | recommend no change |
| C.10 | generic dual-calculus combinator | 0 | — | recommend not building |

Total realistic saving from the low-risk items (C.1–C.7, C.8 excluded):
**≈ 320 lines**, on a 5,369-line core (search 1093 + closure 1805 +
saturate 2471),
with no change to the mathematics and every `#guard_msgs` pin expected to
be byte-identical.  The discipline used for stage 1 applies: strip, then
verify the pins unchanged and the smoke cell still PASS
(docs/frjw-compaction.md:16–20).

---

## PART D — The `⊕'` framing, explained

A short section for the explainer; here is its content in full, since it
is short enough to settle now rather than commission.

### D.1 Why not `⊕`

`Sum` (`⊕`) is `Type u → Type v → Type (max u v)`.  Both sides here are
`Prop`s:

    ProvableGbuC G  : Prop := Nonempty (GbuRC G [] G)      (gbu_circ.lean:1368)
    DisprovableW G  : Prop := ∃ t Γ, Nonempty (FRJWr G t Γ G)
                                                        (FRJ/CalculusW.lean:246)

so `ProvableGbuC G ⊕ DisprovableW G` does not typecheck.  `PSum` (`⊕'`)
is `Sort u → Sort v → Sort (max 1 u v)`: it accepts `Sort 0` arguments
and lands in `Type 0` when both are `Prop`.  This is the immediate,
mechanical reason — but it is not the interesting one.

### D.2 Why not `∨`

`ProvableGbuC G ∨ DisprovableW G` typechecks and is *provable*: it is
`provable_or_disprovable` (saturate:2394–2398), obtained from
`decideGbuW` by forgetting.  What it cannot do is be **eliminated into a
`Type`**.  `Or` is a `Prop`, and Lean's large-elimination restriction
forbids matching on a `Prop`-valued inductive to produce data (except
for subsingletons).  So from `A ∨ B` one cannot build
`Decidable (PLL G)` — which is `Sort 1` data, `isTrue h | isFalse h` —
without `Classical.choice`.

That is exactly what is at stake, and it is visible in the pin.  With
`⊕'`:

```lean
def decidePLL (G : Form) : Decidable (PLL G) :=
  match decideGbuW G with
  | .inl h => isTrue (FRJ.Gbu.pll_of_provableGbuC h)
  | .inr h => isFalse (FRJ.soundnessW h)               (saturate:2428–2431)

/-- info: 'FRJ.Gbu.W.decidePLL' depends on axioms: [propext, Quot.sound] -/
```

Had the chain been stated with `∨`, the same definition would have
required `Or.elim` into `Type`, i.e. choice, and the pin would read
`[propext, Classical.choice, Quot.sound]`.  A decidability result whose
witness is produced by choice decides nothing: the standing rule in this
development is that a `Decidable` hypothesis must not be discharged by
`Classical.choice` — decidability *follows from* completeness, it is
never assumed.

### D.3 What an inhabitant lets a program do

An inhabitant of `A ⊕' B` is a *tagged* value: `PSum.inl` or `PSum.inr`,
and the tag is data.  A program may branch on it in any context,
including one that returns a term.  Three uses in the chain:

1. `decidePLL` (above) — the tag becomes the `Decidable` verdict.
2. `dichotomyW` (search:1068–1080), whose type is

       DisprovableW G ⊕' GbuRC G [] G

   Note the right side: not `Nonempty (GbuRC G [] G)` but the derivation
   itself.  So one layer down, the positive side really does *carry the
   proof term*, and any consumer — a checker, a printer, a
   proof-transformation — can take it apart.
3. `totalityW` (search:325) returns `RefAt true (Z :: R₀) Ψ X ⊕' GbuIC G Ψ X`
   and the caller *matches on it* to decide whether to apply `L⊃ᵢ`
   (search:544–545).  With `∨` the corner could not be closed at all:
   the derivation on the right is what `.limpLI` is applied to.

**One asymmetry, worth stating plainly.**  At the crown, `decideGbuW G :
ProvableGbuC G ⊕' DisprovableW G` has `Nonempty` on the left and `∃` on
the right, so both sides are squashed and the `⊕'` carries exactly one
bit — which is all `Decidable` needs.  `decideGbuW_of` does the
squashing explicitly:

```lean
match dichotomyW … with
| .inl hdis => .inr hdis
| .inr d => .inl ⟨d⟩                                   (closure:1092–1097)
```

The `⟨d⟩` discards `d`.  If a certified *artefact* is ever wanted at the
crown — a printable Gbu◯ derivation, or an FRJW disproof to render as a
countermodel — the fix is a Type-valued restatement,

    DisprovableWT G := Σ' (t : Tag) (Γ : List Form), FRJWr G t Γ G

and a `decideGbuWT G : GbuRC G [] G ⊕' DisprovableWT G`, from which the
present `decideGbuW` follows by squashing.  Nothing in the proofs would
change; `dichotomyW` already returns the derivation on one side, and
`hsat.1` (`dichotomy:79`) yields only `Nonempty` on the other, so the
disproof side would need `WSaturated.1` strengthened to carry the row's
derivation — which `WRow` already does (closure:952–954).  **UNCERTAIN
whether this is a small change**: it touches the abstract-database
interface, which is deliberately `Prop`-valued.  Flag it as a design
question, not as work.

### D.4 Relation to `Decidable`

`Decidable p` is, up to the choice of constructor names, `p ⊕' ¬ p`.
The dichotomy replaces the negative side `¬ ProvableGbuC G` with a
*positive certificate of a different calculus*, `DisprovableW G`.  So

    decideGbuW G : ProvableGbuC G ⊕' DisprovableW G

is "`Decidable (ProvableGbuC G)` with a witness on the false side".  The
two halves that make this a decision procedure are proved separately:

- **Exhaustiveness** — no goal escapes both — is the constructive
  content of `decideGbuW` itself, i.e. FRJW completeness *and* Gbu◯
  completeness simultaneously (`frjw_complete`, `gbuw_complete`,
  saturate:2402–2411).  This is what the chain is for.
- **Exclusivity** — no goal satisfies both — is a *theorem*, not part of
  the `PSum`: `PSum` permits both sides to be inhabited.  It comes from
  the two soundness results,

      not_disprovableW_of_provableGbuC (h : ProvableGbuC G) : ¬ DisprovableW G
      not_provableGbuC_of_disprovableW (h : DisprovableW G) : ¬ ProvableGbuC G
                                            (gbu_frjw_exclusion.lean:26–33)

  each of which is one line: `fun hd => soundnessW hd (pll_of_provableGbuC h)`.
  One forces PLL-validity, the other refutes it.

Composing the two gives the semantic reading

    provableGbuC_iff_pll     : ProvableGbuC G ↔ PLL G           (saturate:2414)
    disprovableW_iff_not_pll : DisprovableW G ↔ ¬ PLL G         (saturate:2420)

so the decision object is *sound and complete in both directions
simultaneously*, and `decidePLL` reads it off.

### D.5 What is new here

Two things, stated conservatively:

1. **The pair, mechanised, for a modal logic.**  The duality between a
   backtrack-free proof calculus and a forward refutation calculus is
   due to Fiorentini and Ferrari, for intuitionistic propositional
   logic: *Duality between unprovability and provability in forward
   proof-search for Intuitionistic Propositional Logic*, ACM TOCL 21(3),
   2020 — the repository's source of truth for FRJ(G) and for `Gbu`
   (docs/frj-fidelity.md:3–6; docs/calculus-map.md records "`Gbu` is
   Fiorentini & Ferrari §5").  What is ours is the `◯`-extension on both
   sides, including the licenced `|◯C|` adaptation of `L⊃ᵢ` and every
   proof in the chain above.  I am confident of that citation and of no
   other; in particular I make **no** claim about what the S4 paper
   (JLC 31(3), 2021) contains — it is unread here, and repository policy
   is that nothing may be attributed to it.
2. **The single object.**  Packaging the two calculi into one
   `⊕'`-valued function, made exhaustive by construction and exclusive
   by the two soundness theorems, is what turns "two completeness
   theorems" into "one decision procedure" without leaving the
   constructive fragment.  The evidence that this is not merely
   cosmetic is the axiom pin: `[propext, Quot.sound]` throughout, no
   `Classical.choice`, on a result — decidability of PLL — that is
   normally obtained through the finite model property.  The
   independent route to Gbu◯ completeness through the LJF◯ translation
   (`gbuC_complete`, `wip/gbu_ljfo.lean`) still stands, and its
   independence is itself evidence; the compaction has *not* retired it
   (docs/frjw-compaction.md:50–52).

---

## Commissioning menu

| part | deliverable | est. effort |
|---|---|---|
| **A** | the recursion explainer proper: §A.1–A.7 written out with the quoted types, the measure table and the two-level diagram | 4–6 h |
| **B.2** | `#eval`-checked cell/measure trace for `G₁ = (p ⊃ ◯q) ⊃ (◯p ⊃ ◯q)`, as a new `wip/frjw_trace.lean` plus the table | 2–3 h |
| **B.2+** | the same for the two free-standing cells (corner, chase), including checking they behave as the walkthrough claims | 2 h |
| **B.3** | `show`-assertions at the ten stage boundaries in a shadow copy, one build | 3–4 h + build |
| **C.1–C.7** | the compaction itself (~330 lines), pins re-verified, smoke cell re-run | 4–6 h + builds |
| **D** | already written above; needs only trimming into the explainer | 30 min |

Nothing here is blocked on anything else, except that **B.3 should
follow C.1–C.7** if the compaction is commissioned — otherwise the stage
line numbers move under it.
