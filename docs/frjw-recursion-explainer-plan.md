# Plan for an FRJW/GBUW recursion explainer — the stage-4 brief

> **Status against the branch tip (2026-09-02, late morning, Fable).**
> This is the second version of the plan, written by an Opus subagent
> against `aa13537` (stage 3).  The first version (against `637dfcd`,
> stage 1) is archived at
> `docs/archive/frjw-recursion-explainer-plan-stage1.md`.  Between
> `aa13537` and the commit that lands this file, the following Part-C
> items were executed on Matthew's instruction (numbers in the first
> version's scheme, which Matthew used, then in this version's):
>
> | first-version # | this version's # | item | result |
> |---|---|---|---|
> | C.3 | §C.2 | `Focus`/`focusCtx`, `clo_focus`, `forall_cons`, `Focus.lt1`/`lt2` | `d633a37`: search 852 → 737 |
> | C.7 | §C.3 | `stepAll` as a flatten, one `sub_stepAll` | `60aee6d`: saturate 2531 → 2434 |
> | C.6 | §C.4 | `regUp`/`irrUp`, `downReg`/`downIrr` | `1fbdef7`: closure 1804 → 1803, block 226 → 183 |
> | — | §C.10 | the dead-declaration sweep (`wgTpLt`, `tpC_free_lt_circ`, `IHW`) | done in the commit landing this file |
>
> So the line numbers quoted for `wip/gbu_frjw_search.lean`,
> `wip/gbu_frjw_closure.lean` and `wip/gbu_frjw_saturate.lean` below
> are those of `aa13537` and have moved; names have not.  Part E, the
> stage-4 brief proper, is unaffected.  The register of
> `docs/frjw-compaction.md` ("The C-items") holds the verification
> record for each.

**This document is a PLAN, not the explainer.**  It sets out, in five
commissionable parts, what an explanation of the `decideGbuW` chain
would have to contain: what the recursions actually recurse on, how the
proof states could be made inspectable, which compaction combinators the
proof text supports (and which it does not), how to present the `⊕'`
framing, and (Part E, the priority for stage 4) the spine of a
narrative explanation of the proof STRATEGY.  Each part is separable;
the menu at the end gives effort estimates so parts can be commissioned
individually.

**Provenance of every line number below.**  Branch
`claude/frjw-w1-w2-lean-5aabff` at **`aa13537`** ("compaction stage 3 —
pair-V measure retired; searchW back on wgC = (unclosed, tpC,
seqSize)"), pushed to `origin/frjw-dev`.  File sizes at that commit:

| file | lines |
|---|---|
| `wip/gbu_frjw_dichotomy.lean` | 132 |
| `wip/gbu_frjw_search.lean` | 852 |
| `wip/gbu_frjw_closure.lean` | 1804 |
| `wip/gbu_frjw_saturate.lean` | 2531 |
| `wip/gbu_frjw_corner.lean` | 654 |
| `wip/gbu_frjw_circdb.lean` | 544 |
| `wip/gbu_frjw_db.lean` | 569 |
| `wip/gbu_frjw_exclusion.lean` | 47 |
| `FRJ/RefAt.lean` | 510 |
| `wip/gbu.lean` | 523 |
| `wip/gbu_circ.lean` | 2524 |

Line numbers move if the compaction proceeds; the explainer should be
regenerated against a pinned hash and say which.

Everything cited here is PROVED, sorry-free, `#guard_msgs`-pinned
`[propext, Quot.sound]`, with four declarations pinned lighter at
`[propext]`: `pledge_of_le`, `impInI_mono_sub`, `Gbu.W.wSubsumes_refl`,
`Gbu.W.wSubsumes_trans` (closure:1720, 1732, 1776, 1780).  Where I am
uncertain I say so; those places are marked **UNCERTAIN**.

**Vocabulary.**  An object of `FRJWr`/`FRJWi` is a DISPROOF; "proof" and
"derivation" are reserved for `Gbu◯`, `LaxND` and `G4c`.  The duality
being mechanised is due to Fiorentini and Ferrari (*Duality between
unprovability and provability in forward proof-search for Intuitionistic
Propositional Logic*, ACM TOCL 21(3), 2020); the `◯`-extension on both
sides is ours.  Nothing here is attributed to any other paper.

---

## PART A — What is being recursed on, exactly

### A.0 The objects the recursions move between

Stated once, so the rest can be terse.  All from
`wip/gbu_frjw_dichotomy.lean`.

    WSeq  = .reg (t : Tag) (Γ : List Form) (C : Form)
          | .irr (St Th : List Form) (C : Form)                    (58–60)

    WDerivable G (.reg t Γ C)  = Nonempty (FRJWr G t Γ C)
    WDerivable G (.irr St Th C) = Nonempty (FRJWi G St Th C)       (63–65)

    WSubsumes (.reg t₁ Γ₁ C₁) (.reg t₂ Γ₂ C₂) =
        C₁ = C₂ ∧ tagLeB t₁ t₂ = true ∧ Γ₁ ⊆ Γ₂
    WSubsumes (.irr St₁ Th₁ C₁) (.irr St₂ Th₂ C₂) =
        C₁ = C₂ ∧ St₁ ≐ St₂ ∧ Th₁ ⊆ Th₂
    WSubsumes _ _ = False                                          (70–75)

    WSaturated G D = (∀ s, D s → WDerivable G s)
                   ∧ (∀ s, WDerivable G s → ∃ s', D s' ∧ WSubsumes s s')
                                                                   (78–80)

    WEvalR D Ψ C = ∃ t Γ, D (.reg t Γ C) ∧ ∀ X ∈ Ψ, Clo Γ X        (85–86)
    WEvalI D Ω C = ∃ St Th, D (.irr St Th C) ∧ St ⊆ Ω ∧ Ω ⊆ St ++ Th
                                                                   (98–99)
    WUnrefutedBelow G D Ω C =
        ¬ WEvalI D Ω C ∧ ∃ Ω₀, (∀ X ∈ Ω₀, X ∈ gHat G) ∧
          (∀ X ∈ Ω₀, Clo Ω X) ∧ ¬ WEvalI D Ω₀ C                    (104–108)

and the target of the search, Type-valued:

    WSearchOk G D : Bool × List Form × Form → Type                 (121–130)
      | (true,  Ψ, C) => (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G →
                         ¬ WEvalR D Ψ C → GbuRC G Ψ C
      | (false, Ω, C) => (∀ X ∈ Ω, X ∈ sfL G) →
                         (C.isCirc = false → ∀ X ∈ Ω, X ∈ gHat G) →
                         C ∈ sfR G →
                         WUnrefutedBelow G D Ω C → GbuIC G Ω C

A *cell* is the triple `(reg?, Ψ, C)`, and at `aa13537` that is the
whole of the search state: there is no auxiliary parameter.

There are five genuine recursions in the chain, plus a handful of
list-scanning ones.  Each is treated below in the order the chain uses
them.

---

### A.1 `searchW`'s `main` — well-founded on the 3-lex measure

**File**: `wip/gbu_frjw_search.lean:274–817`, under
`set_option maxHeartbeats 3200000 in` (search:271).

**Recursion principle.**  `wgLt_wf.fix` (search:279), where

    WgLt (x y : Nat × Nat × Nat) =
      x.1 < y.1 ∨ (x.1 = y.1 ∧
        (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 < y.2.2)))     (gbu.lean:305–307)

    wgLt_wf : WellFounded WgLt                                 (gbu.lean:492–493)

`wgLt_wf` is proved through an explicit `Acc` construction on the triple
(`accWg`, gbu.lean:478–491) with `termination_by (a, b, c)` and a
`decreasing_by` block that maps `WgLt` into `Prod.Lex`.  This is the
pre-existing order of the `◯`-free layer; the FRJW search adds no
measure machinery of its own.

**The measure.**

    wgC G reg Ψ C = (unclosed G Ψ, tpC reg C, seqSize Ψ C)
                                                    (gbu_circ.lean:1634–1635)

with

    unclosed G Ψ  = (sfL G).countP (fun X => !cloB Ψ X)     (gbu.lean:262–263)
    tpC reg C     = if reg then 2 else if C.hasCirc then 1 else 0
                                                    (gbu_circ.lean:1631–1632)
    seqSize Ψ C   = (Ψ.map Form.size).sum + C.size          (gbu.lean:292–293)

**Motive, as it literally appears** (search:277–278):

```lean
have main : ∀ x : Nat × Nat × Nat, ∀ p : Bool × List Form × Form,
    wgC G p.1 p.2.1 p.2.2 = x → WSearchOk G D p
```

so the motive handed to `wgLt_wf.fix` is

    fun x => ∀ p, wgC G p.1 p.2.1 p.2.2 = x → WSearchOk G D p

Three things to say about this in the explainer.

1. The `wgC … = x` equation is the standard device for turning a
   well-founded fixpoint over *measure values* into one over *cells*:
   the recursive call supplies its own cell and proves its measure drops
   below `x`, and `hx ▸` (search:284) transports.
2. The motive is **Type-valued** (`WSearchOk … : Type`), so this is a
   `def`-shaped recursion producing terms, not a `theorem`.  That is the
   whole point: the positive side returns the `Gbu◯` derivation.
3. There are **no side conditions on an auxiliary parameter**.  The
   fixpoint takes the cell and nothing else.  (See the history paragraph
   below for what used to be there.)

**The induction hypothesis** (search:281–285), installed immediately
after the `fix`:

```lean
have IH : ∀ q : Bool × List Form × Form,
    WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G reg Ψ C) →
    WSearchOk G D q :=
  fun q hq => ihW _ (hx ▸ hq) q rfl
have IHW := IH
```

`IHW` is a bare alias with exactly two consumers (search:342, 399), a
residue of the stage-3 collapse.  It should be inlined; see §C.10.

**What one step consumes and produces.**  A step consumes a cell
`(reg, Ψ, C)`, the hypotheses `hΨ` (context ⊆ `Sf^L G`), `hC` (goal ∈
`Sf^R G`), the mode-specific `hΩc` or nothing, and the negative database
fact (`hne : ¬ WEvalR D Ψ C` regular, `hnb : WUnrefutedBelow G D Ψ C`
irregular, whose first component is `hne : ¬ WEvalI D Ψ C`, search:291).
It produces a `Gbu◯` derivation `GbuRC G Ψ C` or `GbuIC G Ψ C`, a
*term*, built by applying one `Gbu◯` constructor to the terms returned
by the recursive calls.  Every branch ends in either such a constructor
application or `absurd (…) hne`: the negative fact is contradicted
because the database would have had a row.

**Which measure component each step drops.**  Twenty-six recursive
calls, three payment lemmas, and they partition exactly:

| # | component | payment lemma | sites (search:) | count |
|---|---|---|---|---|
| 1 | `unclosed G Ψ` | `wgDrop` (170–172), always applied to `unclosed_lt` (gbu.lean:278–288) | 343 (irregular `R⊃ₙᵢ`), 400 (`totalityW`'s callback), 671 (regular `R⊃ₙ`) | 3 |
| 2 | `tpC reg C` | `wgFocus` (154–157), via `tpC_false_lt_true` | 589 (`limpStep`'s left premise), 689, 694 (regular `R∨ₖ`), 714 (regular `R◯`) | 4 |
| 3 | `seqSize Ψ C` | `wgKeep` (143–152) | 301, 307, 320, 326, 336, 427, 448, 473, 512, 549, 559, 610, 652, 657, 666, 733, 764, 791, 804 | 19 |

Component 1 must come first because `R⊃ₙ` *grows* the context, so
neither 2 nor 3 can pay for it; and `unclosed`-monotonicity
(`unclosed_mono`, gbu.lean:267–272) is what lets every other step keep
it constant.  Component 2 is graded by whether the goal *contains* a
`◯`, not whether it *is* one; the reason is recorded at the definition
(gbu_circ.lean:1622–1629): `R∧ᵢ` at `C₁ ∧ ◯C₂` would raise the latter.

An important nuance for the explainer, easy to get wrong: **the payment
lemma names the worst case it can prove, not the component that actually
drops at a given cell.**  `wgKeep` goes through `wgCCtx`
(gbu_circ.lean:1664–1674), which case-splits: if `unclosed` happens to
drop it returns `Or.inl` and components 2 and 3 are never consulted.  On
the primary example of §B.5 the `L◯` step is proved by `wgKeep` but the
operative drop is component 1.  So the table above says *what each step
is licensed by*, not *what falls at each cell*; the `#eval` trace of §B.2
says the latter.

`wgKeep` carries an auto-param for the `tpC` side condition
(search:145–150), trying in order `Nat.le_refl`, `tpC_false_mono orL'`,
`tpC_false_mono orR'`, `tpC_le_circ`.  Worth one sentence: it is why 9
of the 19 descent sites need no `tpC` argument written out at all.

**History (one paragraph, and no more).**  From the goal-closed state
(`a97787b`) through compaction stage 2, `searchW` carried a fourth
component and a fourth argument.  The corner had a *chase*: at a
critical `◯Z`-cell it applied `L⊃ᵢ` into a context implication's
antecedent `A`, whose size the goal `◯Z` does not bound, so neither
`seqSize` nor `tpC` could pay for the descent.  What paid was a visited
list `V : List (Form × Form)` of (antecedent, goal) pairs, with measure
component `vRem G V = |Sf^R(G) × Sf^R(G) ∖ V|`; pairs rather than
antecedents, so that re-chasing the same `A` under a different goal
stayed payable.  Stage 2 deleted the chase, because `totalityW` (§A.2)
settles every `Sf^R`-form at a critical cell outright and so decides the
antecedent without a chase; stage 3 then observed that `V` was constant
`[]` through the whole recursion and deleted the component, the
`WgLtW`/`wgW` order, and the two side conditions `hVsf`/`hregV`.  Both
retirements carry supersession tables at
`docs/frjw-compaction.md:84–95` and `:125–136`; no constraint was
re-opened.  The architecture note records the same at
`docs/searchw-architecture.md:29–32` and `:62`.  Nothing else in this
document refers to `V`.

---

### A.2 `totalityW` — structural induction on the goal formula

**File**: `wip/gbu_frjw_search.lean:212–267` (docstring 212–223,
declaration 224–267).  A `private def`, so again term-producing.

**Recursion principle**: structural on `X : Form` (the equation
compiler's own recursion; the recursive calls at 241–242, 247–248, 258
and 265 are all at immediate subformulas).

**Motive, literally** (search:224–231):

```lean
private def totalityW {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
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
derivation.  `R₀` is instantiated by the caller (search:370–371) as the
decidable list of *all* refuted `Sf^R`-forms.

**What a step consumes and produces**, per constructor of `Form`:

- `.bot` (232) → `.inl .bot`; no recursion.
- `.atom a` (233–239) → two decidable tests: is `a` refuted (`decI`), is
  `a ∈ Ψ`.  The `absurd` at search:239 is the *dilemma* that closed the
  corner: an atom absent from the context is refuted by the `Ax^I` row
  (`evalI_axI_gHat`), an atom present is derivable by `ax`.
- `.and`, `.or` (240–251) → both children recursed; the results combined
  by the De Morgan pairing (`∧`: one refuted side against both derivable
  sides; `∨`: both refuted against one derivable).
- `.imp A' B'` (252–263) → refuted as a form (`.ups`), else split on
  `Clo Ψ A'`: if closed, recurse on `B'`; if not, call `reccall`, which
  is the *non-structural* step (search:261–263).
- `.circ V` (264–267) → recurse on the body; `.circ rfl r` or
  `.rcircI d hX`.

**The one non-structural step.**  `reccall` is supplied by the caller as
a closure over `IHW` (search:398–407), paid for by measure component 1:
`wgDrop (unclosed_lt (sfR_imp hXsf).1 hncl)` (search:400–401).  So
`totalityW` is structurally recursive *given a callback whose
termination is the enclosing well-founded recursion's business*.  This
two-level arrangement is the single most important architectural point
in the whole chain and deserves its own diagram in the explainer
(see §E.iv).

---

### A.3 `tCr` / `tCi` — mutual structural induction on FRJW disproofs

**File**: `wip/gbu_frjw_closure.lean:1452–1677` (a `mutual` block);
`tCr` 1454–1602, `tCi` 1605–1675.

**Recursion principle**: structural, on the FRJW disproof term,
mutually (a regular disproof's premises can be irregular and vice
versa).  These are `theorem`s: the conclusion is a `Prop`
(`∃ r ∈ db, …`), so no data escapes.

**Motives, literally**:

```lean
theorem tCr {G : Form} {db : List (WRow G)} (hcl : DBClosed G db) :
    ∀ {t : Tag} {Γ : List Form} {C : Form},
      FRJWr G t Γ C → ∃ r ∈ db, WSubsumes (.reg t Γ C) r.s   (closure:1454–1456)

theorem tCi {G : Form} {db : List (WRow G)} (hcl : DBClosed G db) :
    ∀ {St Th : List Form} {C : Form},
      FRJWi G St Th C → ∃ r ∈ db, WSubsumes (.irr St Th C) r.s (closure:1605–1607)
```

Together they give

```lean
theorem tC_of_closed (hcl : DBClosed G db) :
    ∀ s, WDerivable G s → ∃ r ∈ db, WSubsumes s r.s           (closure:1681–1684)
```

which is exactly `WSaturated.2` for the membership predicate of a
`DBClosed` database (`wsat_of_closed`, closure:1073–1082).

**Case count**: `tCr` has 13 cases (axR 1457, andR1 1460, andR2 1466,
impIn 1472, circIn 1479, joinAt 1486, joinAtP 1497, joinAtF 1516,
joinOr 1528, joinOrP 1541, joinOrF 1560, joinCirc 1572, joinCircP 1585);
`tCi` has 8 (axI 1608, andI1 1611, andI2 1617, orI 1623, impInI 1643,
lift 1658, circNotIn 1665, axIC 1673).  Twenty-one in all, matching the
21 fields of `DBClosed` (closure:1179–1339) one for one.

**What one step consumes and produces.**  Uniformly, three moves:

1. *Recurse* on each premise, getting a stored subsumer as a `Prop`-level
   existential.
2. *Extract the shape*: `reg_shape` (closure:1367–1375) turns
   `WSubsumes (.reg t Γ C) s` into
   `s = .reg (tagOf s) (ctxOf s) C ∧ tagLeB t (tagOf s) = true ∧ Γ ⊆ ctxOf s`,
   and `irr_shape` (closure:1358–1365) the irregular analogue.  For the
   join rules, where the premises form a *family* indexed by `Fin (n+1)`,
   the per-premise existentials are turned into functions without choice
   by `irrPick` (closure:1393–1408) and `regPick` (closure:1419–1435),
   which skolemise through `List.find?` over the decidable subsumption
   test `subsumesB` (closure:1105–1146).
3. *Refire and close*: apply the matching `DBClosed` clause at the
   subsumers' shapes, transferring the rule's side conditions across the
   premise swap with the `_of_swap` lemmas (`hJ1_of_swap` closure:181–191,
   `hJ2_strict_of_swap` 193–201, `hJ5_of_swap` 747–759, `hJ7s_of_swap`
   761–770), then compose with `wSubsumes_trans` (closure:972).

The **T-B monotonicity** direction (the rule applied to stored subsumers
of its premises yields a conclusion subsuming the original's) is what
makes step 3 sound, and its nine standalone statements
(`joinCirc_mono` closure:235, `joinOr_mono` 267, `joinAt_mono` 322,
`circIn_mono` 376, `orI_mono` 408, `impInI_mono` 445, `joinAtF_mono` 607,
`joinOrF_mono` 636, `joinAtP_mono` 772, `joinOrP_mono` 806,
`joinCircP_mono` 840) are archived-in-place with no code consumer
(closure:42–50; `docs/frjw-compaction.md:32–46`).  The *live* content is
the transfer lemmas plus the context-inclusion lemmas (`joinOr_ctx_sub`
closure:213, `joinAt_ctx_sub` 299, `joinCtx*_mono` 547–733) and
`subset_of_ctxEq_left`, used 8 times to close a join case
(closure:1496, 1515, 1527, 1540, 1559, 1571, 1584, 1603).

---

### A.4 `sat` — fuel recursion, terminated by a pigeonhole

**File**: `wip/gbu_frjw_saturate.lean:1304–1390`.

**Recursion principle**: structural on a `Nat` fuel argument.  `sat` is
*not* well-founded recursion; the mathematical termination argument is a
separate theorem saying the supplied fuel suffices.

```lean
def sat (G : Form) : Nat → List (WRow G) → List (WRow G)
  | 0, db => db
  | fuel + 1, db =>
      let new := stepNew G db
      if new.isEmpty then db else sat G fuel (insertNew G new db)  (saturate:1304–1308)

def closureDB (G : Form) : List (WRow G) :=
  sat G ((univList G).length + 1) []                               (saturate:1364–1365)
```

**What one round consumes and produces.**  `stepAll G db`
(saturate:1206–1213) is a 19-fold `++` of emitters, firing every rule at
every stored premise combination: families range over
`(irrTs db).sublists` / `(regTs db).sublists`, parameters over
`goalPool G` and `(gAt G).sublists`, each emission guarded by a `dite`
on the rule's own decidable hypotheses, so every emitted `WRow` carries
its disproof by the corresponding FRJW constructor.  `stepNew`
(saturate:1301–1302) filters to rows whose *canonical key* is new;
`insertNew` (saturate:1232–1234) prepends them.

**The pigeonhole.**  Four lemmas:

```lean
insertNew_length_lt : (∃ r ∈ new, keyOf G r ∉ keysOf G db) →
    db.length < (insertNew G new db).length              (saturate:1266–1269)
insertNew_nodup    : (keysOf G db).Nodup →
    (keysOf G (insertNew G new db)).Nodup                (saturate:1286–1288)
keys_sub_univ      : ∀ k ∈ keysOf G db, k ∈ univList G   (saturate:1324–1325)
sat_fixed          : (keysOf G db).Nodup →
    (univList G).length + 1 ≤ db.length + fuel →
    (stepNew G (sat G fuel db)).isEmpty = true           (saturate:1331–1334)
```

`sat_fixed` is by induction on `fuel`: at `fuel = 0` the store's
key-list is nodup and inside `univList G`, so
`db.length ≤ (univList G).length`, contradicting the arithmetic
hypothesis; at `fuel+1` a non-empty round produces a fresh key,
`db.length` strictly grows, and the hypothesis is re-established.  The
finiteness of `univList G` (saturate:114–120) rests on the
wellformedness theorems `wfR`/`wfI` (banked earlier) plus `goalWr`,
`goalWi` and `tagWr` (closure:879–934): every derivable row has
`Ĝ`-bounded zones, an `Sf^R`-goal, and an `Sf^R`-pledged tag.

**Canonical keying** is what makes the pigeonhole finite despite rows
being stored in former-shaped (non-canonical) contexts:
`canonSeq G` (saturate:109–111) filters each zone through the
deduplicated pool, `canonCtx_congr` (saturate:67–72) says `≐`-equal
contexts have *equal* canonical lists, and `subsumes_of_canonSeq_eq`
(saturate:159–198) converts equal keys back into subsumption.  The
bridge to the clauses is

```lean
theorem stored_of_emitted (h : r ∈ stepAll G (closureDB G)) :
    ∃ e ∈ closureDB G, WSubsumes r.s e.s                 (saturate:1385–1390)
```

used 25 times, once per coverage lemma (21 clauses; four of them use it
twice through a `by_cases`: `cov_andR2`, `cov_andI2`, `cov_joinAtP`,
`cov_joinOrP`).

A note for the explainer: `dedupF` (saturate:76–78) is a hand-rolled
deduplication, present because mathlib's `List.mem_dedup` drags in
`Classical.choice` (saturate:74–75).  Three such choice leaks were
driven out at this stage (`docs/searchw-architecture.md:290–292`); the
point is worth making, because a decidability theorem that secretly used
choice would be worthless.  Decidability is never assumed here: it
follows from the completeness pair, and the axiom pin is the evidence.

---

### A.5 The T-A chain argument — `keptChain_sub_keptOf_of_le`

**File**: `wip/gbu_frjw_closure.lean:67–82`.

**Recursion principle**: induction on the inductive family
`KeptChain Υ base pool kept` (`FRJ/RefAt.lean:144–150`), whose `cons`
case carries a `RefAt true Υ (base ++ rest) Y` certificate over the base
plus *the earlier links only*.

```lean
theorem keptChain_sub_keptOf_of_le
    {Υ Υ' base base' pool pool' kept : List Form}
    (hu : Υ ⊆ Υ') (hb : base ⊆ base') (hp : pool ⊆ pool')
    (h : KeptChain Υ base pool kept) :
    ∀ Y ∈ kept, Y ∈ keptOf Υ' base' pool'                 (closure:67–71)
```

**What one step consumes and produces.**  At `cons Y B rest`
(closure:74–82): the induction hypothesis places `rest` inside
`keptOf Υ' base' pool'`; then `refAt_mono hu (…)` (`FRJ/RefAt.lean:52–63`)
lifts the link's certificate from `base ++ rest` to
`base' ++ keptOf …`, and `keptOf_saturated` (`FRJ/RefAt.lean:374`)
absorbs the link into the greedy fixpoint (`keptOf`,
`FRJ/RefAt.lean:245–257`).  The parameter-growth form (`hu`, `hb`, `hp`)
is what absorbs zone growth under premise swap; it is the reason a
*single* lemma serves both T-A and the join monotonicity cases.

The order-sensitivity worry (a link's certificate may cite `Clo Ψ`-facts
routed through *other* stuck implications) is dissolved elsewhere, by
`clo_sf_support` (corner:331) and `refutedCleanly_circ_certs`
(corner:470): a certificate's `Clo`-leaves are subformulas of its target,
hence strictly smaller, so a level-by-level construction on link size
always finds every leaf in place.  The explainer should present T-A and
that size argument together; separately they look like magic.

---

### A.6 The minor recursions (one table, for completeness)

| definition | file:line | principle | why it exists |
|---|---|---|---|
| `findNotT` | search:33–44 | structural on the list | constructive `findNot`, a total scan returning `(∀ a ∈ l, P a) ⊕' (Σ' a, a ∈ l ∧ ¬ P a)`; 8 call sites in `searchW` (353, 356, 375, 640, 645, 684, 699, 709) plus 2 in helpers (65, 202) |
| `splitOfMem` | search:46–55 | structural on the list | constructive split at a member, `Σ' s t, l = s ++ a :: t`; 5 call sites in `searchW` (411, 460, 489, 582, 725) plus 1 in `splitHatT` (69) |
| `splitHatT` | search:61–72 | via `findNotT` | all members `Ĝ`-shaped, or a split at a non-`Ĝ` member; 1 call site (575), the regular critical/non-critical fork |
| `findCMT` | search:197–208 | via `findNotT` over `(gAt G).sublists` | the classical countermodel scan for the `Ax^I◯` manufacture; `Decidable.of_not_not` (search:208) is what keeps it choice-free; 1 call site (368) |
| `dedupF` | saturate:76–78 | structural | choice-free deduplication |
| `decForallFin` / `decExistsFin` | saturate:688–711 | structural on `n` | `∀`/`∃` over `Fin` without `finRange` and without mathlib's `Fin` order instances (the recurring `Classical.choice` trap) |
| `growChain` / `keptOf` | RefAt.lean:245–257 | fuel = pool length | the greedy kept chain |
| `classForce_congr` | saturate:1688–1700 | structural on `Form` | `classForce` sees only atom membership |
| `rootDisproof?` | saturate:2444–2448 | structural on the store | the Type-valued root scan; its negative lemma `rootDisproof?_none` (2451–2468) recurses in lockstep |

### A.7 The chain, end to end

```
  wgLt_wf.fix ──> searchW ──> dichotomyW        (cell level, Type-valued)
        ↑              │
    totalityW ─────────┘        (structural on Form, with one callback)

  KeptChain-induction ──> T-A ──┐
  disproof-induction ──> tCr/tCi ──> tC_of_closed ──> decideGbuW_of_dbClosed
                                                              ↑
  fuel-recursion + pigeonhole ──> closureDB ──> closureDB_closed

  decideGbuW G : ProvableGbuC G ⊕' DisprovableW G     (saturate:2387–2388)
     ├─> provable_or_disprovable, frjw_complete, gbuw_complete,
     │   provableGbuC_iff_pll, disprovableW_iff_not_pll, decidePLL
     │                                                (saturate:2394–2431)
     └─> (bare form, separate route through the same store)
         decideGbuWData G : GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)
                                                      (saturate:2485–2487)
```

Key line numbers: `searchW` 274–817, `dichotomyW` 829–840,
`decideGbuW_of` closure:1089–1096, `decideGbuW_of_dbClosed`
closure:1688–1690, `closureDB_closed` saturate:2354–2378,
`decideOfStore` saturate:2472–2480.

---

## PART B — State previews at each main stage

### B.0 What "state" should mean here

Two different things are worth previewing, and the explainer should not
conflate them.

- **The proof state**: the Lean goal plus the named hypotheses in scope
  at a chosen point of `searchW`'s tactic block.  This is what makes the
  proof enterable; it is what a reviewer needs to check a branch without
  reading the whole file.
- **The search state**: the cell `(reg?, Ψ, C)` and the measure value
  `wgC G reg Ψ C`, at each step of a concrete run.  This is what makes
  the *algorithm* legible, and it is independently checkable by `#eval`.

I recommend producing both, with the search-state trace first: it is
cheap, mechanically checkable, and it gives the vocabulary for reading
the proof states.

### B.1 The stage map — where to cut, and what is in scope

All references `wip/gbu_frjw_search.lean` @ `aa13537`.

| stage | lines | new hypotheses at that point (as named in the code) |
|---|---|---|
| **S0** fixpoint set-up | 277–285 | `hsat`, `decI`; then `x`, `ihW`; `reg`, `Ψ`, `C`, `hx`; `IH`, `IHW` |
| **S1** mode split | 286 | `cases reg` |
| **S2** irregular preamble | 287–296 | `hΨ`, `hΩc`, `hC`, `hnb`, `hne`, `hax`; `atom`/`bot` close here |
| **S3** irregular `∧`/`∨`/`⊃` | 297–350 | `∧` 297–312 (`h₁`,`h₂`,`hg`,`d₁`,`d₂`); `∨` 313–330 (`he₁`,`he₂`); `⊃` 331–350 (`hA`,`hB`,`hcl`) |
| **S4** `◯`-goal dispatcher | 351–358 | `hZsf`; then `hg` (all of `Ψ` in `Ĝ`) or `⟨X,hXΨ,hXn⟩`; then `hnoc` or `⟨Y,hYΨ,hYc⟩` |
| **S5** the CRITICAL modal cell | 359–366 | `hΩai`; `byDec (decI Ψ Z)` |
| **S5a** `Z` refuted: row manufacture | 367–445 | `heZ` |
| **S5a-0** classical countermodel scan | 368–369 | `⟨ats,hsub,hFf,hall⟩` closes by `wEvalI_axIC`, else `hnocm` |
| **S5a-i** the certificate test | 370–384 | `R₀`, `hR₀def`, `hR₀ok`; `hallK` closes by `refutedCleanly_circ_certs` |
| **S5a-ii** **THE CORNER** (`totalityW`) | 385–445 | `⟨Y₂,hY₂,hnK⟩`, `hY₂i`, `hY₂Ψ`, `hA₂sf`, `hB₂sf`, `hRef`/`hDer`, `l₂`,`r₂`,`hsplit₂`, `hΓ₂`, `hclB₂`, `hmemsub₂`, `d₂` |
| **S5b** `Z` unrefuted: `R◯ᵢ` | 446–452 | `heZ` (negative), `d` |
| **S6** modal member: `L◯ᵢ` | 453–487 | `hYc'`, `lY`,`rY`,`hYsplit`, `hΓ`, `hmemsub`, `hY'sf`, `hcov`, `d` |
| **S7** non-`Ĝ` member: `⊥`/`∧`/`∨` left | 488–568 | `lX`,`rX`,`hXsplit`, `hΓ`, `hmemsub`; per case `hA`,`hB`,`hcov`/`hcovL`,`hcovR`,`hszo` |
| **S8** REGULAR preamble | 569–578 | `hΨ`, `hC`, `hne`, `hax`; `hall`/`⟨l,r,X,hsplit,hX⟩`; `hΩ` |
| **S8a** regular critical helpers | 579–637 | `limpStep` (579–626), `fromImp` (627–633), `upsToImp` (634–637) |
| **S8b** regular goal cases | 638–748 | atom 639–643, bot 644–648, `∧` 649–661, `⊃` 662–679, `∨` 680–697, `◯` 698–748 |
| **S9** non-critical invertible left rule | 749–816 | `hXmem`, `hΓ`, `hmemsub`; `⊥` 759, `∧` 760–782, `∨` 783–816 |
| **S10** the base call | 817 | `exact fun p => main _ p rfl` |

Two release points are worth naming explicitly because they are the
architecture, not bookkeeping.

- **Irregular to regular** (component 1 pays): the irregular `R⊃ₙᵢ`
  (search:342–350) and `totalityW`'s callback (search:398–407).  Both
  are `wgDrop (unclosed_lt …)`.
- **Regular to irregular** (component 2 pays): `wgFocus` at search:589
  (`limpStep`'s left premise `Ψ →g A`), 689 and 694 (`R∨ₖ`), 714 (`R◯`).

### B.2 Mechanism 1 (recommended): the `#eval`-checked cell/measure trace

Write a scratch file `wip/frjw_trace.lean` (a *new* file; nothing
existing is touched) that

1. fixes the example formula `G` and the cells of the trace as literal
   `Bool × List Form × Form` data;
2. `#eval`s, for each cell, the triple
   `(unclosed G Ψ, tpC reg C, seqSize Ψ C)`, i.e. exactly
   `wgC G reg Ψ C`, all three components computable;
3. `#eval`s the guards the searcher actually branches on, so the trace
   says *why* each branch fires: `cloB Ψ A`, `isHat X`, `impPart Ψ`,
   `X.isCirc`, `Form.size`, and membership in `sfL G` / `sfR G` /
   `gHat G` / `gAt G` / `gImp G`;
4. `#guard`s the strict-decrease claim `WgLt (wgC …) (wgC …)` between
   consecutive cells by evaluating the two triples and comparing
   lexicographically, and (this is the part the stage-1 version got
   wrong) records *which component* actually drops, which need not be
   the one the payment lemma is named for (see the nuance in §A.1).

The database-dependent test (`decI`) cannot be evaluated without the
concrete `closureDB G`, which is only feasible for the very smallest
formulas (see §B.4).  So the trace table should have a column "database
verdict" whose entries are *assumed* and labelled as such, with the
semantic justification given in prose (a `◯`-free goal not derivable
from the context is refuted; a context atom is not).  Everything
arithmetic is then machine-checked and everything database-level is
stated as an assumption of the walkthrough.

Deliverable: one markdown table, of the form

    step  rule fired   cell (reg?, Ψ, C)                    wgC          drops
    0     —            (true,  [],              G₁)         (5,2,10)     —
    1     R⊃ₙ          (true,  [p⊃◯q],          ◯p⊃◯q)      (4,2,9)      #1
    …

with the `wgC` column produced by `#eval` and pasted verbatim.

### B.3 Mechanism 2: `trace_state` in a shadow copy

`searchW`'s body is a tactic block, so proof states are directly
printable.  Method: copy `wip/gbu_frjw_search.lean` to
`wip/gbu_frjw_search_traced.lean` (a new file; the original is not
modified), insert `trace_state` at the stage boundaries of §B.1, and
build that file alone.  Notes and caveats:

- `set_option maxHeartbeats 3200000 in` (search:271) is already needed
  for the untraced file; the traced copy will be slower still.  Budget a
  single build, not an edit-rebuild loop.
- `trace_state` output at S5a-ii is large.  The useful artefact is a
  *curated* transcript: the goal, plus the hypotheses named in §B.1 for
  that stage, with the rest elided and the elision marked.
- An alternative with less output: `show` statements asserting the
  expected goal at each stage.  A `show` that elaborates is itself a
  check that the stage description is right, and it survives in the file
  as documentation.  **I recommend the `show`-assertion variant over raw
  `trace_state`**: it produces the same information, is self-checking,
  and does not depend on transcribing tool output.
- **UNCERTAIN**: I have not built the traced copy, so I cannot promise
  the `show` forms elaborate without `change`/`conv` massaging at every
  stage.  Budget accordingly (see the menu).  What would settle it: one
  build of the shadow copy.

### B.4 Mechanism 3: end-to-end `#eval` — what already exists

This is already built and its limits are already known.
`wip/decidepll_smoke.lean` (50 lines) runs
`@decide (PLL G) (decidePLL G)` on five cells, one per invocation, and
separately runs `decideGbuWData G` and reports which object came back:

    lake env lean --run wip/decidepll_smoke.lean impid
    lake env lean --run wip/decidepll_smoke.lean data atom

`wip/decidepll_smoke_out.txt` records 7/7 PASS twice over, once at the
goal-closed state and once as a regression after compaction stage 3
(2026-09-02 10:12 BST): `atom`, `bot`, `circbot` false; `p ⊃ p` and
`p ⊃ ◯p` true; and the bare form returning
`disproof(tag=chain (atom "p"), |Γ|=0)` for `atom` and `proof` for
`unit`.  The gate was watched failing and restored (line 2 of the output
file).  This is `#eval`-level evidence only; it taints nothing (the
`#guard_msgs` pins are the kernel gates), and a timeout is a FLAG, never
a verdict.

For the explainer this is worth one paragraph and no more.  It shows the
whole chain computes at the bottom of the scale, and it is **not** a
tracing mechanism, because `closureDB G` saturates the entire wellformed
universe of `G` before any cell is searched.  **UNCERTAIN**: I have not
measured where the wall is; the five passing cells have `|sfR G| ≤ 3`.
What would settle it: a fuelled sweep over formulas of increasing
`|sfR G|` with a wall-clock cap, reported as flags, not verdicts.

### B.5 The worked examples

**Primary: `G₁ = (p ⊃ ◯q) ⊃ (◯p ⊃ ◯q)`.**  PLL-valid (it is the strength
law of the lax modality), so `¬ WEvalR D [] G₁` holds by `soundnessW`
and `searchW` genuinely runs and returns a derivation.  Hand-computed
data, to be confirmed by `#eval` in the trace file:

    sfR G₁ = [G₁, p, ◯p⊃◯q, ◯q, q]
    sfL G₁ = [p⊃◯q, ◯q, q, ◯p, p]
    sizes  : p = 1, ◯q = 2, ◯p = 2, p⊃◯q = 4, ◯p⊃◯q = 5, G₁ = 10

Traced stages:

| step | stage | cell | `wgC` | operative drop |
|---|---|---|---|---|
| 0 | S8, S8b `⊃`, `rimpNI` (671) | `(true, [], G₁)` | `(5, 2, 10)` | — |
| 1 | S8, S8b `⊃`, `rimpNI` (671) | `(true, [p⊃◯q], ◯p⊃◯q)` | `(4, 2, 9)` | #1 |
| 2 | S8, S8b `◯`, `lcirc` (719–748) | `(true, [◯p, p⊃◯q], ◯q)` | `(3, 2, 8)` | #1 |
| 3 | S8, S8b `◯` critical (698–718), then `limpStep` | `(true, [p, p⊃◯q], ◯q)` | `(2, 2, 7)` | #1 |
| 4a | S2, `ax` (292–293) | `(false, [p⊃◯q, p], p)` | `(2, 0, 6)` | #2 |
| 4b | S8, `ax` (573–574) | `(true, [◯q, p], ◯q)` | `(2, 2, 5)` | #3 |

Reading of the interesting steps:

- step 2 fires because `findNotT (X.isCirc = false)` at search:699–701
  finds `◯p`, so the `L◯` branch (719–748) takes precedence over the
  critical branch;
- step 3 is the critical branch: `hnoc` holds (no modal member),
  `decI Ψ q` says `q` is refuted (`q` is not derivable from
  `[p, p⊃◯q]`), so the scan over `impPart Ψ = [p⊃◯q]` runs; `p ∈ Ψ`, so
  `p` is *not* refuted, and `fromImp` (627–633) hands to `limpStep`
  (579–626);
- `limpStep`'s `d₁` (588–607) is the release to irregular mode by
  `wgFocus`, and its `d₂` (608–625) is the `seqSize` descent into the
  consequent.

**Note for the explainer**, and the reason the table's last column
exists: on this example the operative drop is component 1 at three
consecutive steps even though steps 2 and 3 are proved by `wgKeep`.
That is `wgCCtx`'s case split doing its work (§A.1).

**Addendum for the pure-`seqSize` descent: `G₂ = ◯p ⊃ (◯p ∧ ◯p)`.**  Two
steps: `rimpNI` (671) to `(true, [◯p], ◯p ∧ ◯p)` with `wgC = (?, 2, 7)`,
then the regular `∧` case (649–661) to `(true, [◯p], ◯p)` with
`wgC = (?, 2, 4)`: the context is unchanged, so component 1 is constant,
`tpC` is constant at 2, and `seqSize` is the operative drop.  Then `ax`.
Two lines of trace, and it closes the coverage of the three components.

**A free-standing corner cell for `totalityW`.**  `WSearchOk` is a
per-cell statement, so the corner should be exhibited from a *cell*, not
from a root formula.  What the corner needs (search:359–445): an
irregular cell with `Ψ ⊆ Ĝ_at ∪ Ĝ_imp` (no modal member, all members in
`Ĝ`), goal `◯Z`, `Z` refuted at `Ψ`, no classical countermodel, and some
implication in `Ψ` whose antecedent fails both halves of the test at
search:375–377 (`ante Y ∈ R₀ ∨ RefAt true (Z :: R₀) Ψ (ante Y)`).
`totalityW` is then called at that antecedent, and the atom dilemma is
what decides it.

I recommend presenting `totalityW` **on its own**, at a cell chosen for
the dilemma rather than for reachability, e.g.

    G  = (p ⊃ q) ⊃ ◯r        Ψ = [p, p ⊃ q]        Z = r
    X ranges over sfR G;  R₀ = the refuted Sf^R-forms at Ψ

and walking the five clauses of the structural induction at
search:232–267, with the `atom` case (233–239) presented first because
it is where the dilemma lives: `p ∈ Ψ` gives `.inr (.ax …)`, and any
atom not in `Ψ` gives `.inl (.ups …)` through `evalI_axI_gHat`.

**UNCERTAIN** on two counts.  (i) I have not verified that this cell is
reachable from any root formula, nor that the `decI` verdicts come out
as the walkthrough needs; both should be `#eval`-checked (the syntactic
side conditions: `sfL`, `sfR`, `gHat`, `gAt`, `gImp`, `impPart`, `cloB`)
and the cell adjusted if not.  (ii) Reachability is not needed for
correctness of the exposition (`totalityW` is stated per cell), but it
IS needed if the explainer claims the walk is what the searcher does on
some formula.  What would settle both: the trace file of §B.2 extended
with the corner cell, plus one `#eval` of `closureDB G` for that `G` if
it is small enough.

**On the formulas that do NOT work.**  `◯p ⊃ p` and `◯(◯p ⊃ p)` are both
PLL-*invalid*, so `dichotomyW` (search:829–840) decides `WEvalR D [] G`
positively and takes the `.inl` branch: `searchW` is never entered.
They are the right examples for the *disproof* side ("the store already
has the row") and the wrong examples for tracing the search.  Worth one
explicit sentence in the explainer, because the asymmetry is easy to
miss, and `decideGbuWData` makes it demonstrable: the smoke run returns
`disproof(tag=chain (atom "p"), |Γ|=0)` for `G = p`.

### B.6 Recommendation and effort

Recommended package: **B.2 (the `#eval`-checked trace) plus B.3 in its
`show`-assertion variant, on `G₁`, the `G₂` addendum, and one
free-standing corner cell.**

| item | effort |
|---|---|
| B.2 trace file + table for `G₁` and `G₂` | 2–3 h |
| B.2 extended to the corner cell (incl. checking it behaves as claimed) | 2 h |
| B.3 `show`-assertions at the stage boundaries, one build | 3–4 h, plus one long build |
| B.3 raw `trace_state` transcripts instead | 2 h + a long build, but the artefact is worse |
| B.4 write-up of the existing smoke evidence | 20 min |

---

## PART C — Reusable tactics, and the strategy that is not a tactic

### C.0 What stage 3 already did to this survey

The stage-1 version of this plan listed nine candidates.  Stage 3
(`aa13537`) overtook two of them:

- **§C.2 of the old plan (`IHi`/`IHr`, retiring the `hregV` payload) is
  SUBSUMED.**  The `hregV` side condition no longer exists; the ~28
  lines it costed are already gone.  What survives of that item is one
  observation, now §C.10: `IHW` at search:285 is a bare alias.  The old
  §C.2's separate warning about the six `hΩc` lambdas sharing the
  `Bool.noConfusion` payload was vindicated the hard way during the
  stage-3 strip; it is recorded at `docs/frjw-compaction.md:112–117`.
- **§C.5 (`wfFixMeasure`) must now be extracted from the reverted
  form**, which is simpler: the fixpoint has no auxiliary parameter, so
  the combinator is the plain measure-fixpoint wrapper.

The remaining items are re-costed below against `aa13537`.  Savings are
line counts estimated by hand from the quoted text; they are
approximate and should be re-measured after each change.

### C.1 `byDecNeg` — RE-COSTED, and the verdict has changed

The stage-1 plan proposed

```lean
private def byDecNeg {p r : Prop} (d : Decidable p) {q : Sort _}
    (hnr : ¬ r) (h1 : p → r) (h2 : ¬ p → q) : q :=
  byDec d (fun hp => absurd (h1 hp) hnr) h2
```

on the strength of "the dominant use of `byDec` is a test whose positive
branch immediately contradicts the standing negative database
hypothesis".  Against `aa13537` that claim does not survive.  `byDec`
(search:21–25) is used 15 times: 4 in `totalityW` (234, 237, 253, 256),
10 in `searchW` (292, 316, 317, 334, 366, 573, 664, 682, 683, 708), 1 in
`dichotomyW` (833).  Of the nine `absurd (…) hne` closers in `searchW`,
exactly **one** is the positive branch of the `byDec` immediately above
it:

```lean
· refine byDec (decI Ψ C₂) (fun he₂ => ?_) (fun he₂ => ?_)
  · exact absurd (gbuInv10 hsat hC he₁ he₂) hne              (search:317–318)
```

The other eight sit one scan deeper or in a different scrutinee:

| site | closer | what the branch actually came from |
|---|---|---|
| 295, 296 | `evalI_axI_gHat` | a `cases C` arm *after* `byDec (C ∈ Ψ)` |
| 369 | `wEvalI_axIC` | `findCMT`'s `.inl` branch |
| 379–384 | `gbuInvLift ∘ wEvalR_of_refutedCleanly ∘ refutedCleanly_circ_certs` | `findNotT`'s `.inl` branch |
| 642, 647 | `gbuSuccAtF` | `findNotT (decI Ψ (ante Y))`'s `.inl` branch |
| 686 | `gbuSuccOrF` | `findNotT`'s `.inl`, inside two `byDec` positives |
| 711 | `gbuSuccCirc` | `findNotT`'s `.inl`, inside a `byDec` positive |

and `totalityW`'s one such closer (search:239) contradicts on the
**negative** branch, so it would need a dual combinator anyway.

**Verdict: do not build `byDecNeg`.**  It fits one site, saves one line,
and the "impossible: the store would have had a row" reading it was
meant to buy is already carried by the named lemma at the site.  The
recurring shape is not "decide then contradict" but "scan then
contradict", and `findNotT` already is that combinator.

### C.2 `focusCtx`, `clo_focus`, `sfL_cons` — the principal-formula step

**Still the largest item.**  The most repeated block in `searchW` is:
split the context at the principal formula, build the `≐`, derive the
three consequences (membership, `Clo`-coverage, `Sf^L`-preservation),
and do the `seqSize` arithmetic.

Quoted, twice (of six split blocks: search:411–423, 460–464, 489–493,
582–587, 725–729, and the S9 variant 751–754):

```lean
obtain ⟨lY, rY, hYsplit⟩ := splitOfMem hYΨ
have hΓ : Ψ ≐ .circ Y' :: (lY ++ rY) := by
  rw [hYsplit]; exact ctxEq_split
have hmemsub : ∀ V ∈ lY ++ rY, V ∈ Ψ :=
  fun V hV => (hΓ V).mpr (List.mem_cons_of_mem _ hV)          (search:460–464)
```
```lean
obtain ⟨lY, rY, hYsplit⟩ := splitOfMem hYΨ
obtain ⟨hAsf, hBsf⟩ := sfL_imp (hΨ _ hYΨ)
have hΓ : Ψ ≐ .imp A B :: (lY ++ rY) := by
  rw [hYsplit]; exact ctxEq_split
have hmemsub : ∀ W ∈ lY ++ rY, W ∈ Ψ :=
  fun W hW => (hΓ W).mpr (List.mem_cons_of_mem _ hW)          (search:582–587)
```

and the arithmetic, eight times identically modulo the split name
(search:431, 476, 515, 536, 615, 738, 769, 788):

```lean
rw [hYsplit, seqSize_split, seqSize_cons]
```

Proposed, one structure packaging the split with its consequences:

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

`clo_focus` collapses ten three-to-five-line blocks (search:414–420 the
corner's `hclB₂`, 466–470, 504–509, 538–542, 543–547, 610–613, 733–736,
764–768, 791–794, 804–807) to one-liners such as
`clo_focus hΓ (.imp (.base List.mem_cons_self))`.  `sfL_cons`
collapses sixteen `intro W hW; rcases List.mem_cons.mp hW with rfl | hW'`
blocks (search:344–348, 402–406, 437–441, 480–484, 520–526, 551–555,
561–565, 591–595, 596–600, 602–606, 620–624, 673–677, 742–746, 774–780,
797–801, 810–814).  There are 31 `rcases List.mem_cons.mp` occurrences
in the file; not all are of this shape.

Saving: ≈ 24 (`focusCtx`) + ≈ 8 (the `seqSize` rewrites) + ≈ 33
(`clo_focus`) + ≈ 48 (`sfL_cons`) ≈ **110 lines** on an 852-line file,
the single largest item in this survey, and the one that most improves
legibility: each rule step becomes "focus, cover, descend, apply the
constructor".

### C.3 `stepAll` as a flatten — retire the nineteen `sub_stepAll_*`

`stepAll` is a 19-fold `++` (saturate:1206–1213), and membership in it is
proved by nineteen near-identical theorems (saturate:1423–1535, 113
lines) whose payloads are nested `Or.inl` chains up to eighteen deep:

```lean
theorem sub_stepAll_AxR {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitAxR G, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inl (Or.inl hx)))))))))))))))))                 (saturate:1423–1427)
```
```lean
theorem sub_stepAll_JoinCircP {G : Form} {db : List (WRow G)} :
    ∀ x ∈ emitJoinCircP G db, x ∈ stepAll G db := by
  intro x hx
  simp only [stepAll, List.mem_append]
  exact Or.inr hx                                       (saturate:1531–1535)
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

with the 25 call sites in the coverage layer becoming
`sub_stepAll (by simp [emitters]) hemit`, or 19 one-line abbreviations.
Saving ≈ **95 lines**, and it removes the most brittle text in the
development: an `Or.inl` chain that must be recounted whenever an
emitter is added.

### C.4 `regUp` / `irrUp` and the closers — the T-C unary shape

Quoted twice (of nine unary cases in `tCr`/`tCi`: andR1, andR2, impIn,
circIn, andI1, andI2, impInI, lift, circNotIn):

```lean
| _, _, _, .impIn (A := A) (B := B) d hA hg => by
    obtain ⟨r, hr, hsub⟩ := tCr hcl d
    obtain ⟨hshape, hle, hΓ⟩ := reg_shape hsub
    obtain ⟨r₂, hr₂, hsub₂⟩ := hcl.impIn (tagOf r.s) (ctxOf r.s) A B
      (by rw [← hshape]; exact List.mem_map.mpr ⟨r, hr, rfl⟩)
      (clo_mono hΓ hA) hg
    exact ⟨r₂, hr₂, wSubsumes_trans (wSubsumes_reg hle hΓ) hsub₂⟩ (closure:1472–1478)
```
```lean
| _, _, _, .andI1 (A₁ := A₁) (A₂ := A₂) d hg => by
    obtain ⟨r, hr, hsub⟩ := tCi hcl d
    obtain ⟨hshape, hst, hth⟩ := irr_shape hsub
    obtain ⟨r₂, hr₂, hsub₂⟩ := hcl.andI1 (stabOf r.s) (thOf r.s) A₁ A₂
      (by rw [← hshape]; exact List.mem_map.mpr ⟨r, hr, rfl⟩) hg
    exact ⟨r₂, hr₂, wSubsumes_trans (wSubsumes_irr hst.symm hth) hsub₂⟩ (closure:1611–1616)
```

The incantation `by rw [← hshape]; exact List.mem_map.mpr ⟨r, hr, rfl⟩`
appears 9 times (closure:1464, 1470, 1476, 1483, 1615, 1621, 1648, 1662,
1669).  Proposed:

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

Saving ≈ 3 lines × 9 sites ≈ **27 lines**, plus the disappearance of the
`r₂`/`hr₂` scaffolding.  For the eight join closers, `downReg` alone
absorbs the closer (`subset_of_ctxEq_left` appears 8 times inside it,
closure:1496, 1515, 1527, 1540, 1559, 1571, 1584, 1603): another
≈ 16 lines.

### C.5 `wgGoal` — the pure goal-descent measure step

Nine of the nineteen `wgKeep` sites are the same two-line incantation
(search:301–302, 307–308, 320–321, 326–327, 336–337, 448–449, 652–653,
657–658, 666–667):

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

Saving ≈ **9 lines**.  Low risk; the auto-param already exists on
`wgKeep`.

### C.6 `wfFixMeasure` — the measure-fixpoint wrapper

The `∀ x, … → wgC … = x → …` device plus the `hx ▸` transport
(search:277–284) is boilerplate for "well-founded recursion on a
measure".  Since stage 3 there is no auxiliary parameter, so the
combinator is the textbook one:

```lean
def wfFixMeasure {α : Sort u} {β : Sort v} {ρ : β → β → Prop}
    (hwf : WellFounded ρ) (m : α → β) {C : α → Sort w}
    (step : ∀ a, (∀ a', ρ (m a') (m a) → C a') → C a) : ∀ a, C a
```

It is instantiated **twice** in the repository (here, and in `searchO`,
the retired `◯`-free predecessor in `wip/gbu_search_circ.lean`), so
extracting it is not speculative.  Saving here ≈ 8 lines.  The case for
it is reuse, not size: it is the piece a *third* calculus would want
first.

### C.7 The coverage skeleton — a macro, with a caveat

Twenty-five sites share the shape

```lean
have hemit : (⟨.reg .barren (rm (gAt G) F) F,
    .axR F hF hg (CtxEq.refl _)⟩ : WRow G) ∈ emitAxR G := by
  refine List.mem_filterMap.mpr ⟨F, mem_goalPool.mpr hg, ?_⟩
  exact dif_pos ⟨hF, hg⟩
exact stored_of_emitted (sub_stepAll_AxR _ hemit)         (saturate:1671–1675)
```

(`stored_of_emitted` 25×, `List.mem_filterMap.mpr` 26×,
`mem_goalPool.mpr` 26×, `dif_pos` 25×.)

A `macro "cover" …` taking the emitter lemma, the goal-pool witness and
the `dite` payload would save ≈ 2 lines × 25 ≈ 50 lines.  **My
assessment is that this one is marginal**: the shapes differ in arity
(one, two or three `mem_flatMap` layers) and in whether a `by_cases`
precedes, and a macro that has to take all of that as parameters is not
obviously more readable than the explicit text.  Rank it below C.3,
which achieves a comparable saving with no loss of explicitness.

### C.8 The `_of_swap` / `SameIrr` congruence layer — verdict: leave it

`SameIrr` / `SameReg` (saturate:214–231) with their ~25 congruence
lemmas, and the four `_of_swap` transfers (closure:181–201, 747–770), are
already the factored form of "a join depends on its family only through
the row set".  The individual lemmas are one-liners over
`mem_unionAll` / `List.mem_filter`; there is no further common factor I
can see that is not just `simp`.  **Recommend: no change.**  The one
observation worth making in the explainer is structural rather than
compactive: `SameIrr` is exactly the statement that the join rules factor
through the *set* of premise rows, which is why arbitrary-arity families
can be reindexed to stored sublists at all (`reindex_irr`,
saturate:1540–1611; `reindex_reg`, 1614–1659).

### C.9 Could the MAIN induction be a reusable combinator?

The old plan asked whether the `A ⊕' B`-shaped target invites a generic
"decide-or-recurse for dual calculi".  My assessment, unchanged and now
better evidenced by §C.11:

**What such a combinator would buy is the fixpoint plumbing only, i.e.
exactly C.6.**  The abstraction would need four parameters (the cell
type, the measure, the rule set of the proof calculus, and the query
interface of the refutation calculus's store) and the entire content of
`searchW` sits in the last two.  Concretely:

- The branch structure is not generic.  Every `byDec` and every
  `findNotT` in `searchW` is on a query whose meaning is FRJW-specific
  (`WEvalI`, `Clo`, `∈ Ψ`, `isCirc`, `gHat`), and each positive branch
  is closed by a *named inversion lemma* of the Gbu◯/FRJW pair.  There
  is no calculus-independent statement of "the positive branch is
  impossible"; that IS the duality, proved rule by rule.
- The measure is not generic either: `unclosed` is defined from `Cl(Γ)`,
  a Gbu-specific closure operator, and `tpC`'s grading by `hasCirc` is a
  fact about *this* modality's `L⊃ᵢ` licence.
- The `⊕'` shape at the target is genuinely generic, but it is one line
  of type, not an argument.

So: `byDec`, `findNotT` and `splitOfMem` already give everything a
generic decide-or-scan combinator would give at the branch level;
`wfFixMeasure` gives everything it would give at the recursion level;
and there is nothing in between.  I would not build the abstract
combinator.  What I *would* extract, if the intention is to make the
technique reusable for a third calculus, is not a combinator but a
**checklist**: the three measure components and what each pays for, the
two-level arrangement of §A.2 (structural totality with a measure-paid
callback), and the canonical-key-plus-pigeonhole saturation of §A.4.
Those transfer; the code does not.

### C.10 Declarations that are now dead — a stage-4 sweep

Found while re-deriving the line numbers.  All are `private`, so the
check is file-local and complete.

| declaration | file:line | consumers at `aa13537` |
|---|---|---|
| `wgTpLt` | search:159–162 | **none** (it paid for the chase's `◯`-free-antecedent release) |
| `tpC_free_lt_circ` | search:164–168 | **none** (only `wgTpLt` used it) |
| `IHW` | search:285 | a bare `have IHW := IH`; two uses (342, 399) that can read `IH` |

Removing all three is ≈ 12 lines and zero mathematical content.  This is
a stage-4 item, not a stage-5 one: it is exactly the residue stage 3
left behind, and it should be swept before the explainer's line numbers
are frozen.

**UNCERTAIN**: I have not compiled the file with these removed.  What
would settle it: one `lake build wip.gbu_frjw_search` after the deletion,
with the two pins (search:844–850) checked byte-identical.

### C.11 The inversion-lemma bank — the STRATEGY

Matthew's remark: *"Creating and gathering the named inversion lemmas is
a strategy but maybe not a tactic, but you are in the best place to
know."*  He is right, and the separation is worth making sharply,
because it is the difference between the mathematical content of the
duality and the typing of it.

**The strategy.**  For every rule of `Gbu◯`, there is a lemma saying:
*if the store answers the premise query, then it answers the conclusion
query.*  Contrapositively, at a cell where the store does NOT answer,
the premise query is unanswered too, which is exactly the negative
hypothesis the recursive call needs.  These lemmas are proved **once per
rule**, by opening `WSaturated` (its `.1` extracts the premise row's
disproof, its `.2` re-stores the FRJW constructor applied to it), and
they are the mathematical content of the duality: each one is the FRJW
rule that mirrors one `Gbu◯` rule.  Gathering them into a bank is the
strategy; it is what makes `searchW` a rule-by-rule walk instead of a
search.

The bank, in full, with consuming sites in
`wip/gbu_frjw_search.lean` @ `aa13537`:

| lemma | file:line | statement (schematically) | consumed at |
|---|---|---|---|
| `gbuInv1` | db:63–70 | `WEvalR D (A::B::Ψ) C → WEvalR D (A∧B::Ψ) C` | 781 (`L∧`) |
| `gbuInv2` | db:99–113 | `A∧B ∈ sfR G → WEvalR D Ψ C₁ ∨ WEvalR D Ψ C₂ → WEvalR D Ψ (C₁∧C₂)` | 655, 660 (`R∧`) |
| `gbuInv3L` | db:73–79 | `WEvalR D (A₁::Ψ) C → WEvalR D (A₁∨A₂::Ψ) C` | 802 (`L∨`, left) |
| `gbuInv3R` | db:81–87 | `WEvalR D (A₂::Ψ) C → WEvalR D (A₁∨A₂::Ψ) C` | 815 (`L∨`, right) |
| `gbuInv4` | db:90–96 | `WEvalR D (B::Ψ) C → WEvalR D (A⊃B::Ψ) C` | 625 (`L⊃`, right premise) |
| `gbuInv5` | db:116–126 | `A⊃B ∈ sfR G → Clo Ψ A → WEvalR D Ψ B → WEvalR D Ψ (A⊃B)` | 669 (`R⊃`) |
| `gbuInv6` | db:129–139 | `A⊃B ∈ sfR G → WEvalR D (A::Ψ) B → WEvalR D Ψ (A⊃B)` | 678 (`R⊃ₙ`) |
| `gbuInv7` | db:142–161 | `A∧B ∈ sfR G → WEvalI D Ω C₁ ∨ WEvalI D Ω C₂ → WEvalI D Ω (C₁∧C₂)` | 305, 311 (`R∧ᵢ`) |
| `gbuInv8` | db:165–211 | `A⊃B ∈ sfR G → Clo Ω A → WEvalI D Ω B → WEvalI D Ω (A⊃B)` | 340 (`R⊃ᵢ`) |
| `gbuInv9` | db:216–230 | `A⊃B ∈ sfR G → Ω ⊆ Ĝ → WEvalR D (A::Ω) B → WEvalI D Ω (A⊃B)` | 349 (`R⊃ₙᵢ`), 263 (inside `totalityW`) |
| `gbuInv10` | db:234–260 | `C₁∨C₂ ∈ sfR G → WEvalI D Ω C₁ → WEvalI D Ω C₂ → WEvalI D Ω (C₁∨C₂)` | 318 (`R∨ᵢ`) |
| `gbuInv11` | circdb:25–31 | `WEvalR D (Z::Ψ) C → WEvalR D (◯Z::Ψ) C` | 747 (`L◯`) |
| `gbuInv14` | circdb:418–469 | `Ω ⊆ Ĝ → (∀ X ∈ Ω, Clo Ω' X) → WEvalI D Ω' (◯Z) → WEvalI D Ω (◯Z)` | via `unrefutedBelow_step` (circdb:484), at 5 sites: 443, 486, 528, 557, 567 |
| `gbuInvLift` | circdb:521–533 | `Ω ⊆ Ĝ → WEvalR D Ω C → WEvalI D Ω C` | 379 (the corner's certificate branch) |
| `evalI_axI_gHat` | circdb:34–50 | `Ω ⊆ Ĝ → F.isPrime → F ∈ sfR G → F ∉ Ω → WEvalI D Ω F` | 295, 296 (`ax`), 239 (inside `totalityW`) |
| `wEvalI_axIC` | search:179–193 | a classical countermodel over `Ĝ_at` gives the vacuous-zone `◯F`-row | 369 |
| `gbuSuccAtF` | circdb:54–153 | `Ω ⊆ Ĝ → F prime, unmet, all antecedents refuted → WEvalR D Ω F` | 642, 647 |
| `gbuSuccOrF` | circdb:156–257 | the `∨`-goal analogue | 686 |
| `gbuSuccCirc` | circdb:385–392 | `Ω ⊆ Ĝ_at ∪ Ĝ_imp → ◯Z ∈ sfR G → all antecedents refuted → Z refuted → WEvalR D Ω (◯Z)` | 711 |
| `refutedCleanly_circ_certs` | corner:470–637 | the corner manufacture: `⋈^◯` over `Z :: R`, kept chain built level by level on link size | 381 |
| `wEvalR_of_refutedCleanly` | db:289–292 | a clean refutation reaches the store (through `wEvalRP_of_refutedCleanly`, db:278–286) | 380 |
| `unrefutedBelow_of_gHat` | circdb:472–475 | on a `Ĝ`-context, bare `¬ WEvalI` is the full invariant | 304, 310, 323, 329, 451, 601, 691, 696, 717 |
| `unrefutedBelow_step` | circdb:478–484 | every left rule preserves the invariant at a `◯` goal | 443, 486, 528, 557, 567 |

Twenty-five consumption sites for the inversion lemmas proper, plus
fourteen for the two `WUnrefutedBelow` wrappers: thirty-nine in all.

Three lemmas in the bank's files are **not** consumed by the live chain
at `aa13537` and should be labelled archive in the explainer, not
presented as load-bearing: `gbuInv12` (circdb:488–498) and `gbuInv13`
(circdb:502–515), which take the pledged lookup `WEvalRP` and lost
their consumer when `decRP` left the chain at stage 2
(`docs/frjw-compaction.md:75–78`); and `gbuSuccCircI`
(circdb:400–412).  Similarly `refutedCleanly_circ_kept` (corner:92) and
`refutedCleanly_circ_axI` (corner:251) are pinned banked results whose
consumer went with the pre-totality corner
(`docs/frjw-compaction.md:53–54`).  They are correct and compiled; they
are not part of the current argument.

### C.12 The tactic-shaped part — assessment and verdict

The uniform consumption pattern the brief names is real.  It has two
shapes, and they behave differently.

**Shape 1, the closer** (9 sites): a scan or test comes back positive on
every branch, and the conclusion is a store row that the standing
negative hypothesis forbids.

```lean
· exact absurd (gbuSuccCirc hsat hΩai hC (upsToImp hallI) heZ) hne  (search:711)
```

**Shape 2, the payload** (14 sites): a recursive call needs the negative
hypothesis at the *premise* cell, obtained by contraposing the same
lemma.

```lean
hΨ hB (fun h => hne (gbuInv5 hsat hC hcl h))                        (search:669)
```

Now the concrete question: would `first | exact absurd (gbuInv₁ …) hne |
exact absurd (gbuInv₂ …) hne | …` over the bank work at all these sites?

**What is in scope at every site.**  The searcher's binders are stable:
`hsat` and `decI` from `searchW`'s signature; `hΨ`, `hC`, `hne` (and
`hnb`, `hΩc`) from the mode `show`/`intro` at 288–291 or 570–572; `IH`
from 281.  Local names are also stable within a branch: `hcl` from
`byDec (decClo …)`, `hΓ` from the focus block, `he₁`/`he₂`/`heZ` from
`byDec (decI …)`, `hallI` from `findNotT`, `hg` (irregular) or `hΩ`
(regular) for `Ĝ`-membership.

**Arguments needed beyond what is in scope.**  Counting per lemma, the
arguments a tactic would have to supply that are NOT simply a name in
scope:

| lemma | extra arguments the site supplies |
|---|---|
| `gbuInv1`, `gbuInv3L`, `gbuInv3R`, `gbuInv4`, `gbuInv11` | none, but the result must be wrapped in `wEvalR_ctxEq (ctxEq_symm hΓ)` (4 of the 5 sites) |
| `gbuInv2`, `gbuInv7` | `Or.inl` vs `Or.inr` (disambiguated by the goal, so `first` can try both) |
| `gbuInv5`, `gbuInv8` | `hcl` (in scope) |
| `gbuInv6` | none |
| `gbuInv9` | `hg` irregular / `hX` and `hg` inside `totalityW` (name differs) |
| `gbuInv10` | `he₁` from an *enclosing* `byDec` positive branch |
| `gbuSuccAtF` | `rfl` for the primality of the goal, which depends on the `cases C` arm |
| `gbuSuccOrF`, `gbuSuccCirc` | `upsToImp hallI`, a locally defined helper (search:634–637) |
| `evalI_axI_gHat` | `rfl` for primality, `hax` for non-membership |
| `refutedCleanly_circ_certs` | five arguments, one of them a `?_` hole discharged by a two-line tactic (search:382–384) |

So every alternative *is* expressible as a closed term in stable names,
with two exceptions (`totalityW`'s renamed binders, and the
`refutedCleanly_circ_certs` site's hole), and a `first` combinator
would in principle disambiguate by elaboration failure.

**Verdict: build the bank, do not build the tactic.**  Three reasons,
in order of weight.

1. **It saves nothing.**  Every one of the 23 usable sites is already a
   single line, and `exact absurd (gbuInv10 hsat hC he₁ he₂) hne` is
   *shorter* than any `close_dual`-style invocation that has to name the
   goal-membership witness anyway.  A tactic here is negative-value on
   line count.
2. **It destroys the documentation.**  The named lemma at the site is
   the whole point: it says *which clause of the duality* is being used
   at *which rule*.  Replacing 15 distinct names by one tactic converts
   the most legible part of the file into the least legible.  For a
   development whose stated purpose (the explainer) is to make the proof
   enterable, that is the wrong trade.
3. **It costs build time.**  A 20-branch `first` re-elaborates up to 19
   failing alternatives at each of 23 sites, in a file that already
   needs `set_option maxHeartbeats 3200000` (search:271).  I have not
   measured the cost, so this is a risk rather than a finding
   (**UNCERTAIN**; what would settle it: prototype the `first` at three
   sites and compare `count_heartbeats`), but the direction is not in
   doubt.

The one piece of genuine tactic-shaped reuse in this region is not over
the bank at all: it is `findNotT` (search:33–44), which already
*is* the "scan, and on the all-positive branch you have the fact that
closes the cell" combinator, with 10 call sites.  It was worth building;
a `first` over the bank is not.

**What the explainer should say instead.**  Present the bank as a
TABLE, one row per `Gbu◯` rule, three columns: the rule, its inversion
lemma, and the site where `searchW` consumes it.  That table IS the
proof strategy at cell level, and it is a page.  §E.iii below builds on
this.

### C.13 Ranked summary

| # | item | est. saving | risk | note |
|---|---|---|---|---|
| C.2 | `focusCtx` / `clo_focus` / `sfL_cons` | ~110 | low | biggest legibility gain |
| C.3 | `stepAll` as flatten, one `sub_stepAll` | ~95 | low | also removes the brittlest text |
| C.4 | `regUp`/`irrUp` + `downReg`/`downIrr` | ~43 | low | 9 unary + 8 join closers |
| C.7 | coverage macro | ~50 | medium | marginal; readability cost |
| C.10 | dead-declaration sweep | ~12 | very low | do this first, before line numbers freeze |
| C.5 | `wgGoal` | ~9 | low | |
| C.6 | `wfFixMeasure` | ~8 | low | value is reuse, not size |
| C.1 | `byDecNeg` | ~1 | — | **recommend not building** (re-costed) |
| C.8 | `SameIrr` layer | 0 | — | recommend no change |
| C.9 | generic dual-calculus combinator | 0 | — | recommend not building |
| C.12 | `first`-over-the-bank tactic | negative | — | **recommend not building**; the bank is the strategy |

Total realistic saving from the low-risk items (C.2–C.6, C.10; C.7
excluded): ≈ **280 lines**, on a 5,187-line core (search 852 + closure
1804 + saturate 2531), with no change to the mathematics and every
`#guard_msgs` pin expected to be byte-identical.  The discipline used
for stages 1–3 applies: strip, then verify the pins unchanged and the
smoke cells still PASS, building the wip chain by explicit target
(`lake build wip.gbu_frjw_search wip.gbu_frjw_closure
wip.gbu_frjw_saturate`), since the wip library is not in
`defaultTargets` (`docs/frjw-compaction.md:120–123`).

---

## PART D — The `⊕'` framing, explained

A short section for the explainer; here is its content in full, since it
is short enough to settle now rather than commission.

### D.1 Why not `⊕`

`Sum` (`⊕`) is `Type u → Type v → Type (max u v)`.  Both sides at the
crown are `Prop`s:

    ProvableGbuC G : Prop := Nonempty (GbuRC G [] G)     (gbu_circ.lean:1368)
    DisprovableW G : Prop := ∃ (t : Tag) (Γ : List Form),
                               Nonempty (FRJWr G t Γ G)  (CalculusW.lean:246–247)

so `ProvableGbuC G ⊕ DisprovableW G` does not typecheck.  `PSum` (`⊕'`)
is `Sort u → Sort v → Sort (max 1 u v)`: it accepts `Sort 0` arguments
and lands in `Type 0` when both are `Prop`.  This is the immediate,
mechanical reason, but it is not the interesting one.

### D.2 Why not `∨`

`ProvableGbuC G ∨ DisprovableW G` typechecks and is *provable*: it is
`provable_or_disprovable` (saturate:2394–2398), obtained from
`decideGbuW` by forgetting.  What it cannot do is be **eliminated into a
`Type`**.  `Or` is a `Prop`, and Lean's large-elimination restriction
forbids matching on a `Prop`-valued inductive to produce data (except
for subsingletons).  So from `A ∨ B` one cannot build
`Decidable (PLL G)`, which is `Sort 1` data (`isTrue h | isFalse h`),
without `Classical.choice`.

That is exactly what is at stake, and it is visible in the pin.  With
`⊕'`:

```lean
def decidePLL (G : Form) : Decidable (PLL G) :=
  match decideGbuW G with
  | .inl h => isTrue (FRJ.Gbu.pll_of_provableGbuC h)
  | .inr h => isFalse (FRJ.soundnessW h)               (saturate:2428–2431)

/-- info: 'FRJ.Gbu.W.decidePLL' depends on axioms: [propext, Quot.sound] -/
                                                       (saturate:2523–2525)
```

Had the chain been stated with `∨`, the same definition would have
required `Or.elim` into `Type`, i.e. choice, and the pin would read
`[propext, Classical.choice, Quot.sound]`.  A decidability result whose
witness is produced by choice decides nothing: the standing rule in this
development is that a `Decidable` hypothesis must not be discharged by
`Classical.choice`; decidability *follows from* completeness, it is
never assumed.

### D.3 What an inhabitant lets a program do

An inhabitant of `A ⊕' B` is a *tagged* value, `PSum.inl` or `PSum.inr`,
and the tag is data.  A program may branch on it in any context,
including one that returns a term.  Three uses in the chain:

1. `decidePLL` (above): the tag becomes the `Decidable` verdict.
2. `dichotomyW` (search:829–840), whose type is

       DisprovableW G ⊕' GbuRC G [] G

   Note the right side: not `Nonempty (GbuRC G [] G)` but the derivation
   itself.  So one layer down, the positive side really does carry the
   proof term, and any consumer (a checker, a printer, a
   proof-transformation) can take it apart.
3. `totalityW` (search:231) returns
   `RefAt true (Z :: R₀) Ψ X ⊕' GbuIC G Ψ X`, and the caller *matches on
   it* (search:408–409) to decide whether to apply `L⊃ᵢ`.  With `∨` the
   corner could not be closed at all: the derivation on the right is
   what `.limpLI` is applied to (search:444–445).

### D.4 The asymmetry at the crown — RESOLVED

The stage-1 plan flagged an asymmetry as UNCERTAIN: `decideGbuW G :
ProvableGbuC G ⊕' DisprovableW G` has `Nonempty` on the left and `∃` on
the right, so both sides are squashed and the `⊕'` carries exactly one
bit.  `decideGbuW_of` does the squashing explicitly:

```lean
match dichotomyW (wsat_of_closed db h2) … with
| .inl hdis => .inr hdis
| .inr d => .inl ⟨d⟩                                  (closure:1092–1096)
```

and the `⟨d⟩` discards `d`.  **This is now resolved, and it was small.**
Matthew's observation (2026-09-02) that the bare calculi belong on both
sides produced

```lean
def decideGbuWData (G : Form) :
    GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G) :=
  decideOfStore (closureDB G) (closureDB_closed G)     (saturate:2485–2487)

/-- info: 'FRJ.Gbu.W.decideGbuWData' depends on axioms: [propext, Quot.sound] -/
                                                       (saturate:2527–2529)
```

Note that this is a plain `⊕` (`Sum`), not `⊕'`: both sides are now
Types, so `PSum` is not needed.

**How it was obtained, and why nothing had to change.**  The truncation
was an artefact of the abstract `WSaturated` interface, which stores
derivability as a `Prop` (`WDerivable`, dichotomy:63–65), and NOT of the
mathematics.  At the instantiation the rows already carry their
disproofs as data (`WRow`, closure:952–954).  So the negative side is
recovered by a Type-valued root scan over the instantiated store, made
independently of the abstract interface:

```lean
def rootDisproof? {G : Form} : List (WRow G) → Option (Σ' t Γ, FRJWr G t Γ G)
  | [] => none
  | ⟨.reg t Γ C, d⟩ :: rest =>
      if h : C = G then some ⟨t, Γ, h ▸ d⟩ else rootDisproof? rest
  | ⟨.irr _ _ _, _⟩ :: rest => rootDisproof? rest      (saturate:2444–2448)

theorem rootDisproof?_none : ∀ {db : List (WRow G)},
    rootDisproof? db = none → ¬ WEvalR (· ∈ db.map (·.s)) [] G
                                                       (saturate:2451–2468)

def decideOfStore (db : List (WRow G)) (hcl : DBClosed G db) :
    GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G) :=
  match h : rootDisproof? db with
  | some d => .inr d
  | none =>
      .inl (searchW (wsat_of_closed db (tC_of_closed hcl))
        (fun Ω C => decWEvalI (db.map (·.s)) Ω C)
        (true, ([] : List Form), G) (fun _ h => absurd h List.not_mem_nil)
        (sfR_self G) (rootDisproof?_none h))           (saturate:2472–2480)
```

Three points the explainer should draw out.

- `rootDisproof?_none` is what replaces `dichotomyW`'s
  `decR : Decidable (WEvalR D [] G)`: the *absence* of a root row is
  turned directly into the negative hypothesis `searchW` needs, so the
  scan is both the decision and its certificate.
- The abstract `Prop`-valued interface is untouched.  `searchW`,
  `dichotomyW`, `WSaturated`, `WSearchOk`: none changed.
  `decideOfStore` takes the store abstractly (`db` a parameter, not
  `closureDB G`) so elaboration never unfolds the saturation.
- `decideGbuW` and `decideGbuWData` are two independent routes through
  the same closed store.  Neither is defined from the other; both are
  pinned `[propext, Quot.sound]`.

### D.5 Relation to `Decidable`

`Decidable p` is, up to constructor names, `p ⊕' ¬ p`.  The dichotomy
replaces the negative side `¬ ProvableGbuC G` with a *positive
certificate of a different calculus*, `DisprovableW G`.  So

    decideGbuW G : ProvableGbuC G ⊕' DisprovableW G

is "`Decidable (ProvableGbuC G)` with a witness on the false side".  The
two halves that make this a decision procedure are proved separately.

- **Exhaustiveness** (no goal escapes both) is the constructive content
  of `decideGbuW` itself, i.e. FRJW completeness *and* Gbu◯ completeness
  simultaneously (`frjw_complete` saturate:2402–2404, `gbuw_complete`
  saturate:2409–2411).  This is what the chain is for.
- **Exclusivity** (no goal satisfies both) is a *theorem*, not part of
  the `PSum`: `PSum` permits both sides to be inhabited.  It comes from
  the two soundness results,

      not_disprovableW_of_provableGbuC (h : ProvableGbuC G) : ¬ DisprovableW G
      not_provableGbuC_of_disprovableW (h : DisprovableW G) : ¬ ProvableGbuC G
                                            (exclusion:26–33)

  each of which is one line
  (`fun hd => FRJ.soundnessW hd (pll_of_provableGbuC h)`).  One forces
  PLL-validity, the other refutes it.

Composing the two gives the semantic reading

    provableGbuC_iff_pll     : ProvableGbuC G ↔ PLL G      (saturate:2414–2417)
    disprovableW_iff_not_pll : DisprovableW G ↔ ¬ PLL G    (saturate:2420–2423)

so the decision object is sound and complete in both directions
simultaneously, and `decidePLL` reads it off.

### D.6 What is new here

Two things, stated conservatively.

1. **The pair, mechanised, for a modal logic.**  The duality between a
   backtrack-free proof calculus and a forward refutation calculus is
   due to Fiorentini and Ferrari, for intuitionistic propositional
   logic: *Duality between unprovability and provability in forward
   proof-search for Intuitionistic Propositional Logic*, ACM TOCL 21(3),
   2020, the repository's source of truth for FRJ(G) and for `Gbu`
   (`docs/frj-fidelity.md:3–6`; `docs/calculus-map.md:187` records
   "`Gbu` is Fiorentini & Ferrari §5").  What is ours is the
   `◯`-extension on both sides, including the licenced `|◯C|` adaptation
   of `L⊃ᵢ` (`wip/gbu_circ.lean:1316–1344`, the docstring and the
   `limpLI` constructor) and every proof in the chain above.  I am
   confident of that citation and of no other; in
   particular I make **no** claim about the content of any unread paper,
   and repository policy forbids attributing anything to one.
2. **The single object.**  Packaging the two calculi into one
   `⊕'`-valued function, made exhaustive by construction and exclusive
   by the two soundness theorems, is what turns "two completeness
   theorems" into "one decision procedure" without leaving the
   constructive fragment.  The evidence that this is not merely cosmetic
   is the axiom pin, `[propext, Quot.sound]` throughout with no
   `Classical.choice`, on a result (decidability of PLL) normally
   obtained through the finite model property.  The independent route to
   Gbu◯ completeness through the LJF◯ translation (`gbuC_complete`,
   `wip/gbu_ljfo.lean:816`, same pin) still stands, and its independence
   is itself evidence; the compaction has *not* retired it
   (`docs/frjw-compaction.md:50–52`).

---

## PART E — The stage-4 brief: the proof-strategy narrative

This is the priority.  What follows is the spine of an explanation of
the proof STRATEGY, in the order a reader should meet it, with, for each
item, the proof states or `#eval` previews from Part B to show, the
theorem statements to display as formulas, and an effort estimate.

The audience assumption: a reader who knows sequent calculus and
intuitionistic logic, has not read the Fiorentini–Ferrari paper, and
wants to know *why the construction works*, not *how the Lean is
arranged*.  Every item should be readable without the file open; the
`file:line` citations are for the reader who then wants to check.

### E.i The two calculi and the cell dichotomy statement

**What to say.**  There are two calculi over the same signed
subformula language of a fixed goal `G`.  `Gbu◯` is a two-judgment
*proof* calculus: `Ψ ⇒g C` regular, `Ψ →g C` irregular (right-focused).
`FRJW` is a two-stratum *disproof* calculus: `FRJWr G t Γ C` regular
(tagged) and `FRJWi G St Th C` irregular (two zones).  An object of
`FRJWr`/`FRJWi` is a DISPROOF; nothing in it proves anything.

The theorem being aimed at is not "either a proof or a refutation
exists" but the stronger, per-cell, Type-valued statement: *at any cell
well-formed for `G`, given that the store of disproofs does not answer
the cell's query, one can BUILD the `Gbu◯` derivation.*  Display:

    WSearchOk G D (true, Ψ, C)  =
      (∀ X ∈ Ψ, X ∈ Sf^L G) → C ∈ Sf^R G →
      ¬ WEvalR D Ψ C → GbuRC G Ψ C

    WSearchOk G D (false, Ω, C) =
      (∀ X ∈ Ω, X ∈ Sf^L G) →
      (C.isCirc = false → ∀ X ∈ Ω, X ∈ Ĝ) → C ∈ Sf^R G →
      WUnrefutedBelow G D Ω C → GbuIC G Ω C

**Why the two clauses differ** is the first real content: in irregular
mode the bare negative fact `¬ WEvalI D Ω C` is *vacuous* at a context
outside `Ĝ` (every irregular row has `Ĝ`-bounded zones, so nothing could
answer), which is why `WUnrefutedBelow` (dichotomy:104–108) carries an
`Ĝ`-bounded ancestor `Ω₀` alongside.  A reader who does not meet this in
the first section will misread every irregular step afterwards.

**Show**: the two clauses as displayed formulas; the `WSeq` and
`WSaturated` definitions (dichotomy:58–80); the S0/S1/S2 proof state
from §B.3 (the `show` at search:288–289 is literally the irregular
clause, which makes the point concrete).

**Effort**: 1 h.

### E.ii Why naive search has no measure, and what `wgC` pays for

**What to say.**  Backward `Gbu◯` search does not terminate on any
measure of the sequent, and this is a theorem, not a difficulty:

    not_wf_stepC (G : Form) :
      ¬ WellFounded (fun p q : Bool × List Form × Form => StepC G p q)
                                                (wip/gbu_measure.lean:87–93)

    no_measure_stepC (G : Form) {β : Type} (m : cell → β) {lt : β → β → Prop}
      (hwf : WellFounded lt) (hm : ∀ p q, StepC G p q → lt (m p) (m q)) : False
                                                (wip/gbu_measure.lean:103–107)

pinned "does not depend on any axioms" (gbu_measure.lean:498–500).  The
witness is a two-cycle: with `Γ = ◯Z ⊃ B, Ψ`, the step `L⊃` on `◯Z ⊃ B`
takes `Γ ⇒g Z` to `Γ →g ◯Z`, and `R◯ₙᵢ` takes `Γ →g ◯Z` back to
`Γ ⇒g Z`.  So no reordering or refinement of the weight can work, and
the search must consult something the sequent does not carry.

What it consults is the *store of disproofs*.  The measure then only has
to cover the steps the search actually takes, which are the ones
licensed by "the store has no row here", and those do fall:

    wgC G reg Ψ C = ( unclosed G Ψ , tpC reg C , seqSize Ψ C )

    unclosed G Ψ = |Sf^L(G) ∖ Cl(Ψ)|
    tpC reg C    = 2 if regular; else 1 if ◯ occurs in C; else 0
    seqSize Ψ C  = Σ_{X ∈ Ψ} |X| + |C|

with the three-part story: component 1 pays for the two rules that GROW
the context (`R⊃ₙ`, `R⊃ₙᵢ`), which nothing else can pay for; component 2
pays for release from regular to irregular mode; component 3 pays for
every structural descent.  Then the sentence that makes it land: *the
three components are in that order because `R⊃ₙ` grows the context, so
size cannot pay, and mode release does not change the context, so
`unclosed` stays level and `tpC` can pay.*

**Show**: the `not_wf_stepC` two-cycle as a two-line displayed
derivation sketch; the `wgC` definition; the §B.2 trace table for `G₁`
with the "operative drop" column; and the §A.1 payment table (3 sites /
4 sites / 19 sites).  The trace makes the abstract measure concrete in
one page.

**Effort**: 2 h, plus §B.2's trace file as a dependency.

### E.iii How the two calculi are made to MEET at every cell

**This is the heart, and it is the item most likely to be
under-explained.**  What to say:

At every cell the searcher asks the store a question.  If the answer is
"no", it takes a `Gbu◯` step and recurses.  For that to be sound, one
needs, for each `Gbu◯` rule, a lemma saying *if the store answers the
premise, it answers the conclusion*.  Contrapositively: the conclusion
being unanswered makes the premise unanswered, which is the hypothesis
the recursive call needs.  Displayed, the shape of a whole rule family:

    gbuInv5 : A⊃B ∈ Sf^R(G) → Cl(Ψ) ∋ A → WEvalR D Ψ B → WEvalR D Ψ (A⊃B)
    gbuInv6 : A⊃B ∈ Sf^R(G) → WEvalR D (A::Ψ) B → WEvalR D Ψ (A⊃B)

and its two consuming sites, the `R⊃` and `R⊃ₙ` branches of the regular
implication case (search:664–679).

Each of these lemmas is proved *once*, and each is a small, uniform
argument: `WSaturated.1` extracts the premise row's DISPROOF, an FRJW
constructor is applied to it, and `WSaturated.2` puts the result back in
the store.  Quote one in full (`gbuInv5`, db:116–126) so the reader sees
the whole move; it is eleven lines.

Then present **the bank as a table**, one row per `Gbu◯` rule, three
columns: rule, inversion lemma, consuming site.  That table is the
proof strategy at cell level: it says that `searchW` is not a search but
a *rule-by-rule walk*, and that the walk is exhaustive because the bank
is.  The table is §C.11; it fits on a page.

Two clauses of the bank do not fit the pattern and should be treated as
the interesting exceptions.

- `evalI_axI_gHat` (circdb:34–50) is the *axiom* clause and reads the
  other way: an atom NOT in the context is always refuted, because the
  `Ax^I` row covers it.  It is what makes the atom case of `totalityW`
  a dilemma rather than a gap.
- The `gbuSucc*` family (circdb:54, 156, 385) is the *success* clause: at
  a critical cell where every context implication's antecedent is
  refuted, the store gets the conclusion row directly, by the join
  rules.  These are the largest proofs in the bank (100 lines each) and
  the place where the arbitrary-arity joins are used.

**Show**: the bank table; `gbuInv5` quoted in full; the S8b proof state
at the `⊃` case (search:662–679) showing both branches side by side; and
one `gbuSucc*` statement displayed but not proved.

**Effort**: 3–4 h.  This is the item to commission first if only one is
commissioned.

### E.iv The corner and `totalityW`

**What to say.**  One cell shape resists the walk: irregular, goal `◯Z`,
context inside `Ĝ_at ∪ Ĝ_imp` (atoms and implications only, no modal
member), and `Z` refuted.  There is no `Gbu◯` rule to apply to the goal,
and the only route is modus ponens (`L⊃ᵢ`) on a context implication,
which needs the ANTECEDENT derived first.  The antecedent may be
arbitrarily large relative to the goal, so no size argument reaches it.

The escape is a theorem found by trying to build a counterexample and
failing the same way every time:

    totalityW : at a critical cell, for every X ∈ Sf^R(G),
        RefAt true (Z :: R₀) Ψ X  ⊕'  GbuIC G Ψ X

with `R₀` the decidable list of ALL refuted `Sf^R`-forms
(search:370–371).  Every right-subformula is either refutable at that
cell or derivable at it.  The proof is STRUCTURAL on `X`, because
`RefAt`'s clauses (RefAt.lean:36–48) and the irregular introduction
rules of `Gbu◯` are De Morgan duals:

    ∧    : one side refuted            against   both sides derivable
    ∨    : both sides refuted          against   one side derivable
    ◯    : body refuted (cone)         against   body derivable (R◯ᵢ)
    ⊃    : Cl-antecedent + refuted body against   R⊃ / R⊃ₙ
    atom : absent from Ψ (refuted)     against   present in Ψ (ax)

Each case totalises: a child that fails one side supplies the other.

The one non-structural case is the `¬Clo`-antecedent implication
(search:261–263): it is either refuted as a form (`gbuInv9` reflects a
regular `B`-row into an irregular `A⊃B`-row, so `.ups` catches it) or its
`¬ WEvalR` precondition is exactly what the regular stratum needs, and
*that* recursion drops `unclosed`.  So it is handed back to the caller
as a callback (`reccall`), paid for by the enclosing well-founded
recursion.

**The two-level diagram is the single most valuable picture in the
explainer**: a box for `searchW` (well-founded on `wgC`) containing a box
for `totalityW` (structural on `Form`), with one arrow leaving the inner
box and re-entering the outer one, labelled "`reccall`, paid by
component 1".  Draw it once and refer back to it.

Then the corner's own conclusion: the antecedent that failed the
certificate test cannot be refuted (`.ups` would have passed it), so
totality hands over its DERIVATION and `L⊃ᵢ` steps through the
implication, with the consequent recursion paid by `seqSize`
(search:424–445).

**Show**: the two-level diagram; the `totalityW` type quoted in full;
the atom case (search:233–239) quoted in full, because it is four lines
and it IS the dilemma; the De Morgan table above; the free-standing
corner cell of §B.5 as a worked walk; and the S5a-ii proof state.

**Effort**: 3 h, plus §B.5's corner-cell verification.

### E.v The closure stage: T-A, T-B, T-C, `DBClosed`, and saturation

**What to say.**  Everything so far is parameterised by an abstract
saturated store.  The remaining obligation is to build one, per `G`, and
it is a completeness-shaped argument of its own.

The route: take `D := (· ∈ db)` for a COMPUTED list `db` of rows, each
row carrying its disproof as data (`WRow`, closure:952–954).  Then
`WSaturated.1` is trivial and the whole weight is `WSaturated.2`: every
derivable row is subsumed by a stored one.  That is proved by induction
on the disproof (T-C, `tCr`/`tCi`), against a closedness contract:

    DBClosed G db  —  21 clauses, one per FRJW rule: the rule fired at
                      STORED premise sequents, with its canonical kept
                      chain and canonical conclusion context, has a
                      stored subsumer.                (closure:1179–1339)

    tC_of_closed : DBClosed G db →
      ∀ s, WDerivable G s → ∃ r ∈ db, WSubsumes s r.s (closure:1681–1684)

Each of the 21 cases does the same three things (recurse, extract shape,
refire at the subsumers' shapes), and the reason refiring is sound is
T-B: the rule applied to stored subsumers of its premises yields a
conclusion subsuming the original's.  Two subsidiary points deserve
display.

- **T-A** (closure:67–82) is what makes T-B work for the join rules.  A
  join retains context implications as a `KeptChain` (RefAt.lean:144–150),
  each link certified over the base plus *the earlier links only*.  Under
  premise swap the zones grow, so the old chain must be relocated inside
  the new greedy fixpoint `keptOf`; T-A does that, and its
  parameter-growth form is why one lemma serves both purposes.
- **The order-sensitivity worry and its dissolution** (§A.5) should be
  told with T-A, not after it.

Then saturation.  `stepAll` fires all 19 emitters at every stored premise
combination (saturate:1206–1213); `sat` iterates with fuel
(saturate:1304–1308); rows are keyed by a *canonical* sequent
(`canonSeq`, saturate:109–111) so that `≐`-equal contexts get EQUAL keys;
the store is key-nodup and its keys live in a finite universe
(`univList`, saturate:114–120), so `(univList G).length + 1` rounds
reach a fixpoint (`sat_fixed`, saturate:1331–1334).  Display the
pigeonhole as four lines (§A.4) and the definition

    closureDB G = sat G ((univList G).length + 1) []    (saturate:1364–1365)
    closureDB_closed G : DBClosed G (closureDB G)       (saturate:2354–2378)

One paragraph is owed to the choice hygiene: `dedupF` (saturate:76–78)
exists because mathlib's `List.mem_dedup` carries `Classical.choice`,
and `decForallFin`/`decExistsFin` (saturate:688–711) exist because
mathlib's `Fin` order instances do.  A decidability theorem whose
witness used choice would decide nothing.

**Show**: the `DBClosed` clause count against the `tCr`/`tCi` case count
(21 = 13 + 8); one T-C case quoted in full (`impIn`, closure:1472–1478);
the T-A statement; the four pigeonhole lemmas; and the `#print axioms`
line for `closureDB_closed`.

**Effort**: 3–4 h.

### E.vi The crown, and what the axiom pin certifies

**What to say.**  Composing the closure stage with the cell dichotomy
gives, for every PLL formula `G`, a single object; and reading it two
ways gives two completeness theorems that were never proved separately:

    decideGbuW G : ProvableGbuC G ⊕' DisprovableW G     (saturate:2387–2388)

    frjw_complete : ¬ ProvableGbuC G → DisprovableW G   (saturate:2402–2404)
    gbuw_complete : ¬ DisprovableW G → ProvableGbuC G   (saturate:2409–2411)

    provableGbuC_iff_pll     : ProvableGbuC G ↔ PLL G   (saturate:2414–2417)
    disprovableW_iff_not_pll : DisprovableW G ↔ ¬ PLL G (saturate:2420–2423)

    decidePLL G : Decidable (PLL G)                     (saturate:2428–2431)

    decideGbuWData G : GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)
                                                        (saturate:2485–2487)

**What the pin certifies.**  Every one of these is `#guard_msgs`-pinned
`[propext, Quot.sound]` (saturate:2491–2529).  Say plainly what that
does and does not mean: it means the kernel checked the term and its
transitive dependencies use no axioms beyond propositional extensionality
and the quotient soundness axiom; in particular no `Classical.choice`,
so the `Decidable` instance is a real algorithm rather than an appeal to
excluded middle.  It does not mean the *statements* are the right ones;
that is what `docs/frj-fidelity.md` and the calculus map are for.
`#print axioms` (the `collectAxioms` oracle) is the only sound checker
here, and `native_decide` would taint.

Say also that exclusivity is a separate theorem (`PSum` permits both
sides to be inhabited), one line each way, from the two soundness
results (exclusion:26–33), and that it is what upgrades the dichotomy to
the biconditionals.

**Show**: the seven statements above as displayed formulas; the pin
block; the `decideGbuWData` smoke line
(`atom: decideGbuWData=disproof(tag=chain (atom "p"), |Γ|=0)`), which is
the one place a reader can see both calculi come out as objects.

**Effort**: 1–2 h.

### E.vii What is NOT claimed

**What to say**, plainly and without hedging in either direction.

1. **This is a proof object, not a practical procedure.**  `decidePLL`
   computes, and `wip/decidepll_smoke_out.txt` records 7/7 PASS twice
   over on five formulas with `|Sf^R G| ≤ 3`.  It computes because
   `closureDB G` saturates the *entire* wellformed universe of `G`
   before any cell is searched, and that universe is exponential in
   `|Ĝ|`.  Anything larger is out of interpreter reach.  A timeout is a
   FLAG, never a verdict.  **UNCERTAIN**: where the wall is; nobody has
   measured it.
2. **No complexity claim of any kind is made**, upper or lower.
3. **The `#eval` evidence taints nothing and proves nothing.**  The
   `#guard_msgs` pins are the kernel gates; the smoke file is
   engineering evidence, explicitly labelled untrusted in its own header
   (`wip/decidepll_smoke.lean:1–12`).
4. **PLL decidability is not new.**  What is new here is the *route*: a
   constructive, choice-free decision object that returns a proof or a
   disproof, rather than a model-theoretic argument through the finite
   model property.  The explainer should say which of the two facts is
   being claimed.
5. **The `◯`-extension is ours; the underlying duality is not.**  See
   §D.6.  Nothing is attributed to any paper the repository has not
   read.
6. **Two GBUW completeness routes coexist deliberately.**  The
   dichotomy route (`gbuw_complete`) and the LJF◯ translation route
   (`gbuC_complete`, `wip/gbu_ljfo.lean:816`) are independent, and that
   independence is evidence, not redundancy to be tidied away
   (`docs/frjw-compaction.md:50–52`).

**Show**: the smoke output file verbatim (it is 19 lines, including the
gate-watch line and the stage-3 regression block, and it is the honest
picture in one screen).

**Effort**: 45 min.

### E.viii Commissioning menu for Part E

| item | deliverable | est. effort | depends on |
|---|---|---|---|
| **E.i** | the two calculi and the cell statement | 1 h | — |
| **E.ii** | no naive measure; what `wgC` pays for | 2 h | B.2 trace |
| **E.iii** | **the bank: how the calculi meet** | 3–4 h | C.11 table (written) |
| **E.iv** | the corner, `totalityW`, the two-level diagram | 3 h | B.5 corner cell |
| **E.v** | the closure stage and saturation | 3–4 h | — |
| **E.vi** | the crown and the pin | 1–2 h | — |
| **E.vii** | what is not claimed | 45 min | — |

Recommended order if commissioned piecemeal: **E.iii first** (it is the
strategy, and it is the item a reader will remember), then E.iv, then
E.ii, then E.i as the frame around them, then E.v–E.vii.  E.iii and E.iv
together are the explanation; the rest is context and honesty.

Total for Part E as a whole: **14–17 h**, plus the Part B trace work it
depends on.

---

## Commissioning menu (whole document)

| part | deliverable | est. effort |
|---|---|---|
| **A** | the recursion reference: §A.1–A.7 written out with the quoted types, the measure table and the two-level diagram | 4–5 h |
| **B.2** | `#eval`-checked cell/measure trace for `G₁` and `G₂`, as a new `wip/frjw_trace.lean` plus the table | 2–3 h |
| **B.2+** | the same for the free-standing corner cell, including checking it behaves as claimed | 2 h |
| **B.3** | `show`-assertions at the stage boundaries in a shadow copy, one build | 3–4 h + build |
| **C.10** | the dead-declaration sweep (`wgTpLt`, `tpC_free_lt_circ`, `IHW`) | 20 min + one build |
| **C.2–C.6** | the compaction proper (≈ 270 lines), pins re-verified, smoke cells re-run | 4–6 h + builds |
| **C.11** | the bank table, as a standalone page | 1 h |
| **D** | already written above; needs only trimming into the explainer | 30 min |
| **E** | the proof-strategy narrative, seven items | 14–17 h |

Ordering constraints:

- **C.10 should run first**, before any line numbers are quoted in
  prose; it is 20 minutes and it removes the last stage-3 residue.
- **B.3 should follow C.2–C.6** if the compaction is commissioned;
  otherwise the stage line numbers move under it.
- **E.iii depends on C.11**, which is written above and needs only
  formatting.
- Nothing else is blocked on anything else.
