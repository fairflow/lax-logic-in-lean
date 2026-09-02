# The Gbu◯ / FRJW decision procedure, explained

*Stage 4 of the FRJW campaign.  Written 2026-09-02 for Matthew's own
use, in full detail, from the checked-in sources at commit `b2f2525`
on `frjw-dev`.  It follows the reading order Matthew set: the calculi
first, then what a cell and a motive are, then the proof-state trace
of `searchW` (the B.3 item of the stage-4 brief), then how the two
calculi meet at every cell (E.iii), then the corner and `totalityW`
(E.iv), then two concrete runs (a proof and a disproof) correlated
with the proof states, then the complexity comparison with the
Fiorentini–Ferrari original.  The brief itself is
`docs/frjw-recursion-explainer-plan.md`; the compaction record is
`docs/frjw-compaction.md`.*

**Provenance.**  Every `file:line` is at `b2f2525`.  Every infoview
snapshot in §4 was produced by the method of `docs/annotated/README.md`:
the repository file was copied verbatim to a scratch location outside
the tree, `trace_state` was inserted at the chosen points, the copy was
compiled with `lake env lean` from the package root, and the blocks were
transcribed unedited; the anchors were then re-derived against the
checked-in file.  Nothing in the repository was modified to produce
them and nothing about what is proved changed.  The `#guard_msgs`
pins of every result cited are `[propext, Quot.sound]` unless said
otherwise; `#print axioms` (the `collectAxioms` oracle) is the only
checker recognised here.

**File map (added 2026-09-02, evening).**  After this document was
written the chain was promoted out of `wip/` and the zone binders were
renamed to Greek (`docs/notation.md`).  Every anchor below still
resolves at `b2f2525` (`git show b2f2525:wip/gbu_frjw_search.lean`);
the current locations are `wip/gbu_frjw_{dichotomy, db, circdb, corner,
search, closure, exclusion, saturate}.lean` → `FRJ/Gbu/W/{Dichotomy,
DB, CircDB, Corner, Search, Closure, Exclusion, Saturate}.lean`,
`wip/gbu{,_db,_search,_measure,_circ}.lean` → `FRJ/Gbu/{Base, DB,
Search, Measure, Circ}.lean`, and the §10 modules `wip/gbu_laxnd.lean`,
`wip/gbu_frjw_laxnd.lean` → `FRJ/Gbu/LaxND.lean`, `FRJ/Gbu/W/LaxND.lean`.
In the snapshots of §4 and §7 the binders `St`/`Th`/`stab`/`th`/`Lam`
now read `Ξ`/`Θ`/`Ξs`/`Θs`/`Λ` in the sources; the transcripts are left
as taken.  The full table is in `docs/frjw-compaction.md`,
"Promotion".

**Register.**  An object of `FRJWr`/`FRJWi` is a DISPROOF; "proof" and
"derivation" are reserved for `Gbu◯` (and for `LaxND`, `G4c`, `SC`
elsewhere in the repository).  PROVED, REFUTED and OPEN are kept
distinct; a claim I could not verify is marked UNCERTAIN with what
would settle it.  The duality being mechanised is due to Fiorentini
and Ferrari, *Duality between unprovability and provability in forward
proof-search for Intuitionistic Propositional Logic*, ACM TOCL 21(3),
2020; the `◯`-extension on both sides is ours.  Nothing is attributed
to any other paper.

---

## 1. The two calculi

Both calculi live over the signed subformulas of one fixed goal
formula `G`, and everything else in this document is relative to that
`G`.

### 1.1 Formulas, the signed subformula sets, and the `Ĝ` zones

`Form` (`FRJ/Basic.lean:40–46`) is the propositional language with
`⊥`, atoms, `∧`, `∨`, `⊃`, and the lax modality `◯`.  The paper's
`Sf^R(G)` and `Sf^L(G)`, the right-signed and left-signed subformulas
of `G`, are computed (`sfR`, `sfL`, `FRJ/Basic.lean:632–635`) and
characterised by the paper's four clauses (`sfPos_closed`,
`sfR_self`, `sfR_and`, `sfR_or`, `sfL_and`, `sfL_or`, `sfR_imp`,
`sfL_imp`, all PROVED; `docs/frj-fidelity.md` §2 table).  For
`G = p ⊃ ◯p`, for instance,

    sfR G = [p ⊃ ◯p, ◯p, p]        sfL G = [p]

(the antecedent of a right-signed implication is left-signed, its
consequent right-signed; `◯` preserves sign).

The finite universe every context lives in is

    Ĝ_at  = Sf^L(G) ∩ atoms            (gAt,   FRJ/Basic.lean:1024)
    Ĝ_imp = Sf^L(G) ∩ implications     (gImp,  FRJ/Basic.lean:1027)
    Ĝ_◯   = Sf^L(G) ∩ ◯-formulas       (gCirc, FRJ/Basic.lean:1031)
    Ĝ     = Ĝ_at ++ Ĝ_imp ++ Ĝ_◯       (gHat,  FRJ/Basic.lean:1046)

The third zone `Ĝ_◯` is the modal extension's addition to the paper's
`Ĝ = Ĝ_at ∪ Ĝ_imp`.  A context member that is not in `Ĝ` is `⊥`, a
conjunction or a disjunction; those are exactly the formulas the
invertible left rules decompose.

### 1.2 The closure `Cl(Γ)`

The paper's closure of a context, written `Cl(Γ)` and pronounced "the
formulas Γ trivially proves", is the inductive predicate

```lean
inductive Clo (Γ : List Form) : Form → Prop          -- FRJ/Basic.lean:1118–1127
  | base {C : Form} : C ∈ Γ → Clo Γ C
  | and  {X Y : Form} : Clo Γ X → Clo Γ Y → Clo Γ (.and X Y)
  | orR  {A X : Form} : Clo Γ X → Clo Γ (.or A X)
  | orL  {A X : Form} : Clo Γ X → Clo Γ (.or X A)
  | imp  {A X : Form} : Clo Γ X → Clo Γ (.imp A X)
  | circ {X : Form} : Clo Γ X → Clo Γ (.circ X)      -- the modal clause: ours
```

with the decision procedure `cloB` (`FRJ/Basic.lean:1228–1234`) and
`cloB_iff : cloB Γ X = true ↔ Clo Γ X`.  The `circ` clause is sound by
the unit of the modality (`X` proves `◯X`).  `Cl` is what the side
conditions `A ∈ Cl(Γ)` / `A ∉ Cl(Γ)` of the two `R⊃` rules consult, and
the measure component `unclosed G Ψ = |Sf^L(G) ∖ Cl(Ψ)|`
(`wip/gbu.lean:262–263`) counts how much of the universe the context
has not yet captured.

### 1.3 Contexts are sets

Contexts are `List Form`, but every rule that focuses on a member
states its conclusion context up to membership equality,

    Γ ≐ Δ   :=   ∀ x, x ∈ Γ ↔ x ∈ Δ                  (CtxEq, FRJ/Basic.lean:1059–1061)

so `Γ ≐ A :: Ψ` reads "Γ is `A, Ψ` as a set".  This is how order and
multiplicity are made irrelevant without quotienting: every
constructor whose conclusion has a computed context carries an `hΓ : Γ'
≐ …` hypothesis, and `Γ'` itself is a variable (`docs/frj-fidelity.md`
divergence 4, and the no-green-slime constraint of the FRJ handoff).

### 1.4 `Gbu◯(G)`: the proof calculus

Two judgments, both indexed by the fixed `G` (`wip/gbu_circ.lean:
1266–1365`, mutual, Type-valued):

    GbuRC G Ψ C      written   Ψ ⇒g C      regular sequents
    GbuIC G Ψ C      written   Ψ →g C      irregular sequents

The intended reading, from the paper's GBU(G) (its §5): a regular
sequent is one at which the searcher may apply left rules to the
context; an irregular sequent is one whose context is *frozen*, so
that only right rules apply, which is what makes the search
backtrack-free.  Irregular sequents arise as the premises of `R∨` and
as the left premise of `L⊃`.  In `Gbu◯` the modality forces one
relaxation: at an irregular sequent whose goal is `◯`-shaped, the
left rules are admitted after all (the `…ᵢ` rules below), because
`Ω →g ◯q` can need modus ponens on an implication of `Ω` and no `◯`
rule can substitute for it (`not_gbuR_omegaNI`, kernel-checked, cited
in the docstring at `wip/gbu_circ.lean:1316–1319`).

Every left rule's conclusion context is `Γ` with `Γ ≐ X :: Ψ` for the
principal formula `X`; I write the conclusion as `X, Ψ` below.  Side
conditions in brackets.

**Regular rules** (`GbuRC`, twelve constructors):

```
 ───────────── ax  [A ∈ Γ]            ───────────── L⊥  [⊥ ∈ Γ]
   Γ ⇒g A                               Γ ⇒g C

   A, B, Ψ ⇒g C                        Γ ⇒g A     Γ ⇒g B
 ─────────────── L∧                  ───────────────────── R∧
   A ∧ B, Ψ ⇒g C                         Γ ⇒g A ∧ B

   A, Ψ ⇒g C     B, Ψ ⇒g C               Γ →g Cₖ
 ────────────────────────── L∨        ───────────── R∨ₖ   (k = 1, 2)
       A ∨ B, Ψ ⇒g C                    Γ ⇒g C₁ ∨ C₂

   A ⊃ B, Ψ →g A     B, Ψ ⇒g C
 ────────────────────────────── L⊃
        A ⊃ B, Ψ ⇒g C

     Γ ⇒g B                              A, Γ ⇒g B
 ─────────────── R⊃  [A ∈ Cl(Γ)]      ─────────────── R⊃ₙ  [A ∉ Cl(Γ)]
   Γ ⇒g A ⊃ B                            Γ ⇒g A ⊃ B

   Z, Ψ ⇒g ◯C                             Γ →g Z
 ─────────────── L◯  [◯Z ∈ Sf^L(G)]   ───────────── R◯  [◯Z ∈ Sf^R(G)]
   ◯Z, Ψ ⇒g ◯C                            Γ ⇒g ◯Z
```

Lean names: `ax lbot landL randR lorL rorR1 rorR2 limpL rimpI rimpNI
lcirc rcirc`.  Note the mode changes: `R∨ₖ`, `L⊃`'s left premise and
`R◯` all have IRREGULAR premises.

**Irregular rules** (`GbuIC`, twelve constructors):

```
 ───────────── ax  [A ∈ Γ]
   Γ →g A

   Γ →g A     Γ →g B                      Γ →g Cₖ
 ───────────────────── R∧ᵢ             ───────────── R∨ₖᵢ
     Γ →g A ∧ B                          Γ →g C₁ ∨ C₂

     Γ →g B                              A, Γ ⇒g B
 ─────────────── R⊃ᵢ  [A ∈ Cl(Γ)]     ─────────────── R⊃ₙᵢ  [A ∉ Cl(Γ)]   (premise REGULAR)
   Γ →g A ⊃ B                            Γ →g A ⊃ B

     Γ →g Z
 ───────────── R◯ᵢ  [◯Z ∈ Sf^R(G)]     (premise IRREGULAR: focus is not released)
   Γ →g ◯Z

   Z, Ψ →g ◯C                           A ⊃ B, Ψ →g A     B, Ψ →g ◯C
 ─────────────── L◯ᵢ  [◯Z ∈ Sf^L(G)]  ──────────────────────────────── L⊃ᵢ  [◯C ∈ Sf^R(G); A ◯-free or A ∈ Sf^R(G)]
   ◯Z, Ψ →g ◯C                                  A ⊃ B, Ψ →g ◯C

                                        A, B, Ψ →g ◯C              A, Ψ →g ◯C     B, Ψ →g ◯C
 ─────────────── L⊥ᵢ  [◯C ∈ Sf^R(G)]  ─────────────── L∧ᵢ         ────────────────────────── L∨ᵢ
   ⊥, Ψ →g ◯C                           A ∧ B, Ψ →g ◯C                  A ∨ B, Ψ →g ◯C
```

Lean names: `ax randI rorI1 rorI2 rimpII rimpNII rcircI lcircI limpLI
lbotI landLI lorLI`.  The six left rules at a `◯`-goal (`L◯ᵢ L⊃ᵢ L⊥ᵢ
L∧ᵢ L∨ᵢ`, plus `L◯` on the regular side) and the two `R◯` rules are the
modal extension; the paper's GBU(G) has none of them, and its irregular
judgment has no left rules at all.  The side condition of `L⊃ᵢ` is the
`|◯C|` adaptation recorded in the docstring at `wip/gbu_circ.lean:
1321–1337`: the original condition "the modal antecedent is smaller
than the local goal" made the calculus incomplete (the cell
`[◯((◯p ⊃ r) ∧ ◯p)] ⇒g ◯r ∨ z` is PLL-valid and underivable under it),
and the repair admits any right-signed subformula of `G` as antecedent.

`⊢_Gbu◯(G) G` is `ProvableGbuC G := Nonempty (GbuRC G [] G)`
(`wip/gbu_circ.lean:1368`).  Soundness for Kripke semantics is
`soundRC`/`soundIC` (`wip/gbu_circ.lean:1372–1480`), and
`pll_of_provableGbuC` connects it to `PLL`.

### 1.5 `FRJW(G)`: the disproof calculus

Two strata, again indexed by `G` (`FRJ/CalculusW.lean:52–241`, mutual,
Type-valued):

    FRJWr G t Γ C     written   t : Γ ⇒ C        regular disproofs, tagged
    FRJWi G Ξ Θ C     written   Ξ ; Θ → C        irregular disproofs, two zones

(Notation, Matthew's ruling of 2026-09-02, `docs/notation.md`: the
paper writes the stable zone `Σ`, which is not a Lean identifier, so
it is `Ξ` here in the text and in the binders; `Θ` is the paper's; `Ψ`
stays with `Gbu◯` as in the paper.  The Lean quoted in this document
is the code at `b2f2525`, where the binders still read `St`/`Th`, and
`stab`/`th` for the join families; the rename to `Ξ`/`Θ`, `Ξs`/`Θs` is
scheduled with the promotion of the chain out of `wip/`.)

An object of either family is a DISPROOF of its goal at its context:
soundness (`soundnessW`, `FRJ/CalculusW.lean:290–339` and the
countermodel construction it rests on) turns a root disproof
`t : Γ ⇒ G` into a Kripke countermodel of `G`, so
`DisprovableW G := ∃ t Γ, Nonempty (FRJWr G t Γ G)`
(`FRJ/CalculusW.lean:246–247`) implies `¬ PLL G`.  The paper's reading
of an irregular sequent `Ξ ; Θ → C` is that the countermodel's root
forces both zones and refutes `C`, with `Ξ` the *stable* zone that
survives when the sequent enters a join and `Θ` the zone that may be
lost; the join side condition (J1) below is what that reading needs.
The precise semantic clauses are in `FRJ/Model.lean` and the fidelity
table `docs/frj-fidelity.md` §3.

**Tags** are the modal extension's bookkeeping on regular disproofs
(`FRJ/Calculus.lean:311–319`):

```lean
inductive Tag where
  | barren          -- the root's modal cone is {root}
  | chain (D : Form) -- the root's modal cone is a promise chain, every world of which refutes D
  | blocked         -- no claim (a fallible promise, or an unmatched chain)
```

with the retention order `blocked ≤ chain D ≤ barren` (`tagLeB`), and
the pledge relation

```lean
inductive Covers (Γ : List Form) (W : Form) : Form → Prop   -- FRJ/Calculus.lean:238–243
  | refl : Covers Γ W W
  | circ {Z} : Covers Γ W Z → Covers Γ W (.circ Z)
  | andL {Z₁ Z₂} : Covers Γ W Z₁ → Covers Γ W (.and Z₁ Z₂)
  | andR {Z₁ Z₂} : Covers Γ W Z₂ → Covers Γ W (.and Z₁ Z₂)
  | imp  {A Z} : Covers Γ W Z → Clo Γ A → Covers Γ W (.imp A Z)
```

("every world of the chain refutes `W`, hence refutes `Z`").

**Refutation certificates.**  The barren joins retain a context
implication only when its antecedent is refuted at the new root; the
certificate for that is

```lean
inductive RefAt (cone : Bool) (Υ ctx : List Form) : Form → Prop   -- FRJ/RefAt.lean:36–48
  | ups  {C} : C ∈ Υ → RefAt cone Υ ctx C
  | bot  : RefAt cone Υ ctx .bot
  | imp  {A B} : Clo ctx A → RefAt cone Υ ctx B → RefAt cone Υ ctx (.imp A B)
  | circ {Z} : cone = true → RefAt cone Υ ctx Z → RefAt cone Υ ctx (.circ Z)
  | or   {Z₁ Z₂} : RefAt cone Υ ctx Z₁ → RefAt cone Υ ctx Z₂ → RefAt cone Υ ctx (.or Z₁ Z₂)
  | andL {Z₁ Z₂} : RefAt cone Υ ctx Z₁ → RefAt cone Υ ctx (.and Z₁ Z₂)
  | andR {Z₁ Z₂} : RefAt cone Υ ctx Z₂ → RefAt cone Υ ctx (.and Z₁ Z₂)
```

read: "over the goals `Υ` of the join's premises and the context
`ctx`, the new root refutes `X`"; `cone = true` means the root's modal
cone is the root itself, which is what licenses the `◯` clause.  A
*kept chain* is a list of context implications each retained by such a
certificate over the base plus the earlier links only:

```lean
inductive KeptChain (Υ base pool : List Form) : List Form → Prop   -- FRJ/RefAt.lean:144–150
  | nil : KeptChain Υ base pool []
  | cons {Y B rest} : KeptChain Υ base pool rest → Form.imp Y B ∈ pool →
      RefAt true Υ (base ++ rest) Y → KeptChain Υ base pool (Form.imp Y B :: rest)
```

with `keptOf Υ base pool` (`FRJ/RefAt.lean:245–257`) the greedy
fixpoint that computes the largest one.

**Regular rules** (`FRJWr`, thirteen constructors).  Below, `Ĝ_at ∖ F`
is `rm (gAt G) F`, and every rule carries `hgoal : C ∈ Sf^R(G)` for its
goal, which I omit.

```
 ────────────────────── Ax^R   [F prime;  Γ' ≐ Ĝ_at ∖ F]
   barren : Γ' ⇒ F

   t : Γ ⇒ Aₖ                       t : Γ ⇒ B
 ────────────────── ∧∈ₖ            ──────────────── ⊃∈  [A ∈ Cl(Γ)]
   t : Γ ⇒ A₁ ∧ A₂                  t : Γ ⇒ A ⊃ B

   t : Γ ⇒ Z
 ──────────────── ◯∈   [t = barren, or t = chain W with Covers Γ W Z]
   t : Γ ⇒ ◯Z

   { Ξⱼ ; Θⱼ → Cⱼ }ⱼ₌₀…ₙ
 ─────────────────────────────── ⋈^At   [F prime, F ∉ ⋃ⱼ Ξⱼ^at; (J1), (J2), no ◯ in any Ξⱼ;
   barren : Γ' ⇒ F                        kept a KeptChain over Υ = {Cⱼ}, base ⋈ctx^At, pool Θ;
                                          Γ' ≐ ⋈ctx^At(Ξ, Θ, F) ++ kept]

   { Ξⱼ ; Θⱼ → Cⱼ }ⱼ
 ─────────────────────────────── ⋈^∨    [(J1), (J2), no ◯ in any Ξⱼ; kept as above;
   barren : Γ' ⇒ C₁ ∨ C₂                  RefAt true Υ (base ++ kept) C₁ and C₂;  Γ' ≐ base ++ kept]

   { Ξⱼ ; Θⱼ → Cⱼ }ⱼ
 ─────────────────────────────── ⋈^◯    [(J1), (J2′): every A ⊃ B ∈ ⋃ⱼ Ξⱼ^imp has RefAt true Υ (base ++ kept) A;
   barren : Γ' ⇒ ◯Z                       no ◯ in any Ξⱼ; kept as above; RefAt true Υ (base ++ kept) Z;
                                          Γ' ≐ base ++ kept]

   { Ξⱼ ; Θⱼ → Cⱼ }ⱼ     { tᵢ : Δᵢ ⇒ Dᵢ }ᵢ₌₀…ₖ
 ────────────────────────────────────────── ⋈^At_P / ⋈^∨_P    [(J1), (J2), (J5), (J7s), the tag clause htag;
   t' : Γ' ⇒ F  /  C₁ ∨ C₂                                    F ∉ ⋃ Ξ^at  /  C₁, C₂ ∈ Υ;  Γ' ≐ ⋈ctx_P(Ξ, Θ, Υ, Δ)]

   { Ξⱼ ; Θⱼ → Cⱼ }ⱼ     { tᵢ : Δᵢ ⇒ Dᵢ }ᵢ
 ────────────────────────────────────────── ⋈^◯_P   [(J1), (J2), (J5), (J7s); every Dᵢ = Z with the pledge;
   chain Z : Γ' ⇒ ◯Z                                  Z ∈ Υ;  Γ' ≐ ⋈ctx_P(Ξ, Θ, Υ, Δ)]

   { Ξⱼ ; Θⱼ → Cⱼ }ⱼ
 ─────────────────────────────── ⋈^At_F / ⋈^∨_F   [(J1), (J2); F ∉ ⋃ Ξ^at  /  C₁, C₂ ∈ Υ;  Γ' ≐ ⋈ctx_F(Ξ, Θ, Υ)]
   blocked : Γ' ⇒ F  /  C₁ ∨ C₂
```

The join side conditions, by the names used in the constructors
(`FRJ/CalculusW.lean:76–198`):

| name | statement | role |
|---|---|---|
| (J1) `hJ1` | `∀ i ≠ j, Ξᵢ ⊆ Ξⱼ ++ Θⱼ` | each stable zone is forced at every other premise's root |
| (J2) `hJ2` | `∀ A ⊃ B ∈ ⋃ⱼ Ξⱼ^imp, A ∈ Υ` where `Υ = upsilon rhs = {Cⱼ}` | every stable implication's antecedent is one of the refuted goals (strict form) |
| (J2′) | `… RefAt true Υ (base ++ kept) A` | the `RefAt`-relaxed form, in `⋈^◯` only (relaxed 2026-09-01 with Matthew's sign-off) |
| `hcirc` | `⋃ⱼ Ξⱼ^◯ = []` | barren joins take no modal stable formula |
| `hkc` | `KeptChain Υ base (thPool th) kept` | the retained implications, certified link by link |
| (J5) `hJ5` | `∀ ◯Y ∈ ⋃ⱼ Ξⱼ^◯, ∃ i, Y ∈ Cl(Δᵢ)` | a promise join may take modal stable formulas if some regular premise covers the body |
| (J7s) `hJ7s` | `∀ i j, ∀ X ∈ Ξⱼ, X ∈ Cl(Δᵢ)` | every stable formula is closure-available at every regular premise |
| `htag` | `t' = blocked ∨ (t' = chain (D 0) ∧ ∀ i, Dᵢ = D 0 ∧ pledge(tᵢ, Δᵢ, D 0))` | the promise chain's tag, or no claim |

The context formers `joinCtxAtVBase`, `joinCtxOrVBase`, `joinCtxAtP`,
`joinCtxOrP`, `joinCtxAtF`, `joinCtxOrF`, `thPool`, `upsilon` are
definitions imported from `FRJ/Calculus.lean` and `FRJ/CalculusV.lean`
(`docs/frjw-plan.md` has the fidelity log).

**Irregular rules** (`FRJWi`, eight constructors):

```
 ──────────────────────────────────────── Ax^I   [F prime;  Θ' ≐ (Ĝ_at ∖ F) ++ Ĝ_imp ++ Ĝ_◯]
   [] ; Θ' → F

   Ξ ; Θ → Aₖ                          Ξ₁ ; Θ₁ → C₁     Ξ₂ ; Θ₂ → C₂
 ────────────────── ∧∈ᵢₖ              ───────────────────────────────── ∨∈  [Ξ₁ ⊆ Ξ₂ ++ Θ₂, Ξ₂ ⊆ Ξ₁ ++ Θ₁;
   Ξ ; Θ → A₁ ∧ A₂                      Ξ' ; Θ' → C₁ ∨ C₂                  Ξ' ≐ Ξ₁ ++ Ξ₂, Θ' ≐ Θ₁ ∩ Θ₂]

   Ξ ; Θ ++ Λ → B
 ─────────────────── ⊃∈ᵢ   [Θ ∩ Λ = ∅;  A ∈ Cl(Ξ ++ Λ);  Ξ' ≐ Ξ ++ Λ, Θ' ≐ Θ]
   Ξ' ; Θ' → A ⊃ B

   t : Γ ⇒ C                            t : Γ ⇒ Z
 ──────────────── Lift  [Θ ⊆ Ĝ ∩ Cl(Γ)] ──────────────── ◯∉  [pledge(t, Γ, Z);  Θ ⊆ Ĝ ∩ Cl(Γ)]
   [] ; Θ → C                            [] ; Θ → ◯Z

 ──────────────────── Ax^I◯   [ats ⊆ Ĝ_at;  classForce ats F = false;  Θ' ≐ vacZone(ats)]
   [] ; Θ' → ◯F
```

`Lift` is the rule FRJW adds to FRJV and `⊃∉` the one it deletes
(`FRJ/CalculusW.lean:1–41`); `◯∉`, `Ax^I◯` and the `◯` clauses of
`⋈` are the modal extension.  `vacZone(ats) = Ĝ.filter (classForce
ats)` (`FRJ/Calculus.lean:200–201`): the `Ĝ`-formulas forced by the
classical valuation `ats`.

### 1.6 The store and the queries

The search is parameterised by an abstract *store* `D : WSeq → Prop`
of disproof sequents (`wip/gbu_frjw_dichotomy.lean:58–108`):

```lean
inductive WSeq where
  | reg (t : Tag) (Γ : List Form) (C : Form)
  | irr (St Th : List Form) (C : Form)

def WDerivable (G : Form) : WSeq → Prop
  | .reg t Γ C  => Nonempty (FRJWr G t Γ C)
  | .irr St Th C => Nonempty (FRJWi G St Th C)

def WSubsumes : WSeq → WSeq → Prop            -- s₁ ⊑ s₂: s₂ is at least as good
  | .reg t₁ Γ₁ C₁, .reg t₂ Γ₂ C₂ => C₁ = C₂ ∧ tagLeB t₁ t₂ = true ∧ Γ₁ ⊆ Γ₂
  | .irr St₁ Th₁ C₁, .irr St₂ Th₂ C₂ => C₁ = C₂ ∧ St₁ ≐ St₂ ∧ Th₁ ⊆ Th₂
  | _, _ => False

def WSaturated (G : Form) (D : WSeq → Prop) : Prop :=
  (∀ s, D s → WDerivable G s) ∧                                  -- (DB1): sound
  (∀ s, WDerivable G s → ∃ s', D s' ∧ WSubsumes s s')            -- (DB2): complete up to subsumption
```

A saturated store contains, up to subsumption, every disproof there
is.  The two *queries* the searcher asks it are

```lean
def WEvalR (D) (Ψ : List Form) (C : Form) : Prop :=              -- "the store refutes Ψ ⇒g C"
  ∃ t Γ, D (.reg t Γ C) ∧ ∀ X ∈ Ψ, Clo Γ X

def WEvalI (D) (Ω : List Form) (C : Form) : Prop :=              -- "the store refutes Ω →g C"
  ∃ St Th, D (.irr St Th C) ∧ St ⊆ Ω ∧ Ω ⊆ St ++ Th
```

A regular query is answered by any stored regular row for `C` whose
context closure covers `Ψ`; an irregular one by a stored irregular row
for `C` whose stable zone lies inside `Ω` and whose two zones together
cover `Ω`.  Because every irregular row has `Ĝ`-bounded zones, a bare
negative answer `¬ WEvalI D Ω C` is vacuous at a context outside `Ĝ`;
the invariant the irregular search carries instead is

```lean
def WUnrefutedBelow (G) (D) (Ω : List Form) (C : Form) : Prop :=
  ¬ WEvalI D Ω C ∧
    ∃ Ω₀, (∀ X ∈ Ω₀, X ∈ gHat G) ∧ (∀ X ∈ Ω₀, Clo Ω X) ∧ ¬ WEvalI D Ω₀ C
```

("unrefuted here, and unrefuted at some `Ĝ`-bounded ancestor `Ω₀`
that `Ω` covers").

### 1.7 The cell statement and the crown

The search proves, for every cell (§2), the Type-valued statement

```lean
def WSearchOk (G : Form) (D : WSeq → Prop) : Bool × List Form × Form → Type
  | (true, Ψ, C) =>
      (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G →
      ¬ WEvalR D Ψ C → GbuRC G Ψ C
  | (false, Ω, C) =>
      (∀ X ∈ Ω, X ∈ sfL G) →
      (C.isCirc = false → ∀ X ∈ Ω, X ∈ gHat G) →
      C ∈ sfR G →
      WUnrefutedBelow G D Ω C → GbuIC G Ω C
```

(`wip/gbu_frjw_dichotomy.lean:121–130`): at a well-formed cell, if the
store does not refute it, one can BUILD the `Gbu◯` derivation.  The
main theorem of the search stage is

```lean
def searchW (hsat : WSaturated G D) (decI : ∀ Ω C, Decidable (WEvalI D Ω C)) :
    ∀ p : Bool × List Form × Form, WSearchOk G D p         -- wip/gbu_frjw_search.lean:328–330
```

and the crown, after the closure and saturation stages have built a
concrete saturated store for every `G`,

```lean
def decideGbuW (G : Form) : ProvableGbuC G ⊕' DisprovableW G              -- saturate:2387
def decideGbuWData (G : Form) : GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)    -- saturate:2485
def decidePLL (G : Form) : Decidable (PLL G)                              -- saturate:2428
theorem frjw_complete : ¬ ProvableGbuC G → DisprovableW G
theorem gbuw_complete : ¬ DisprovableW G → ProvableGbuC G
theorem provableGbuC_iff_pll : ProvableGbuC G ↔ PLL G
theorem disprovableW_iff_not_pll : DisprovableW G ↔ ¬ PLL G
```

all pinned `[propext, Quot.sound]`.

---

## 2. What a cell is

A **cell** is a triple

    (mode, Ψ, C) : Bool × List Form × Form

naming one sequent of `Gbu◯(G)` together with its judgment:
`(true, Ψ, C)` is the regular sequent `Ψ ⇒g C`, `(false, Ψ, C)` the
irregular sequent `Ψ →g C`.  The same context and goal give two
different cells, one per judgment, and they are decided differently
(§4, S2 versus S8).  In the Lean text the cell is the variable `p` of
`searchW`, destructured as `⟨reg, Ψ, C⟩`.

The word is used because the cells form a finite grid: a cell is
*well-formed for `G`* when `Ψ ⊆ Sf^L(G)` as a set and `C ∈ Sf^R(G)`,
so up to the set-reading of contexts there are at most
`2 · 2^|Sf^L(G)| · |Sf^R(G)|` of them, and the search moves through
that grid.  It never leaves it: every recursive call of `searchW` is
at a well-formed cell, which is why the two hypotheses `hΨ` and `hC`
are re-established at every step.

A cell is also a *question* put to the store: the regular query
`WEvalR D Ψ C` or the irregular one `WEvalI D Ω C` (§1.6).  The cell
statement `WSearchOk G D (mode, Ψ, C)` (§1.7) says that a negative
answer at this cell yields a `Gbu◯` derivation of it.  So the
dichotomy is a statement per cell, and "the dichotomy at cell level"
means: for every well-formed cell, either the store refutes it or
`Gbu◯` derives it.

Two more words used below.  A cell is **critical** when every context
member is in `Ĝ` (atoms, implications, `◯`-formulas), so no invertible
left rule applies; the regular critical cells are where the paper's
GBU(G) does its real work (the `L⊃` step on a context implication), and
the irregular critical cells with a `◯`-goal and no modal member,
`Ψ ⊆ Ĝ_at ∪ Ĝ_imp`, are the *corner* (§6).  The **measure** of a cell
is

    wgC G reg Ψ C = (unclosed G Ψ, tpC reg C, seqSize Ψ C)    -- wip/gbu_circ.lean:1634–1635
    unclosed G Ψ  = |Sf^L(G) ∖ Cl(Ψ)|                           -- wip/gbu.lean:262
    tpC reg C     = 2 if regular; 1 if ◯ occurs in C; else 0    -- wip/gbu_circ.lean:1631
    seqSize Ψ C   = Σ_{X∈Ψ} |X| + |C|                           -- wip/gbu.lean:292

compared lexicographically (`WgLt`, `wip/gbu.lean:305`; well-founded by
`wgLt_wf`, `wip/gbu.lean:492`).  Every recursive call of `searchW`
goes to a cell of strictly smaller measure, and §4 shows at which
snapshot each component is the one paying.

---

## 3. What a motive is

When a statement is proved by induction, or a function defined by
recursion, there is always a statement *schema* in play: the thing
being established, as a function of the object recursed on.  Lean
calls that function the **motive**.  For induction on the natural
numbers the motive is the predicate `P : ℕ → Prop` in

    P 0  →  (∀ n, P n → P (n+1))  →  ∀ n, P n

and the induction principle `Nat.rec` takes the motive as its first
(usually implicit) argument.  The word is the same for recursion into
a `Type`: a motive `C : α → Sort u` and the principle returns
`∀ a, C a`.  Two things about it are easy to miss when one has only
ever done informal induction.

*The motive must be chosen, and the choice is the proof.*  Proving
`∀ n, P n` by induction on `n` is often impossible with `P` itself as
the motive and possible with a stronger `Q` (with `Q n → P n`); the
textbook name is "strengthening the induction hypothesis", and in Lean
it is literally choosing a different motive.

*The motive must be a well-typed function of the recursed object.*  If
the goal mentions the recursed variable in a way Lean cannot abstract
into a function (typically because other hypotheses depend on it),
`induction` fails with "motive is not type correct"; the cure is to
`generalize` or `revert` until the goal is a function of the variable.
That failure message is where most Lean users first meet the word.

**The three motives of this development.**

(a) `searchW` (`wip/gbu_frjw_search.lean:331–333`) is well-founded
recursion on the *measure value*, through

    wgLt_wf.fix : ∀ {C : ℕ × ℕ × ℕ → Sort u},
        (∀ x, (∀ y, WgLt y x → C y) → C x) → ∀ x, C x

and the motive supplied is

    C x  :=  ∀ p : Bool × List Form × Form, wgC G p.1 p.2.1 p.2.2 = x → WSearchOk G D p

"every cell whose measure is `x` satisfies the cell statement".  The
equation `wgC … = x` is the standard device for recursing on a measure
rather than on the object: the fixpoint gives, at measure `x`, the
hypothesis `ihW` that the motive holds at every smaller measure `y`,
and a recursive call at a cell `q` then supplies `q`'s own measure
value, a proof that it is smaller, and `rfl` for the equation.  Snapshot
S0a of §4 shows exactly this state: the goal is the motive applied to
`x`, and `ihW` is the motive at every `y` with `WgLt y x`.  One line
later (`rintro ⟨reg, Ψ, C⟩ hx`) the cell has been introduced and the
equation `hx` names its measure; snapshot S0b shows the derived
hypothesis `IH`, which is `ihW` specialised to cells (`fun q hq => ihW
_ (hx ▸ hq) q rfl`): "any cell of smaller measure than the current one
satisfies the cell statement".  That `IH` is what every recursive call
of §4 invokes.

(b) `totalityW` (`wip/gbu_frjw_search.lean:278–321`) is structural
recursion on a formula `X : Form`, and its motive is implicit: the
equation compiler reads it off the declared type,

    motive X  :=  X ∈ sfR G → RefAt true (Z :: R₀) Ψ X ⊕' GbuIC G Ψ X

"every right-signed subformula is either certifiably refuted at this
cell or derivable at it".  There is no `induction` tactic in sight;
the five equations of the definition are the five cases of the
induction and the recursive calls at immediate subformulas are the
induction hypotheses.

(c) `tCr`/`tCi` (`wip/gbu_frjw_closure.lean:1452–1677`) are mutual
structural induction on a DISPROOF `d`, and the motives are `Prop`s:

    motive_r (d : FRJWr G t Γ C)   :=  ∃ r ∈ db, WSubsumes (.reg t Γ C) r.s
    motive_i (d : FRJWi G St Th C) :=  ∃ r ∈ db, WSubsumes (.irr St Th C) r.s

"every derivable disproof sequent has a stored subsumer".  Here the
motive mentions only the *indices* of `d` (its tag, zones and goal),
not `d` itself; that is what allows the conclusion to be a proposition
extracted from an inductive family in `Type` without any choice
principle.

**How a motive appears interactively.**  With the cursor after
`refine wgLt_wf.fix (fun x ihW => ?_)` the infoview shows S0a: the
motive is not named anywhere on screen, it is simply *the goal*, with
`ihW`'s type being the same statement at every smaller `y`.  With the
cursor inside a case of `induction d with | impIn d hA hg ih => …`
(the `tCr` proof is written as a recursive definition, but the same
state arises from the tactic) the goal is the motive at the
constructor's conclusion and `ih` is the motive at its premise.  When
one wants to see the motive explicitly, `induction d using FRJWr.rec
(motive_1 := …) (motive_2 := …)` names it; when Lean cannot infer it,
that is the form one is forced into.  For `wgLt_wf.fix` the motive is
inferred from the expected type of the `have main : ∀ x, ∀ p, … → …`
line, which is why that line is written with `x` first: its body IS
the motive.

---

## 4. The proof-state trace of `searchW` (B.3)

### 4.0 How to read this section

Twenty-two snapshots of the infoview, taken at the stage boundaries
of `searchW` (`wip/gbu_frjw_search.lean:328–690` at `b2f2525`).  The
method is the one of `docs/annotated/README.md` §"The extraction
method": a verbatim copy of the file outside the repository,
`trace_state` inserted at each point (preceded by a `trace` label so
the transcript is self-describing), one compilation with `lake env
lean` (38 s), blocks transcribed unedited.  Each snapshot is captioned
with its **anchor**, the line of the checked-in file *after which* the
state is observed (or, where the caption says "on entry", the line the
state is observed *before*).

One mechanical trim, flagged here once and applied to every snapshot
after S0b: the six standing hypotheses

```
G : Form
D : WSeq → Prop
hsat : WSaturated G D
decI : (Ω : List Form) → (C : Form) → Decidable (WEvalI D Ω C)
x : ℕ × ℕ × ℕ
ihW : (y : ℕ × ℕ × ℕ) → WgLt y x → (p : Bool × List Form × Form) → wgC G p.1 p.2.1 p.2.2 = y → WSearchOk G D p
```

are identical in all twenty-two blocks and are replaced by the line
`⟨standing: G D hsat decI x ihW⟩`.  Nothing else is trimmed: every
other hypothesis is reproduced exactly as Lean printed it, daggers
included.  The `case` line is Lean's bookkeeping name for the branch
and is kept where it orients the reader.

Reading conventions particular to this proof.  `hx` is the measure
equation of the current cell, always in the unreduced form
`wgC G (reg, Ψ, C).1 (reg, Ψ, C).2.1 (reg, Ψ, C).2.2 = x`, because it
was introduced by `rintro` on the tuple; Lean does not reduce the
projections in a hypothesis.  `IH` is the induction hypothesis at
cells of smaller measure (§3).  The three hypotheses `hΨ`, `hC` and
`hne` (regular) or `hΨ`, `hΩc`, `hC`, `hnb`, `hne` (irregular) are the
cell statement's own premises, introduced at S2/S8.  `f : Focus Ψ X`
is the focus on a context member (compaction item C.3): its fields
`f.rest`, `f.ctxEq : Ψ ≐ X :: f.rest`, `f.memsub`, `f.size` are what
the descended cell is built from.

The stage map, for orientation (all lines `wip/gbu_frjw_search.lean`):

| stage | lines | what happens |
|---|---|---|
| S0 | 331–338 | the fixpoint on the measure, the cell, `IH` |
| S1 | 339 | `cases reg`: irregular first, regular second |
| S2 | 341–349 | irregular preamble; `ax` if `C ∈ Ψ`; atoms and `⊥` are impossible |
| S3 | 350–399 | irregular `∧`, `∨`, `⊃` goals |
| S4 | 400–407 | irregular `◯Z` goal: is every member in `Ĝ`? is there a modal member? |
| S5 | 408–415 | the critical modal cell; is `Z` refuted? |
| S5a | 416–466 | `Z` refuted: countermodel scan, `R₀`, the certificate test, THE CORNER |
| S5b | 467–473 | `Z` unrefuted: `R◯ᵢ` |
| S6 | 474–490 | a modal member: `L◯ᵢ` |
| S7 | 491–528 | a non-`Ĝ` member: `L⊥ᵢ`, `L∧ᵢ`, `L∨ᵢ` |
| S8 | 529–538 | regular preamble; `ax`; the `Ĝ`-scan; the critical regular cell |
| S8a | 539–568 | the helpers `limpStep`, `fromImp`, `upsToImp` |
| S8b | 569–658 | regular goal cases: atom/`⊥`, `∧`, `⊃`, `∨`, `◯` |
| S9 | 659–689 | the non-critical regular cell: `L⊥`, `L∧`, `L∨` |
| S10 | 690 | the base call |

### 4.1 S0a: the motive at `x`

Anchor `wip/gbu_frjw_search.lean:333`, immediately after
`refine wgLt_wf.fix (fun x ihW => ?_)`.

```
G : Form
D : WSeq → Prop
hsat : WSaturated G D
decI : (Ω : List Form) → (C : Form) → Decidable (WEvalI D Ω C)
x : ℕ × ℕ × ℕ
ihW : (y : ℕ × ℕ × ℕ) → WgLt y x → (p : Bool × List Form × Form) → wgC G p.1 p.2.1 p.2.2 = y → WSearchOk G D p
⊢ (p : Bool × List Form × Form) → wgC G p.1 p.2.1 p.2.2 = x → WSearchOk G D p
```

The goal is the motive of §3(a) applied to `x`; `ihW` is the motive at
every `y` below `x` in `WgLt`.  There is no cell yet: `x` is a measure
value, and the cell is universally quantified in the goal.  The two
hypotheses that never change from here on are `hsat` (the store is
saturated) and `decI` (the irregular query is decidable); these are
`searchW`'s two parameters, and they are the *whole* of what the
search knows about the store.

### 4.2 S0b: the cell, its measure equation, and `IH`

Anchor `search:338`, after `have IH … := fun q hq => ihW _ (hx ▸ hq) q rfl`.

```
G : Form
D : WSeq → Prop
hsat : WSaturated G D
decI : (Ω : List Form) → (C : Form) → Decidable (WEvalI D Ω C)
x : ℕ × ℕ × ℕ
ihW : (y : ℕ × ℕ × ℕ) → WgLt y x → (p : Bool × List Form × Form) → wgC G p.1 p.2.1 p.2.2 = y → WSearchOk G D p
reg : Bool
Ψ : List Form
C : Form
hx : wgC G (reg, Ψ, C).1 (reg, Ψ, C).2.1 (reg, Ψ, C).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G reg Ψ C) → WSearchOk G D q
⊢ WSearchOk G D (reg, Ψ, C)
```

`rintro ⟨reg, Ψ, C⟩ hx` has named the cell.  `IH` is the usable form of
the induction hypothesis: "any cell `q` of smaller measure than
`(reg, Ψ, C)` satisfies the cell statement".  Its one-line proof
`fun q hq => ihW _ (hx ▸ hq) q rfl` is the whole of the measure
bookkeeping: `hx ▸ hq` rewrites `q`'s measure comparison from "smaller
than the current cell's measure" to "smaller than `x`", and `rfl`
discharges `q`'s own measure equation.  From here on `x`, `ihW` and
`hx` are never used again, only `IH`.

The goal `WSearchOk G D (reg, Ψ, C)` is still folded; `cases reg` next
splits it into the two judgments and the `show` lines at 341 and 530
unfold it to the two clauses of §1.7.

### 4.3 S2: the irregular preamble

Anchor `search:346`, after the `refine byDec (inferInstance :
Decidable (C ∈ Ψ)) (fun hax => .ax C …) (fun hax => ?_)`.

```
case false
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
C : Form
hx : wgC G (false, Ψ, C).1 (false, Ψ, C).2.1 (false, Ψ, C).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G false Ψ C) → WSearchOk G D q
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
hΩc : C.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G
hC : C ∈ sfR G
hnb : WUnrefutedBelow G D Ψ C
hne : ¬WEvalI D Ψ C
hax : C ∉ Ψ
⊢ GbuIC G Ψ C
```

This is the irregular cell `Ψ →g C` with all four premises of the cell
statement introduced.  `hΩc` is the modal invariant peculiar to the
irregular judgment: unless the goal is `◯`-shaped, the context is
inside `Ĝ` (no invertible left rule is pending, because the irregular
judgment has none except at `◯` goals).  `hne` is the first component
of `hnb`, extracted for convenience.  `hax` records that the axiom
did not fire.

What the next line does with this state: `cases C`.  For `atom a` and
`bot` the branch closes at once by `absurd (evalI_axI_gHat hsat (hΩc
rfl) rfl hC hax) hne`: an atom or `⊥` that is *not* in a `Ĝ`-context
is always refuted by the store (the `Ax^I` row of §1.5 covers it), so
`hne` is contradicted.  This is the first appearance of the pattern
that runs through the whole proof: *the positive branch of a test is
closed by a lemma saying the store would have had a row*, §5.

In the proof run of §7 (`p ⊃ ◯p`) this state is reached once, at the
cell `(false, [p], p)`, and there the `byDec` above it took the OTHER
branch: `p ∈ [p]`, so `.ax p (ctxEq_cons_self hax)` closed the cell
without ever reaching S2.

### 4.4 S3: an irregular `⊃`-goal whose antecedent is not closure-available

Anchor `search:395`, on entry to the `¬ Clo Ψ A` branch of the
irregular `imp A B` case.

```
case false.imp.refine_2
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
A B : Form
hx : wgC G (false, Ψ, A.imp B).1 (false, Ψ, A.imp B).2.1 (false, Ψ, A.imp B).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G false Ψ (A.imp B)) → WSearchOk G D q
hΩc : (A.imp B).isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G
hC : A.imp B ∈ sfR G
hnb : WUnrefutedBelow G D Ψ (A.imp B)
hne : ¬WEvalI D Ψ (A.imp B)
hax : A.imp B ∉ Ψ
hA : A ∈ sfL G
hB : B ∈ sfR G
hg : ∀ X ∈ Ψ, X ∈ gHat G
hcl : ¬Clo Ψ A
⊢ GbuIC G Ψ (A.imp B)
```

The goal has been refined to `A ⊃ B`; `hA`, `hB` are the signed
subformula facts for its two halves (`sfR_imp`); `hg` is `hΩc`
discharged at `rfl` (the goal is not `◯`-shaped, so the context is in
`Ĝ`); `hcl` is the decision `decClo Ψ A` in its negative branch.  The
next line applies `R⊃ₙᵢ`, which changes mode: the premise `A, Ψ ⇒g B`
is REGULAR.  Its measure payment is

    wgDrop (unclosed_lt hA hcl) : WgLt (wgC G true (A :: Ψ) B) (wgC G false Ψ (A.imp B))

component 1: `A` is a left-signed subformula not in `Cl(Ψ)`, so adding
it to the context strictly reduces `|Sf^L(G) ∖ Cl(Ψ)|`, and nothing
else about the measure matters (the mode rank actually *rises*, 0 or
1 to 2, which is why this step cannot be paid by anything but
`unclosed`).  The negative hypothesis the recursive call needs,
`¬ WEvalR D (A :: Ψ) B`, is obtained by contraposing the bank lemma

    gbuInv9 : A ⊃ B ∈ Sf^R(G) → Ψ ⊆ Ĝ → WEvalR D (A :: Ψ) B → WEvalI D Ψ (A ⊃ B)

against `hne`.  The other branch of the `decClo` test (not shown; the
`hcl : Clo Ψ A` case at 388–394) applies `R⊃ᵢ` instead, paid by
`seqSize` (`B` is smaller than `A ⊃ B`), with `gbuInv8` supplying the
negative hypothesis.

### 4.5 S4: an irregular `◯Z` goal, before the two scans

Anchor `search:401`, after `have hZsf : Z ∈ sfR G := sfR_circ hC`.

```
case false.circ
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
Z : Form
hx : wgC G (false, Ψ, Z.circ).1 (false, Ψ, Z.circ).2.1 (false, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G false Ψ Z.circ) → WSearchOk G D q
hΩc : Z.circ.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G
hC : Z.circ ∈ sfR G
hnb : WUnrefutedBelow G D Ψ Z.circ
hne : ¬WEvalI D Ψ Z.circ
hax : Z.circ ∉ Ψ
hZsf : Z ∈ sfR G
⊢ GbuIC G Ψ Z.circ
```

The `◯`-goal is the only irregular goal at which the context is not
known to be inside `Ĝ`: `hΩc`'s premise `Z.circ.isCirc = false` is
false, so `hΩc` is vacuous here and gives nothing.  That is why the
irregular left rules exist only at `◯` goals, and why the next two
lines scan `Ψ` twice with `findNotT`: first for a member outside `Ĝ`
(if one exists, S7 decomposes it), then, if all members are in `Ĝ`, for
a modal member `◯Y'` (if one exists, S6 opens it).  If both scans come
back empty, `Ψ ⊆ Ĝ_at ∪ Ĝ_imp`, and we are at the critical modal cell,
S5.  The two scans are constructive: `findNotT` returns either the
universal statement or a witness with its membership proof, as a `⊕'`.

### 4.6 S5: the critical modal cell

Anchor `search:414`, after the `hΩai` block.

```
case false.circ.inl.inl
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
Z : Form
hx : wgC G (false, Ψ, Z.circ).1 (false, Ψ, Z.circ).2.1 (false, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G false Ψ Z.circ) → WSearchOk G D q
hΩc : Z.circ.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G
hC : Z.circ ∈ sfR G
hnb : WUnrefutedBelow G D Ψ Z.circ
hne : ¬WEvalI D Ψ Z.circ
hax : Z.circ ∉ Ψ
hZsf : Z ∈ sfR G
hg : ∀ a ∈ Ψ, a ∈ gHat G
hnoc : ∀ a ∈ Ψ, a.isCirc = false
hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G
⊢ GbuIC G Ψ Z.circ
```

`hg` and `hnoc` are the two scans' universal outcomes (Lean's own
binder name `a` shows they came from `findNotT`), combined into `hΩai`:
the context is atoms and implications only.  This is the cell shape
the paper's GBU(G) never meets (its irregular judgment has no `◯`
goal) and the whole difficulty of the modal extension sits here.  The
next line asks the store whether `Z` itself is refuted at `Ψ`:
`byDec (decI Ψ Z)`.  If it is not (S5b), `R◯ᵢ` applies and the goal
shrinks.  If it is (S5a), no right rule helps, and the only `Gbu◯`
route is modus ponens on a context implication (`L⊃ᵢ`), which needs its
antecedent derived first; the store side must instead manufacture a
`◯Z`-row by a barren join.

### 4.7 S5a-i: `Z` refuted, no classical countermodel, the certificate test

Anchor `search:423`, after `hR₀ok`.

```
case false.circ.inl.inl.refine_1.inr
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
Z : Form
hx : wgC G (false, Ψ, Z.circ).1 (false, Ψ, Z.circ).2.1 (false, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G false Ψ Z.circ) → WSearchOk G D q
hΩc : Z.circ.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G
hC : Z.circ ∈ sfR G
hnb : WUnrefutedBelow G D Ψ Z.circ
hne : ¬WEvalI D Ψ Z.circ
hax : Z.circ ∉ Ψ
hZsf : Z ∈ sfR G
hg : ∀ a ∈ Ψ, a ∈ gHat G
hnoc : ∀ a ∈ Ψ, a.isCirc = false
hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G
heZ : WEvalI D Ψ Z
hnocm : ∀ ats ∈ (gAt G).sublists, ¬(classForce ats Z = false ∧ ∀ X ∈ Ψ, classForce ats X = true)
R₀ : List Form := List.filter (fun A => decide (WEvalI D Ψ A)) (sfR G)
hR₀def : R₀ = List.filter (fun A => decide (WEvalI D Ψ A)) (sfR G)
hR₀ok : ∀ A ∈ R₀, WEvalI D Ψ A
⊢ GbuIC G Ψ Z.circ
```

Three things have happened since S5.  `heZ`: the store refutes `Z` at
`Ψ`.  `hnocm`: the classical countermodel scan `findCMT` came back
empty, so no valuation over `Ĝ_at` forces all of `Ψ` while falsifying
`Z`; had one existed, the `Ax^I◯` row would have refuted `◯Z` at `Ψ`
outright (`wEvalI_axIC`, closing by `hne`).  `R₀`: the list of ALL
right-signed subformulas the store refutes at `Ψ`, computed by
filtering `sfR G` through the decider; `hR₀ok` is its specification.
`R₀` is the `Υ`-like set over which the next line runs the
*certificate test*: for every context implication `Y' = A ⊃ B`, is
`A ∈ R₀`, or does `A` carry a `RefAt true (Z :: R₀) Ψ` certificate?
If every implication passes (`hallK`, not shown), the barren join
`⋈^◯` can be fired with the whole context retained
(`refutedCleanly_circ_certs`, `wip/gbu_frjw_corner.lean:470`), the
store has a `◯Z`-row, and `hne` is contradicted.  If one fails, we are
at the corner.

### 4.8 S5a-ii: the corner

Anchor `search:443`, after `obtain ⟨hA₂sf, hB₂sf⟩ := sfL_imp (hΨ _ hY₂Ψ)`.

```
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
Z : Form
hx : wgC G (false, Ψ, Z.circ).1 (false, Ψ, Z.circ).2.1 (false, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G false Ψ Z.circ) → WSearchOk G D q
hΩc : Z.circ.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G
hC : Z.circ ∈ sfR G
hnb : WUnrefutedBelow G D Ψ Z.circ
hne : ¬WEvalI D Ψ Z.circ
hax : Z.circ ∉ Ψ
hZsf : Z ∈ sfR G
hg : ∀ a ∈ Ψ, a ∈ gHat G
hnoc : ∀ a ∈ Ψ, a.isCirc = false
hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G
heZ : WEvalI D Ψ Z
hnocm : ∀ ats ∈ (gAt G).sublists, ¬(classForce ats Z = false ∧ ∀ X ∈ Ψ, classForce ats X = true)
R₀ : List Form := List.filter (fun A => decide (WEvalI D Ψ A)) (sfR G)
hR₀def : R₀ = List.filter (fun A => decide (WEvalI D Ψ A)) (sfR G)
hR₀ok : ∀ A ∈ R₀, WEvalI D Ψ A
Y₂ : Form
hnK✝ : ¬(ante Y₂ ∈ R₀ ∨ RefAt true (Z :: R₀) Ψ (ante Y₂))
hY₂i : Y₂.isImp = true
hY₂Ψ✝ : Y₂ ∈ Ψ
A₂ B₂ : Form
x✝ : (A₂.imp B₂).isImp = true
hY₂Ψ : A₂.imp B₂ ∈ Ψ
hnK : ¬(ante (A₂.imp B₂) ∈ R₀ ∨ RefAt true (Z :: R₀) Ψ (ante (A₂.imp B₂)))
hY₂ : A₂.imp B₂ ∈ impPart Ψ
hA₂sf : A₂ ∈ sfR G
hB₂sf : B₂ ∈ sfL G
⊢ GbuIC G Ψ Z.circ
```

The certificate test has found a failing implication `Y₂`, matched
to `A₂ ⊃ B₂` (the daggered `hnK✝`, `hY₂Ψ✝` are the pre-match versions,
kept by Lean because the `match` generalised them; `x✝` is the `isImp`
proof the match consumed).  `hnK` says: `A₂` is NOT in `R₀`, i.e. the
store does NOT refute `A₂` at `Ψ` (that is the meaning of `ante (A₂
⊃ B₂) ∉ R₀`, through `hR₀def`), AND `A₂` carries no certificate.  Note
the sign of `hA₂sf`: the antecedent of a left-signed implication is
RIGHT-signed, so `A₂ ∈ sfR G`, and `totalityW`'s motive applies to it.

The next line is the call that closes the corner:

    totalityW hsat decI hg (fun X hXsf hI => …) (fun A' B' hXsf hncl hnR => IH (true, A' :: Ψ, B') …) A₂ hA₂sf
      : RefAt true (Z :: R₀) Ψ A₂ ⊕' GbuIC G Ψ A₂

Its second argument proves that every refuted form is in `R₀` (the
filter specification, read backwards); its third is the callback of
§3(b): a `¬Clo` antecedent implication `A' ⊃ B'` is handed to the
regular stratum at the cell `(true, A' :: Ψ, B')`, paid by `unclosed`
through `IH`.  The result is matched: the `.inl` (certificate) branch
is absurd by `hnK`; the `.inr` branch is S5a-ii(Der).

### 4.9 S5a-ii(Der): `A₂` is derivable, `L⊃ᵢ` steps through `Y₂`

Anchor `search:458`, after `hclB₂`.

```
case inr
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
Z : Form
hx : wgC G (false, Ψ, Z.circ).1 (false, Ψ, Z.circ).2.1 (false, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G false Ψ Z.circ) → WSearchOk G D q
hΩc : Z.circ.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G
hC : Z.circ ∈ sfR G
hnb : WUnrefutedBelow G D Ψ Z.circ
hne : ¬WEvalI D Ψ Z.circ
hax : Z.circ ∉ Ψ
hZsf : Z ∈ sfR G
hg : ∀ a ∈ Ψ, a ∈ gHat G
hnoc : ∀ a ∈ Ψ, a.isCirc = false
hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G
heZ : WEvalI D Ψ Z
hnocm : ∀ ats ∈ (gAt G).sublists, ¬(classForce ats Z = false ∧ ∀ X ∈ Ψ, classForce ats X = true)
R₀ : List Form := List.filter (fun A => decide (WEvalI D Ψ A)) (sfR G)
hR₀def : R₀ = List.filter (fun A => decide (WEvalI D Ψ A)) (sfR G)
hR₀ok : ∀ A ∈ R₀, WEvalI D Ψ A
Y₂ : Form
hnK✝ : ¬(ante Y₂ ∈ R₀ ∨ RefAt true (Z :: R₀) Ψ (ante Y₂))
hY₂i : Y₂.isImp = true
hY₂Ψ✝ : Y₂ ∈ Ψ
A₂ B₂ : Form
x✝ : (A₂.imp B₂).isImp = true
hY₂Ψ : A₂.imp B₂ ∈ Ψ
hnK : ¬(ante (A₂.imp B₂) ∈ R₀ ∨ RefAt true (Z :: R₀) Ψ (ante (A₂.imp B₂)))
hY₂ : A₂.imp B₂ ∈ impPart Ψ
hA₂sf : A₂ ∈ sfR G
hB₂sf : B₂ ∈ sfL G
hDer : GbuIC G Ψ A₂
f : Focus Ψ (A₂.imp B₂)
hclB₂ : ∀ W ∈ Ψ, Clo (B₂ :: f.rest) W
⊢ GbuIC G Ψ Z.circ
```

`hDer` is the DERIVATION of `Ψ →g A₂` that totality returned: a term,
not a proposition.  `f` focuses `Ψ` on `A₂ ⊃ B₂`; `hclB₂` says every
member of `Ψ` is closure-available in the descended context
`B₂, f.rest` (the focused implication itself through its consequent,
`Clo.imp`; the rest by membership).  The remaining lines build

    .limpLI (transportIC hDer f.ctxEq) d₂ (Or.inr hA₂sf) hC f.ctxEq

where `d₂ := IH (false, B₂ :: f.rest, ◯Z) …` is the recursive call on
the consequent, paid by `seqSize` (`f.lt1`: `B₂` is smaller than `A₂ ⊃
B₂`) with `unrefutedBelow_step hsat hclB₂ hnb` transporting the
invariant, and `transportIC` moves `hDer` from `Ψ` to `A₂ ⊃ B₂ ::
f.rest` (the `L⊃ᵢ` rule wants its left premise in the focused shape).
`Or.inr hA₂sf` discharges `L⊃ᵢ`'s side condition by the `|◯C|`
adaptation: `A₂ ∈ Sf^R(G)`.

### 4.10 S5b: `Z` unrefuted at the critical cell

Anchor `search:468`, on entry to the negative branch of `decI Ψ Z`.

```
case false.circ.inl.inl.refine_2
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
Z : Form
hx : wgC G (false, Ψ, Z.circ).1 (false, Ψ, Z.circ).2.1 (false, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G false Ψ Z.circ) → WSearchOk G D q
hΩc : Z.circ.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G
hC : Z.circ ∈ sfR G
hnb : WUnrefutedBelow G D Ψ Z.circ
hne : ¬WEvalI D Ψ Z.circ
hax : Z.circ ∉ Ψ
hZsf : Z ∈ sfR G
hg : ∀ a ∈ Ψ, a ∈ gHat G
hnoc : ∀ a ∈ Ψ, a.isCirc = false
hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G
heZ : ¬WEvalI D Ψ Z
⊢ GbuIC G Ψ Z.circ
```

The easy half of the critical cell.  `R◯ᵢ` applies with the irregular
premise `Ψ →g Z`, paid by `seqSize` (`seqSize_goal (Nat.lt_succ_self
_)`), and the negative hypothesis of the premise cell is `heZ` itself,
lifted to the invariant by `unrefutedBelow_of_gHat hg heZ` (on a
`Ĝ`-context the bare negative answer IS the invariant, with `Ω₀ := Ψ`).
No bank lemma is needed: the premise's negative fact was decided
directly.

### 4.11 S6: a modal member, `L◯ᵢ`

Anchor `search:484`, after `hcov`.

```
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
Z : Form
hx : wgC G (false, Ψ, Z.circ).1 (false, Ψ, Z.circ).2.1 (false, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G false Ψ Z.circ) → WSearchOk G D q
hΩc : Z.circ.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G
hC : Z.circ ∈ sfR G
hnb : WUnrefutedBelow G D Ψ Z.circ
hne : ¬WEvalI D Ψ Z.circ
hax : Z.circ ∉ Ψ
hZsf : Z ∈ sfR G
hg : ∀ a ∈ Ψ, a ∈ gHat G
Y : Form
hYc' : Y.isCirc = true
Y' : Form
x✝ : Y'.circ.isCirc = true
hYΨ : Y'.circ ∈ Ψ
hYc : ¬Y'.circ.isCirc = false
f : Focus Ψ Y'.circ
hY'sf : Y' ∈ sfL G
hcov : ∀ V ∈ Ψ, Clo (Y' :: f.rest) V
⊢ GbuIC G Ψ Z.circ
```

The second scan found a modal member `◯Y'` (matched from `Y`; `hYc`
is the scan's raw negative, `hYc'` its Boolean flip).  The pattern of
every left rule from here on is the compaction item C.3's "focus,
cover, descend, apply": `f` focuses, `hcov` covers (`Clo.circ` for the
opened member, membership for the rest), the descent is `IH (false,
Y' :: f.rest, ◯Z)` paid by `seqSize` (`f.lt1 (Nat.lt_succ_self _)`:
`|Y'| < |◯Y'|`), the invariant is transported by `unrefutedBelow_step
hsat hcov hnb`, and `.lcircI d (hΨ _ hYΨ) f.ctxEq` applies the rule.
The side condition `◯Y' ∈ Sf^L(G)` is `hΨ _ hYΨ`.

### 4.12 S7: a non-`Ĝ` member, `L∧ᵢ`

Anchor `search:505`, after `hcov` in the `and A B` case.

```
case false.circ.inr.and
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
Z : Form
hx : wgC G (false, Ψ, Z.circ).1 (false, Ψ, Z.circ).2.1 (false, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G false Ψ Z.circ) → WSearchOk G D q
hΩc : Z.circ.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G
hC : Z.circ ∈ sfR G
hnb : WUnrefutedBelow G D Ψ Z.circ
hne : ¬WEvalI D Ψ Z.circ
hax : Z.circ ∉ Ψ
hZsf : Z ∈ sfR G
A B : Form
hXΨ : A.and B ∈ Ψ
hXn : A.and B ∉ gHat G
f : Focus Ψ (A.and B)
hA : A ∈ sfL G
hB : B ∈ sfL G
hcov : ∀ V ∈ Ψ, Clo (A :: B :: f.rest) V
⊢ GbuIC G Ψ Z.circ
```

The first scan found a member outside `Ĝ` (`hXn`); `cases X` on it
leaves only `⊥`, `∧`, `∨` (atoms, implications and `◯`-formulas are in
`Ĝ` by `mem_gHat_of_isHat`, contradiction).  Shown is the `∧` case:
descent to `A :: B :: f.rest` paid by `f.lt2 (Nat.lt_succ_self _)`
(`|A| + |B| < |A ∧ B|`), coverage `Clo.and (base) (base)`, rule
`.landLI d hC f.ctxEq`.  The `∨` case (512–528) has two descents; `⊥`
closes at once by `.lbotI hC f.ctxEq`.  These are exactly the
invertible left rules of the regular judgment (S9) transposed to the
irregular judgment at a `◯` goal; they exist only because `hΩc` is
vacuous there (S4).

### 4.13 S8: the regular preamble

Anchor `search:534`, after the `byDec (C ∈ Ψ)` refine.

```
case true
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
C : Form
hx : wgC G (true, Ψ, C).1 (true, Ψ, C).2.1 (true, Ψ, C).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G true Ψ C) → WSearchOk G D q
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
hC : C ∈ sfR G
hne : ¬WEvalR D Ψ C
hax : C ∉ Ψ
⊢ GbuRC G Ψ C
```

The regular cell `Ψ ⇒g C` with its three premises (compare S2: no
`hΩc`, no invariant; the negative fact is the plain regular query).
This is the state every run of §7 begins in, at the root cell
`(true, [], G)`.  The next line, `rcases splitHatT Ψ with hall | ⟨l, r,
X, hsplit, hX⟩`, decides whether every member is `Ĝ`-shaped (critical,
S8-crit) or exhibits a split at a non-`Ĝ` member (S9).

### 4.14 S8-crit: the critical regular cell

Anchor `search:538`, after `hΩ`.

```
case true.inl
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
C : Form
hx : wgC G (true, Ψ, C).1 (true, Ψ, C).2.1 (true, Ψ, C).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G true Ψ C) → WSearchOk G D q
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
hC : C ∈ sfR G
hne : ¬WEvalR D Ψ C
hax : C ∉ Ψ
hall : ∀ X ∈ Ψ, isHat X = true
hΩ : ∀ Y ∈ Ψ, Y ∈ gHat G
⊢ GbuRC G Ψ C
```

`hΩ`: the context is inside `Ĝ`.  This is the cell shape at which the
paper's GBU(G) applies `L⊃` (its only non-invertible step), and the
three helpers defined next (`limpStep`, `fromImp`, `upsToImp`,
539–568) package that step so that every goal case can call it.

### 4.15 S8a: inside `limpStep`

Anchor `search:545`, after `hΩ'`.

```
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
C : Form
hx : wgC G (true, Ψ, C).1 (true, Ψ, C).2.1 (true, Ψ, C).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G true Ψ C) → WSearchOk G D q
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
hC : C ∈ sfR G
hne : ¬WEvalR D Ψ C
hax : C ∉ Ψ
hall : ∀ X ∈ Ψ, isHat X = true
hΩ : ∀ Y ∈ Ψ, Y ∈ gHat G
A B : Form
hYΨ : A.imp B ∈ Ψ
hnA : ¬WEvalI D Ψ A
f : Focus Ψ (A.imp B)
hAsf : A ∈ sfR G
hBsf : B ∈ sfL G
hΩ' : ∀ W ∈ A.imp B :: f.rest, W ∈ gHat G
⊢ GbuRC G Ψ C
```

`limpStep` is the `L⊃` step: given a context implication `A ⊃ B`
whose antecedent the store does NOT refute (`hnA`), build `Ψ ⇒g C`.
Its two recursive calls are the two premises of `L⊃`:

* `d₁ := IH (false, A ⊃ B :: f.rest, A) …`, the IRREGULAR left premise
  `A ⊃ B, Ψ →g A`.  This is the regular-to-irregular release, paid by
  component 2 (`wgFocus`: `tpC false A < tpC true C`, i.e. `0 or 1 <
  2`), with the context unchanged as a set (`hΩ'` re-establishes the
  `Ĝ`-bound for `hΩc`), and its negative fact is `hnA` transported by
  `wEvalI_ctxEq` across `f.ctxEq` and lifted by
  `unrefutedBelow_of_gHat`.
* `d₂ := IH (true, B :: f.rest, C) …`, the REGULAR right premise
  `B, Ψ ⇒g C`, paid by `seqSize` (`f.lt1`), with `gbuInv4`
  (`WEvalR D (B :: Ψ) C → WEvalR D (A ⊃ B :: Ψ) C`) contraposed against
  `hne` for its negative fact.

Then `.limpL d₁ d₂ f.ctxEq`.  Who calls `limpStep`?  Every goal case
of S8b in which the goal cannot be attacked directly: atoms and `⊥`
always; `∨` when both disjuncts are refuted; `◯Z` when `Z` is refuted.
In each case a scan `findNotT (fun Y => decI Ψ (ante Y)) (impPart Ψ)`
looks for a context implication with an unrefuted antecedent; if there
is none (`hallI`), the store has the conclusion row by one of the
`gbuSucc*` lemmas (§5) and `hne` is contradicted; if there is one,
`fromImp` hands it to `limpStep`.

### 4.16 S8b(∧): a regular `∧`-goal

Anchor `search:581`, after `obtain ⟨h₁, h₂⟩ := sfR_and hC`.

```
case true.inl.and
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
hall : ∀ X ∈ Ψ, isHat X = true
hΩ : ∀ Y ∈ Ψ, Y ∈ gHat G
upsToImp : (∀ Y ∈ impPart Ψ, WEvalI D Ψ (ante Y)) → ∀ (A B : Form), A.imp B ∈ Ψ → WEvalI D Ψ A
C₁ C₂ : Form
hx : wgC G (true, Ψ, C₁.and C₂).1 (true, Ψ, C₁.and C₂).2.1 (true, Ψ, C₁.and C₂).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G true Ψ (C₁.and C₂)) → WSearchOk G D q
hC : C₁.and C₂ ∈ sfR G
hne : ¬WEvalR D Ψ (C₁.and C₂)
hax : C₁.and C₂ ∉ Ψ
limpStep : (A B : Form) → A.imp B ∈ Ψ → ¬WEvalI D Ψ A → GbuRC G Ψ (C₁.and C₂)
fromImp : (Y : Form) → Y ∈ impPart Ψ → ¬WEvalI D Ψ (ante Y) → GbuRC G Ψ (C₁.and C₂)
h₁ : C₁ ∈ sfR G
h₂ : C₂ ∈ sfR G
⊢ GbuRC G Ψ (C₁.and C₂)
```

The three helpers are now hypotheses, specialised to the goal
(`cases C` refined their types).  `R∧` needs both premises, each paid
by `seqSize` through the `wgKeep (fun _ h => .base h) (seqSize_goal …)`
incantation (the context is unchanged, so its coverage is trivial),
with the negative facts from `gbuInv2` (`WEvalR D Ψ C₁ ∨ WEvalR D Ψ C₂
→ WEvalR D Ψ (C₁ ∧ C₂)`, contraposed against `hne` with `Or.inl` and
`Or.inr`).  This is the state the run of §7 for `◯p ⊃ (◯p ∧ ◯p)`
passes through at its second cell.

### 4.17 S8b(⊃): a regular `⊃`-goal, antecedent not closure-available

Anchor `search:602`, on entry to the `¬ Clo Ψ A` branch.

```
case true.inl.imp.refine_2
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
hall : ∀ X ∈ Ψ, isHat X = true
hΩ : ∀ Y ∈ Ψ, Y ∈ gHat G
upsToImp : (∀ Y ∈ impPart Ψ, WEvalI D Ψ (ante Y)) → ∀ (A B : Form), A.imp B ∈ Ψ → WEvalI D Ψ A
A B : Form
hx : wgC G (true, Ψ, A.imp B).1 (true, Ψ, A.imp B).2.1 (true, Ψ, A.imp B).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G true Ψ (A.imp B)) → WSearchOk G D q
hC : A.imp B ∈ sfR G
hne : ¬WEvalR D Ψ (A.imp B)
hax : A.imp B ∉ Ψ
limpStep : (A_1 B_1 : Form) → A_1.imp B_1 ∈ Ψ → ¬WEvalI D Ψ A_1 → GbuRC G Ψ (A.imp B)
fromImp : (Y : Form) → Y ∈ impPart Ψ → ¬WEvalI D Ψ (ante Y) → GbuRC G Ψ (A.imp B)
hA : A ∈ sfL G
hB : B ∈ sfR G
hcl : ¬Clo Ψ A
⊢ GbuRC G Ψ (A.imp B)
```

The regular twin of S3.  `R⊃ₙ` puts `A` into the context, paid by
component 1 (`wgDrop (unclosed_lt hA hcl)`), with `gbuInv6` (`WEvalR D
(A :: Ψ) B → WEvalR D Ψ (A ⊃ B)`) contraposed for the premise's negative
fact; the sibling branch `hcl : Clo Ψ A` applies `R⊃` paid by
`seqSize`, with `gbuInv5`.  This is the FIRST step of both proof runs
in §7: at the root cell `(true, [], p ⊃ ◯p)` the antecedent `p` is not
in `Cl([])`, and the searcher moves to `(true, [p], ◯p)`.

(`limpStep`'s binders print as `A_1 B_1` because `A B` are now taken
by the goal's own halves: Lean's renaming, not a change of meaning.)

### 4.18 S8b(◯)-crit: a regular `◯Z` goal at a critical cell

Anchor `search:633`, after the `hΩai` block.

```
case true.inl.circ.inl
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
hall : ∀ X ∈ Ψ, isHat X = true
hΩ : ∀ Y ∈ Ψ, Y ∈ gHat G
upsToImp : (∀ Y ∈ impPart Ψ, WEvalI D Ψ (ante Y)) → ∀ (A B : Form), A.imp B ∈ Ψ → WEvalI D Ψ A
Z : Form
hx : wgC G (true, Ψ, Z.circ).1 (true, Ψ, Z.circ).2.1 (true, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G true Ψ Z.circ) → WSearchOk G D q
hC : Z.circ ∈ sfR G
hne : ¬WEvalR D Ψ Z.circ
hax : Z.circ ∉ Ψ
limpStep : (A B : Form) → A.imp B ∈ Ψ → ¬WEvalI D Ψ A → GbuRC G Ψ Z.circ
fromImp : (Y : Form) → Y ∈ impPart Ψ → ¬WEvalI D Ψ (ante Y) → GbuRC G Ψ Z.circ
hnoc : ∀ a ∈ Ψ, a.isCirc = false
hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G
⊢ GbuRC G Ψ Z.circ
```

The regular counterpart of S5: no modal member (`hnoc`; had there
been one, S8b(◯)-L◯ would have opened it), context atoms and
implications only.  The next line asks `decI Ψ Z`.  If `Z` IS refuted
(not shown, 635–638), the scan for an implication with unrefuted
antecedent runs; if all antecedents are refuted, `gbuSuccCirc` (§5)
says the store has the `◯Z`-row (the barren join `⋈^◯` fires) and
`hne` is contradicted; otherwise `fromImp` → `limpStep`.  If `Z` is
NOT refuted, S8b(◯)-R◯.

### 4.19 S8b(◯)-R◯: `Z` unrefuted, the release to irregular mode

Anchor `search:639`, on entry to the negative branch.

```
case true.inl.circ.inl.refine_2
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
hall : ∀ X ∈ Ψ, isHat X = true
hΩ : ∀ Y ∈ Ψ, Y ∈ gHat G
upsToImp : (∀ Y ∈ impPart Ψ, WEvalI D Ψ (ante Y)) → ∀ (A B : Form), A.imp B ∈ Ψ → WEvalI D Ψ A
Z : Form
hx : wgC G (true, Ψ, Z.circ).1 (true, Ψ, Z.circ).2.1 (true, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G true Ψ Z.circ) → WSearchOk G D q
hC : Z.circ ∈ sfR G
hne : ¬WEvalR D Ψ Z.circ
hax : Z.circ ∉ Ψ
limpStep : (A B : Form) → A.imp B ∈ Ψ → ¬WEvalI D Ψ A → GbuRC G Ψ Z.circ
fromImp : (Y : Form) → Y ∈ impPart Ψ → ¬WEvalI D Ψ (ante Y) → GbuRC G Ψ Z.circ
hnoc : ∀ a ∈ Ψ, a.isCirc = false
hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G
heZ : ¬WEvalI D Ψ Z
⊢ GbuRC G Ψ Z.circ
```

`R◯` with the IRREGULAR premise `Ψ →g Z`: the release from regular to
irregular mode, paid by component 2 (`wgFocus (fun _ h => .base h)`;
the context is unchanged).  The premise's negative fact is `heZ`
lifted by `unrefutedBelow_of_gHat hΩ`.  This is the SECOND step of the
run for `p ⊃ ◯p` in §7: at `(true, [p], ◯p)`, `p` is not refuted by
the store (it is in the context), so the searcher moves to `(false,
[p], p)`, where `ax` closes.

### 4.20 S8b(◯)-L◯: a modal member, `L◯`

Anchor `search:652`, after `hY'sf`.

```
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
hall : ∀ X ∈ Ψ, isHat X = true
hΩ : ∀ Y ∈ Ψ, Y ∈ gHat G
upsToImp : (∀ Y ∈ impPart Ψ, WEvalI D Ψ (ante Y)) → ∀ (A B : Form), A.imp B ∈ Ψ → WEvalI D Ψ A
Z : Form
hx : wgC G (true, Ψ, Z.circ).1 (true, Ψ, Z.circ).2.1 (true, Ψ, Z.circ).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G true Ψ Z.circ) → WSearchOk G D q
hC : Z.circ ∈ sfR G
hne : ¬WEvalR D Ψ Z.circ
hax : Z.circ ∉ Ψ
limpStep : (A B : Form) → A.imp B ∈ Ψ → ¬WEvalI D Ψ A → GbuRC G Ψ Z.circ
fromImp : (Y : Form) → Y ∈ impPart Ψ → ¬WEvalI D Ψ (ante Y) → GbuRC G Ψ Z.circ
Y : Form
hYc' : Y.isCirc = true
Y' : Form
x✝ : Y'.circ.isCirc = true
hYΨ : Y'.circ ∈ Ψ
hYc : ¬Y'.circ.isCirc = false
f : Focus Ψ Y'.circ
hY'sf : Y' ∈ sfL G
⊢ GbuRC G Ψ Z.circ
```

The regular `L◯`: focus on `◯Y'`, descend to `(true, Y' :: f.rest,
◯Z)` paid by `seqSize`, negative fact from `gbuInv11` (`WEvalR D (Y' ::
Ψ) C → WEvalR D (◯Y' :: Ψ) C`) transported across `f.ctxEq`, rule
`.lcirc d (hΨ _ hYΨ) f.ctxEq`.  Note `L◯` takes precedence over the
critical branch: the second scan runs BEFORE `decI Ψ Z` is consulted,
so a modal member is always opened first.  (On the strength law
`(p ⊃ ◯q) ⊃ (◯p ⊃ ◯q)`, which cannot be run end to end, this is the
step that opens `◯p` at the cell `(true, [◯p, p ⊃ ◯q], ◯q)`.)

### 4.21 S9: the non-critical regular cell

Anchor `search:662`, after `have f := focusCtx hXmem`.

```
case true.inr
⟨standing: G D hsat decI x ihW⟩
Ψ : List Form
C : Form
hx : wgC G (true, Ψ, C).1 (true, Ψ, C).2.1 (true, Ψ, C).2.2 = x
IH : (q : Bool × List Form × Form) → WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G true Ψ C) → WSearchOk G D q
hΨ : ∀ X ∈ Ψ, X ∈ sfL G
hC : C ∈ sfR G
hne : ¬WEvalR D Ψ C
hax : C ∉ Ψ
l r : List Form
X : Form
hsplit : Ψ = l ++ X :: r
hX : isHat X = false
hXmem : X ∈ Ψ
f : Focus Ψ X
⊢ GbuRC G Ψ C
```

`splitHatT` exhibited a non-`Ĝ` member `X` with a split `hsplit`; since
compaction item C.3 the split is used only to recover `hXmem` and the
member is then focused like every other (`f`), so `Ψ` stays a
variable.  `cases X` leaves `⊥` (`.lbot C (ctxEq_cons_self hXmem)`),
`∧` (`L∧`, paid by `f.lt2`, negative fact `gbuInv1`) and `∨` (`L∨`, two
descents paid by `f.lt1`, negative facts `gbuInv3L`/`gbuInv3R`).  These
are the paper's invertible left rules, applied eagerly before any
critical step, exactly as in GBU(G).

### 4.22 S10: the base call

Anchor `search:690`, on entry to `exact fun p => main _ p rfl`.

```
G : Form
D : WSeq → Prop
hsat : WSaturated G D
decI : (Ω : List Form) → (C : Form) → Decidable (WEvalI D Ω C)
main : (x : ℕ × ℕ × ℕ) → (p : Bool × List Form × Form) → wgC G p.1 p.2.1 p.2.2 = x → WSearchOk G D p
⊢ (p : Bool × List Form × Form) → WSearchOk G D p
```

The fixpoint has been closed: `main` holds at every measure value, and
the searcher at a cell `p` is `main (wgC G p.1 p.2.1 p.2.2) p rfl`.
This is the whole of `searchW`: one well-founded recursion, whose body
is the case analysis of S1–S9, with `totalityW` (§6) as its one
subroutine.

### 4.23 What the trace shows about the measure

Collecting the payments observed above (every recursive call of the
file, by the lemma that licenses it):

| component | licence | snapshots where it pays | count |
|---|---|---|---|
| 1 `unclosed` | `wgDrop (unclosed_lt …)` | S3 (`R⊃ₙᵢ`), S5a-ii's callback into the regular stratum, S8b(⊃) (`R⊃ₙ`) | 3 |
| 2 `tpC` | `wgFocus` | S8a (`L⊃`'s left premise), S8b `R∨ₖ` (not snapshotted), S8b(◯)-R◯ | 4 |
| 3 `seqSize` | `wgKeep` | everything else: S5a-ii(Der), S5b, S6, S7, S8a's right premise, S8b(∧), S8b(⊃)'s sibling, S8b(◯)-L◯, S9 | 19 |

One nuance the brief (§A.1 of the plan) records and the trace cannot
show: the licence names the worst case the lemma can prove, not the
component that actually drops at a given cell.  `wgKeep` goes through
`wgCCtx` (`wip/gbu_circ.lean:1664`), which case-splits on whether
`unclosed` happens to drop; if it does, components 2 and 3 are never
consulted.  On the run of §7 the `L◯` step is licensed by `wgKeep` but
the operative drop is component 1.  The `#eval` trace of §7 records
the operative drop separately.

---

## 5. How the two calculi meet at every cell (E.iii)

### 5.1 The shape of the argument

At every cell the searcher asks the store a question and, on a
negative answer, takes one `Gbu◯` step and recurses.  For that to be
sound, each recursive call needs a negative answer at ITS cell, and
that is obtained from the current one by contraposition of a lemma of
the form

    (the store refutes the premise sequent)  →  (the store refutes the conclusion sequent)

one per `Gbu◯` rule.  Contrapositively: if the conclusion is not
refuted, the premise is not refuted either, which is exactly the
hypothesis the recursive call needs.  These lemmas are the *inversion
bank*.  They are proved once each, and each proof is the same small
move: unpack the store's answer at the premise, take the DISPROOF it
stands for (`WSaturated.1`), apply one FRJW rule to it, and put the
result back (`WSaturated.2`).  So each inversion lemma is literally
the FRJW rule that mirrors one `Gbu◯` rule, stated as a fact about
the store.  That is the duality, one rule at a time.

The whole of `gbuInv5`, the `R⊃` clause (`wip/gbu_frjw_db.lean:116–126`):

```lean
/-- **(v)** `Ψ ⇒g B` with `A ∈ Cl(Ψ)` gives `Ψ ⇒g A⊃B`, through `⊃∈`. -/
theorem gbuInv5 (hsat : WSaturated G D)
    {Ψ : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hA : Clo Ψ A) (h : WEvalR D Ψ B) : WEvalR D Ψ (.imp A B) := by
  obtain ⟨t, Γ, hmem, hcl⟩ := h                       -- the store's row for B, with Cl(Γ) ⊇ Ψ
  obtain ⟨d⟩ := hsat.1 _ hmem                          -- its DISPROOF  d : t : Γ ⇒ B
  have hAΓ : Clo Γ A := clo_trans hcl hA               -- A ∈ Cl(Ψ) ⊆ Cl(Γ)
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg t Γ (.imp A B)) ⟨.impIn d hAΓ hgoal⟩  -- apply ⊃∈; the store has a subsumer
  match s', hsub with
  | .reg t' Γ' _, ⟨rfl, _, hΓ⟩ =>
      exact ⟨t', Γ', hs'mem, fun X hX => clo_mono hΓ (hcl X hX)⟩   -- the subsumer answers the query
```

Eleven lines, and the shape of every other member of the bank.  Read
against the rule figures of §1: the `Gbu◯` rule `R⊃` takes `Γ ⇒g B` to
`Γ ⇒g A ⊃ B` under `A ∈ Cl(Γ)`; the FRJW rule `⊃∈` takes `t : Γ ⇒ B`
to `t : Γ ⇒ A ⊃ B` under `A ∈ Cl(Γ)`.  Same premise, same conclusion,
same side condition, on the two sides of the duality.  Its twin
`gbuInv6` (`R⊃ₙ`, `db:129–139`) is the same with `A :: Ψ` in the
premise; the FRJW side needs no `⊃∉` rule for it, because `A` is in the
premise context and so in `Cl(Γ)`.

The bank is used in two ways at the sites, both visible in §4.

*As a closer* (nine sites): a scan or test comes back positive on
every branch, and the resulting store row contradicts the standing
negative fact:

    · exact absurd (gbuInv10 hsat hC he₁ he₂) hne            -- search:371, both disjuncts refuted

*As a payload* (fourteen sites): a recursive call's negative
hypothesis, obtained by contraposing the lemma against `hne`:

    hΨ hB (fun h => hne (gbuInv5 hsat hC hcl h))              -- search:600, the R⊃ premise

Matthew's remark that "creating and gathering the named inversion
lemmas is a strategy but maybe not a tactic" is exactly right, and the
stage-4 brief (§C.11–C.12) records the assessment: the bank is proved
once per rule and it IS the mathematics; the uniform consumption could
be wrapped in a `first`-over-the-bank tactic, but every site is
already one line, the named lemma at the site documents which clause
of the duality is used at which rule, and a twenty-branch `first`
would re-elaborate failing alternatives in a file already at 3.2M
heartbeats.  The one tactic-shaped piece that WAS worth building is
`findNotT`, the constructive scan that returns either the universal
fact or a witness.

### 5.2 The bank, in full

One row per member, with its file and the `searchW` sites (at
`b2f2525`) that consume it.  The files: `db` =
`wip/gbu_frjw_db.lean`, `circdb` = `wip/gbu_frjw_circdb.lean`,
`corner` = `wip/gbu_frjw_corner.lean`, `search` =
`wip/gbu_frjw_search.lean`.

| `Gbu◯` rule | lemma | statement (schematically; `hsat` and the `Sf^R` side conditions omitted) | file:line | consumed at |
|---|---|---|---|---|
| `L∧` | `gbuInv1` | `WEvalR D (A::B::Ψ) C → WEvalR D (A∧B::Ψ) C` | db:63–70 | search:675 (S9) |
| `R∧` | `gbuInv2` | `WEvalR D Ψ C₁ ∨ WEvalR D Ψ C₂ → WEvalR D Ψ (C₁∧C₂)` | db:99–113 | 586, 591 (S8b(∧)) |
| `L∨` (left) | `gbuInv3L` | `WEvalR D (A₁::Ψ) C → WEvalR D (A₁∨A₂::Ψ) C` | db:73–79 | 683 (S9) |
| `L∨` (right) | `gbuInv3R` | `WEvalR D (A₂::Ψ) C → WEvalR D (A₁∨A₂::Ψ) C` | db:81–87 | 688 (S9) |
| `L⊃` (right premise) | `gbuInv4` | `WEvalR D (B::Ψ) C → WEvalR D (A⊃B::Ψ) C` | db:90–96 | 556 (S8a) |
| `R⊃` | `gbuInv5` | `Clo Ψ A → WEvalR D Ψ B → WEvalR D Ψ (A⊃B)` | db:116–126 | 600 (S8b(⊃), `Clo` branch) |
| `R⊃ₙ` | `gbuInv6` | `WEvalR D (A::Ψ) B → WEvalR D Ψ (A⊃B)` | db:129–139 | 604 (S8b(⊃)) |
| `R∧ᵢ` | `gbuInv7` | `WEvalI D Ω C₁ ∨ WEvalI D Ω C₂ → WEvalI D Ω (C₁∧C₂)` | db:142–161 | 358, 364 (S3, `∧` case) |
| `R⊃ᵢ` | `gbuInv8` | `Clo Ω A → WEvalI D Ω B → WEvalI D Ω (A⊃B)` | db:165–211 | 393 (S3, `Clo` branch) |
| `R⊃ₙᵢ` | `gbuInv9` | `Ω ⊆ Ĝ → WEvalR D (A::Ω) B → WEvalI D Ω (A⊃B)` | db:216–230 | 398 (S3), 317 (inside `totalityW`) |
| `R∨ᵢ` (both) | `gbuInv10` | `WEvalI D Ω C₁ → WEvalI D Ω C₂ → WEvalI D Ω (C₁∨C₂)` | db:234–260 | 371 (S3, `∨` case), closer |
| `L◯` | `gbuInv11` | `WEvalR D (Z::Ψ) C → WEvalR D (◯Z::Ψ) C` | circdb:25–31 | 657 (S8b(◯)-L◯) |
| every irregular left rule | `gbuInv14`, through `unrefutedBelow_step` | `Ω ⊆ Ĝ → (∀ X ∈ Ω, Clo Ω' X) → WEvalI D Ω' (◯Z) → WEvalI D Ω (◯Z)` | circdb:418–469, 478–484 | 464, 489, 510, 522, 527 (S5a-ii(Der), S6, S7) |
| `R◯`/`R◯ᵢ` premise | `unrefutedBelow_of_gHat` (no lemma needed: the premise was decided directly) | `Ω ⊆ Ĝ → ¬ WEvalI D Ω C → WUnrefutedBelow G D Ω C` | circdb:472–475 | 357, 363, 376, 382, 472, 550, 617, 622, 643 |
| `ax` (irregular, negative) | `evalI_axI_gHat` | `Ω ⊆ Ĝ → F prime → F ∉ Ω → WEvalI D Ω F` | circdb:34–50 | 348, 349 (S2), 293 (inside `totalityW`), closers |
| the classical countermodel | `wEvalI_axIC` | a valuation over `Ĝ_at` forcing `Ω` and falsifying `F` gives the `Ax^I◯` row for `◯F` | search:233–247 | 418 (S5a), closer |
| `L⊃` exhausted, atom/`⊥` goal | `gbuSuccAtF` | `Ω ⊆ Ĝ → F prime, F ∉ Ω → (every antecedent refuted) → WEvalR D Ω F` | circdb:54–153 | 573, 578 (S8b atom/`⊥`), closers |
| `L⊃` exhausted, `∨` goal | `gbuSuccOrF` | the `∨` analogue | circdb:156–257 | 612 (S8b `∨`), closer |
| `L⊃` exhausted, `◯` goal | `gbuSuccCirc` | `Ω ⊆ Ĝ_at ∪ Ĝ_imp → (every antecedent refuted) → WEvalI D Ω Z → WEvalR D Ω (◯Z)` | circdb:385–392 | 637 (S8b(◯)-crit), closer |
| the corner's barren join | `refutedCleanly_circ_certs` with `wEvalR_of_refutedCleanly` and `gbuInvLift` | every antecedent refuted or certified over `Z :: R₀` → the `⋈^◯` row exists → lifted to the irregular query | corner:470–637; db:289–292; circdb:521–533 | 428–431 (S5a-i, `hallK` branch), closer |

Twenty-three members, thirty-nine consuming sites.  Three lemmas in
the same files are NOT consumed by the live chain and are archive,
not load-bearing: `gbuInv12`, `gbuInv13` (circdb:488–515, on the
pledged query `WEvalRP`, whose consumer left with `decRP` at
compaction stage 2) and `gbuSuccCircI` (circdb:400–412); likewise
`refutedCleanly_circ_kept` and `refutedCleanly_circ_axI` (corner:92,
251), banked results of the pre-totality corner.

### 5.3 Two clauses that read the other way

Two members of the bank are not of the "premise refuted ⇒ conclusion
refuted" shape and carry the two ideas the modal extension needed.

**The axiom clause** `evalI_axI_gHat` (circdb:34–50) says that an atom
or `⊥` that is NOT in a `Ĝ`-context is ALWAYS refuted by the store:
the `Ax^I` row `[] ; (Ĝ_at ∖ F) ++ Ĝ_imp ++ Ĝ_◯ → F` covers every
`Ĝ`-context not containing `F`.  This is why S2 closes the atom and
`⊥` cases outright, and, more importantly, why the atom case of
`totalityW` is a dilemma rather than a gap (§6.3): an atom is in the
context (derivable by `ax`) or it is not (refuted by this row).

**The success clauses** `gbuSuccAtF`, `gbuSuccOrF`, `gbuSuccCirc` say
that at a critical cell where EVERY context implication's antecedent
is refuted, the store has the conclusion row directly, by a barren
join: `⋈^At` for a prime goal, `⋈^∨` for a disjunction whose disjuncts
are refuted, `⋈^◯` for `◯Z` with `Z` refuted.  These are the largest
proofs in the bank (a hundred lines each) because they must assemble
the join's family from the stored rows of the antecedents and
discharge the join's side conditions (J1), (J2), the kept chain, and
the `RefAt` certificates.  They are the paper's `Search` procedure's
"no rule applies, so the database gains a row" step, made into a
lemma about an abstract saturated store.

### 5.4 The sibling branches, side by side

The clearest single picture of the meeting is the regular `⊃` case
(`search:593–605`), whose two branches are S8b(⊃) and its sibling:

```lean
| imp A B =>
    obtain ⟨hA, hB⟩ := sfR_imp hC
    refine byDec (decClo Ψ A) (fun hcl => ?_) (fun hcl => ?_)
    · have d := IH (true, Ψ, B)                              -- R⊃: same context, smaller goal
        (wgKeep (fun _ h => .base h) (seqSize_goal (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
        hΨ hB (fun h => hne (gbuInv5 hsat hC hcl h))        -- premise unrefuted, by ⊃∈
      exact .rimpI d hcl
    · have d := IH (true, A :: Ψ, B) (wgDrop (unclosed_lt hA hcl))   -- R⊃ₙ: A enters the context
        (forall_cons hA hΨ)
        hB (fun h => hne (gbuInv6 hsat hC h))                -- premise unrefuted, by ⊃∈ again
      exact .rimpNI d hcl
```

Two `Gbu◯` rules, two measure payments (component 3, then component
1), two bank lemmas, and in both the FRJW side is the single rule
`⊃∈`.  Every other case of §4 is this shape with different names.

---

## 6. The corner and `totalityW` (E.iv)

### 6.1 The cell shape nothing else handles

One cell shape resists the rule-by-rule walk of §5: irregular, goal
`◯Z`, every context member an atom or an implication (`Ψ ⊆ Ĝ_at ∪
Ĝ_imp`), and `Z` refuted by the store at `Ψ`.  That is the state of
snapshot S5a-i.  No right rule applies (`R◯ᵢ` needs `Z` unrefuted);
no left rule applies except `L⊃ᵢ`, modus ponens on a context
implication `A ⊃ B`, and `L⊃ᵢ`'s left premise `A ⊃ B, Ψ →g A` asks for
the ANTECEDENT to be derived first.  `A` is a right-signed subformula
of `G` of arbitrary size relative to `◯Z`, so no size argument reaches
it, and the paper's IPC calculus never meets the situation because
its irregular judgment has no `◯` goal.

On the store side the matching question is: can the store manufacture
a `◯Z`-row at `Ψ`?  The only rule that produces a barren `◯Z`-row
from irregular premises is `⋈^◯`, and `⋈^◯` retains a context
implication only when its antecedent is refuted at the new root
(condition (J2′) of §1.5, a `RefAt` certificate over the premises'
goals).  So the store can answer if and only if every context
implication's antecedent is refuted-or-certified; that is the
*certificate test* of S5a-i.  When every implication passes,
`refutedCleanly_circ_certs` builds the join and the cell is closed on
the store side (the `hallK` branch, search:428–433).  When one fails,
we have an implication `A₂ ⊃ B₂` whose antecedent `A₂` the store does
not refute and cannot certify, and the proof side must derive it.

### 6.2 Totality

The escape is a theorem found by trying to build a counterexample and
failing the same way every time (the history is in
`docs/searchw-architecture.md` §8–§9):

```lean
private def totalityW (hsat : WSaturated G D) (decI : ∀ Ω C, Decidable (WEvalI D Ω C))
    {Ψ : List Form} {Z : Form} {R₀ : List Form}
    (hg : ∀ X ∈ Ψ, X ∈ gHat G)
    (hR₀mem : ∀ X, X ∈ sfR G → WEvalI D Ψ X → X ∈ R₀)
    (reccall : ∀ A' B', Form.imp A' B' ∈ sfR G → ¬ Clo Ψ A' →
      ¬ WEvalR D (A' :: Ψ) B' → GbuRC G (A' :: Ψ) B') :
    ∀ X, X ∈ sfR G → RefAt true (Z :: R₀) Ψ X ⊕' GbuIC G Ψ X      -- search:278–285
```

In words: at a critical cell, for EVERY right-signed subformula `X` of
`G`, either `X` carries a refutation certificate over `Z :: R₀` (with
`R₀` the list of all forms the store refutes at `Ψ`, so `hR₀mem` says
"everything refuted is in `R₀`"), or `X` is `Gbu◯`-derivable at `Ψ`.
Applied to the failing antecedent `A₂` at S5a-ii: the certificate
branch is impossible (`hnK` says `A₂` has no certificate), so `A₂` is
derivable, `hDer` in S5a-ii(Der), and `L⊃ᵢ` steps through the
implication with the consequent recursion paid by `seqSize`.

The proof is STRUCTURAL on `X`, because the clauses of `RefAt`
(§1.5) and the irregular introduction rules of `Gbu◯` (§1.4) are De
Morgan duals:

| `X` | refuted (`RefAt` clause) | derivable (`Gbu◯` rule) |
|---|---|---|
| `⊥` | `.bot`, always | never needed |
| atom `a` | `.ups`: `a ∈ R₀` (the store refutes it) | `ax`: `a ∈ Ψ` |
| `C₁ ∧ C₂` | `.andL`/`.andR`: ONE side refuted | `R∧ᵢ`: BOTH sides derivable |
| `C₁ ∨ C₂` | `.or`: BOTH sides refuted | `R∨ₖᵢ`: ONE side derivable |
| `A' ⊃ B'` | `.ups`: refuted as a form; or `.imp`: `A' ∈ Cl(Ψ)` and `B'` refuted | `R⊃ᵢ`: `A' ∈ Cl(Ψ)` and `B'` derivable; `R⊃ₙᵢ`: `A' ∉ Cl(Ψ)` and `A', Ψ ⇒g B'` |
| `◯V` | `.circ`: `V` refuted (cone = true) | `R◯ᵢ`: `V` derivable |

Each row totalises: a child that fails one side supplies the other.
The `∧` and `∨` rows are exact complements; `◯` is a `◯`-free
question one level down; `⊥` is always refuted.  Two rows need a word.

### 6.3 The atom dilemma, quoted in full

```lean
  | .atom a, hX =>
      byDec (decI Ψ (.atom a))
        (fun hI => .inl (.ups (List.mem_cons_of_mem _ (hR₀mem _ hX hI))))     -- refuted: it is in R₀
        (fun hnI =>
          byDec (inferInstance : Decidable (Form.atom a ∈ Ψ))
            (fun hmem => .inr (.ax _ (ctxEq_cons_self hmem)))                 -- in the context: ax
            (fun hax => absurd (evalI_axI_gHat hsat hg rfl hX hax) hnI))     -- neither: impossible
```

(`search:287–293`).  If the store refutes `a`, the certificate is
`.ups` with `a ∈ R₀`.  If not, either `a ∈ Ψ` and `ax` derives it, or
`a ∉ Ψ`, and then the axiom clause of §5.3 says the store DOES refute
it (the `Ax^I` row covers every `Ĝ`-context without `a`), contradicting
the first test.  Four lines, and they are the reason the corner
closes: without `evalI_axI_gHat` there would be a third case, an atom
neither refuted nor derivable, and no rule to apply.

### 6.4 The one non-structural step, and the two-level picture

The `⊃` row's second alternative, `A' ∉ Cl(Ψ)`, needs `A', Ψ ⇒g B'`,
a REGULAR cell with a larger context.  Its measure is smaller than the
corner cell's by component 1 (`A'` is a new left-signed antecedent not
in `Cl(Ψ)`), but that is the ENCLOSING recursion's measure, not
structure on `X`.  So `totalityW` does not make that call itself; it
receives it as the parameter `reccall`, and the caller supplies it as
a closure over `IH` (`search:447–452`):

```lean
(fun A' B' hXsf hncl hnR =>
  IH (true, A' :: Ψ, B')
    (wgDrop (unclosed_lt (sfR_imp hXsf).1 hncl))     -- paid by component 1
    (forall_cons (sfR_imp hXsf).1 hΨ)
    (sfR_imp hXsf).2 hnR)
```

with the negative fact `hnR : ¬ WEvalR D (A' :: Ψ) B'` produced inside
`totalityW` by contraposing `gbuInv9` (the `R⊃ₙᵢ` clause of the bank,
`search:317`) against the store's non-refutation of `A' ⊃ B'`.

The picture, which the stage-4 brief calls the single most valuable
one in the explainer:

```
   ┌─────────────────────────────────────────────────────────────────┐
   │  searchW : well-founded on  wgC = (unclosed, tpC, seqSize)      │
   │                                                                 │
   │   S5a-ii: at the corner cell (false, Ψ, ◯Z), call               │
   │      ┌──────────────────────────────────────────────┐           │
   │      │  totalityW : structural on X : Form          │           │
   │      │     ⊥ / atom / ∧ / ∨ / ◯ : by the children   │           │
   │      │     A' ⊃ B' with A' ∉ Cl(Ψ) :  reccall ──────┼──┐        │
   │      └──────────────────────────────────────────────┘  │        │
   │                                                        │        │
   │   ◄────────────── IH (true, A' :: Ψ, B'), paid by unclosed      │
   │                                                                 │
   └─────────────────────────────────────────────────────────────────┘
```

Structural totality inside, with one arrow leaving the inner box and
re-entering the outer recursion at a strictly smaller measure.  The
inner recursion is on the formula, the outer on the cell; the
callback is the only place they touch, and it is paid by the one
measure component that can absorb a growing context.

### 6.5 What totality replaced

The corner was first closed by a *chase*: `L⊃ᵢ` into the failing
antecedent, with a visited-pair list `V` of (antecedent, goal) pairs
as a fourth measure component so that re-entering the same antecedent
under the same goal was blocked while re-entering it under a
different goal remained payable.  That apparatus (the `QD` partition,
the chase branch, `wgW_chase`, `V`, the side conditions `hVsf`/`hregV`)
was retired at compaction stages 2 and 3 once totality was in place,
each retirement with its supersession table (`docs/frjw-compaction.md`);
none of it is in the file at `b2f2525`, and §4's snapshots show the
measure with three components.  The history matters for one reason:
it is the record that the corner was not obvious.  Seven layers of
apparatus (`docs/searchw-architecture.md` §9) were built and each
bought one more class of cell before the structural totality was
found; the goal-set invariant of the sixth layer was the ladder that
produced the seventh, and was then found to have no consumer.

### 6.6 The store side of the corner

For completeness, the branch of S5a-i in which every implication
passes the certificate test (`search:428–433`):

```lean
· refine absurd (gbuInvLift hsat hg
    (wEvalR_of_refutedCleanly hsat
      (refutedCleanly_circ_certs hsat hΩai hC heZ hR₀ok ?_))) hne
  intro A B hAB
  exact hallK (.imp A B) (List.mem_filter.mpr ⟨hAB, rfl⟩)
```

`refutedCleanly_circ_certs` (`corner:470–637`) assembles the `⋈^◯`
join: its premises are the stored irregular rows for `Z` and for the
refuted antecedents, its kept chain is built level by level on the
size of the certificates' `Clo`-leaves (a certificate's leaves are
subformulas of its target, hence strictly smaller, so a level-by-level
construction always finds every leaf in place; `clo_sf_support`,
`corner:331`), and the (J2′) condition is discharged by the
certificates themselves.  `wEvalR_of_refutedCleanly` says the store
then answers the regular query for `◯Z` at `Ψ`, and `gbuInvLift`
(`Lift`, the rule FRJW added) turns that into the irregular answer
that contradicts `hne`.  So on the store side the corner is closed by
the modal join plus `Lift`; on the proof side by totality plus `L⊃ᵢ`;
and the certificate test is the fork between them.

---

## 7. Two runs through the loop, correlated with the proof states

### 7.0 Sources and what they certify

The search-state side of this section is `wip/frjw_trace.lean`
(commit `8c86301`), an `#eval`-only driver that (i) re-runs the
saturation one round at a time, printing each round's new rows with
the FRJW rule that produced them, (ii) runs the root scan
`rootDisproof?`, and (iii) prints the object `decideGbuWData G`
RETURNED, as a tree, by pattern-matching on it: a `Gbu◯` derivation
node prints as `rule | cell | wgC | guards`, an FRJW disproof node as
`rule | sequent`.  Its verbatim output is `wip/frjw_trace_out.txt`.
Two provisos.  The printed trees are the returned terms, nothing is
reconstructed; and the driver's round decomposition is certified
against `stepNew`'s definition by a kernel-checked `rfl` in the file
(`roundsEq`).  Everything else it prints is interpreter-level
evidence, tainting nothing and proving nothing; the pins are the
gates.  (The printer names the irregular axiom of `Gbu◯`, `GbuIC.ax`,
as `axI`.)

The proof-state side is §4 for `searchW` and, for the disproof run,
four further snapshots of the T-C induction (`tCr`/`tCi`,
`wip/gbu_frjw_closure.lean:1496–1676`), taken by the same method
(raw transcript: `docs/annotated/frjw-tC-transcript.txt`).

Both runs are at the bottom of the scale: `|Sf^R(G)| ≤ 3`, stores of
8 and 9 rows, 12 s each in the interpreter.

### 7.1 The proof run: `G = p ⊃ ◯p`

**The universe.**

    Sf^L G = [p]        Sf^R G = [p ⊃ ◯p, ◯p, p]        Ĝ = [p]

**The store, round by round** (`frjw_trace_out.txt`, `unit store`):

| round | emitted / fresh / stored | new rows |
|---|---|---|
| 1 | 3 / 3 / 3 | `barren : [] ⇒ p` (`Ax^R`); `[] ; [] → p` (`Ax^I`); `[] ; [] → ◯p` (`Ax^I◯`) |
| 2 | 19 / 11 / 4 | `barren : [] ⇒ ◯p` (`◯∈`); `blocked : [] ⇒ p` (`⋈^At_F`); `chain p : [] ⇒ p` (`⋈^At_P`); `chain p : [] ⇒ ◯p` (`⋈^◯_P`) |
| 3 | 44 / 9 / 1 | `chain ◯p : [] ⇒ p` (`⋈^At_P`) |
| 4 | 45 / 0 | fixpoint: 8 rows, identical to `closureDB G` |

("fresh" counts rows whose canonical key is new; "stored" is smaller
when several fresh rows share a key, since `insertNew` deduplicates
within the round.)  Read the rows against §1.5: `Ax^I`'s zone is
`(Ĝ_at ∖ p) ++ Ĝ_imp ++ Ĝ_◯ = []`; `Ax^I◯` fires with the empty
valuation, under which `p` is classically false and `vacZone = []`;
the disproofs of `◯p` at the EMPTY context (rounds 1 and 2) are
countermodels to `◯p` alone.  There is no regular row for the goal
`p ⊃ ◯p`, and there cannot be: to get one by `⊃∈` the store would
need a row for `◯p` whose context closure contains `p`, and every
`◯p`-row has context `[]`.

**The root scan**: `rootDisproof? = none`, so `decideOfStore` runs
`searchW` at `(true, [], p ⊃ ◯p)` with the negative fact
`rootDisproof?_none` supplies.

**The derivation returned**, as printed:

```
rimpNI | (reg, [], p ⊃ ◯p) | wgC=(1, 2, 4) | cloB Ψ p=false  Ψ⊆Ĝ=true  ◯∈Ψ=false  focus=-
  rcirc | (reg, [p], ◯p) | wgC=(0, 2, 3) | cloB=n/a  Ψ⊆Ĝ=true  ◯∈Ψ=false  focus=-
    axI | (irr, [p], p) | wgC=(0, 0, 2) | cloB=n/a  Ψ⊆Ĝ=true  ◯∈Ψ=false  focus=p
```

i.e. the `Gbu◯` derivation

```
    ────────── ax
     p →g p
    ────────── R◯   [◯p ∈ Sf^R(G)]
     p ⇒g ◯p
    ─────────── R⊃ₙ   [p ∉ Cl([])]
     ⇒g p ⊃ ◯p
```

**The correlation, cell by cell.**  Each row gives the cell, its
measure (from the trace), the snapshots of §4 the searcher passes
through at it, what the store answered, and the rule applied.

| step | cell | `wgC` | proof states passed (§4) | the store's answers | rule |
|---|---|---|---|---|---|
| 1 | `(true, [], p ⊃ ◯p)` | `(1, 2, 4)` | S0a with `x = (1,2,4)`; S0b; `cases reg` → S8 (`hne : ¬ WEvalR D [] (p ⊃ ◯p)`, true: no root row); `splitHatT []` → `hall` vacuously → S8-crit; `cases C` = `imp p (◯p)`; `decClo [] p` → `false` (the trace's `cloB Ψ p=false`) → S8b(⊃) | `WEvalR D [] (p ⊃ ◯p)`: no.  The premise's negative fact, by `gbuInv6` contraposed: were `[p] ⇒g ◯p` refuted, `⊃∈` would give a root row; the two stored `◯p`-rows have context `[]` and `p ∉ Cl([])`, so they do not answer `WEvalR D [p] ◯p` | `R⊃ₙ`, paid by component 1: `unclosed` 1 → 0 (`p` enters `Cl(Ψ)`) |
| 2 | `(true, [p], ◯p)` | `(0, 2, 3)` | S0b (fresh instance, `x = (0,2,3)`); S8 (`hax : ◯p ∉ [p]`); `splitHatT [p]` → `hall` (`p` is `Ĝ`-shaped) → S8-crit; `cases C` = `circ p`; the modal-member scan → `hnoc`; `hΩai` → S8b(◯)-crit; `decI [p] p` → `false` → S8b(◯)-R◯ | `WEvalI D [p] p`: no.  The only irregular `p`-row is `[] ; [] → p`, and `[p] ⊆ [] ++ []` fails.  So `heZ : ¬ WEvalI D [p] p`, lifted to the invariant by `unrefutedBelow_of_gHat` | `R◯`, paid by component 2: `tpC` 2 → 0 (regular → irregular with a `◯`-free goal); context unchanged |
| 3 | `(false, [p], p)` | `(0, 0, 2)` | S0b (`x = (0,0,2)`); `cases reg` = `false`; `intro hΨ hΩc hC hnb`; `byDec (p ∈ [p])` → positive: `.ax p (ctxEq_cons_self hax)`.  S2 is NOT reached | none needed | `ax` |

Three cells, three rules, and the three measure components in order:
component 1 pays the first descent, component 2 the second, and the
third cell is a leaf.  Note what the trace adds to §4: the snapshots
are generic in `Ψ`, `C`; the run says which branch each decision took
and why (`cloB [] p = false`; no `◯`-member; `p` unrefuted at `[p]`
because the store's `p`-rows all have empty zones).  Note also what
the two `◯p`-rows in the store are doing: they are the disproofs the
bank lemma `gbuInv6` would have used had the premise been refuted,
and their contexts are exactly why it was not.

### 7.2 The disproof run: `G = ◯p ⊃ p`

**The universe.**

    Sf^L G = [◯p, p]        Sf^R G = [◯p ⊃ p, p]        Ĝ = [p, ◯p]

**The store, round by round** (`circp_p store`):

| round | emitted / fresh / stored | new rows |
|---|---|---|
| 1 | 2 / 2 / 2 | `barren : [] ⇒ p` (`Ax^R`); `[] ; [◯p] → p` (`Ax^I`) |
| 2 | 7 / 4 / 4 | `[◯p] ; [] → ◯p ⊃ p` (`⊃∈ᵢ`); `[] ; [] → p` (`Lift`); `blocked : [◯p] ⇒ p` (`⋈^At_F`); `chain p : [] ⇒ p` (`⋈^At_P`) |
| 3 | 24 / 3 / 2 | **`blocked : [◯p] ⇒ ◯p ⊃ p` (`⊃∈`)**; `blocked : [] ⇒ p` (`⋈^At_F`) |
| 4 | 26 / 1 / 1 | `[] ; [◯p] → ◯p ⊃ p` (`Lift`) |
| 5 | 48 / 0 | fixpoint: 9 rows, identical to `closureDB G` |

Reading the rows.  Round 1: `Ax^I`'s zone is now `(Ĝ_at ∖ p) ++ Ĝ_imp
++ Ĝ_◯ = [◯p]`, so the axiom row says "a root refuting `p` may force
`◯p`".  Round 2: `⊃∈ᵢ` moves `◯p` from the `Θ`-zone to the stable zone
(`Λ = [◯p]`, `◯p ∈ Cl([] ++ [◯p])`) and puts `◯p` in front of `p`;
`Lift` turns the regular axiom row into an irregular one; the fallible
atomic join `⋈^At_F` with the single premise `[] ; [◯p] → p` makes the
REGULAR row `blocked : [◯p] ⇒ p` (tag `blocked`: no claim about the
root's modal cone, which is what a fallible join is); `⋈^At_P` with no
regular premises makes a `chain p` row at the empty context.  Round 3:
`⊃∈` applied to `blocked : [◯p] ⇒ p` with `◯p ∈ Cl([◯p])` gives the
ROOT ROW `blocked : [◯p] ⇒ ◯p ⊃ p`.  Rounds 4 and 5: one more `Lift`,
then nothing new.  The new rule `Lift` fires twice in this store
(rounds 2 and 4), though not inside the root's own disproof.

**The root scan**: `rootDisproof? = some`, tag `blocked`, `Γ = [◯p]`,
head rule `⊃∈`.  `decideOfStore` returns `.inr` at once; `searchW` is
never entered.  This is the asymmetry the stage-4 brief warns about:
a PLL-invalid formula is decided by the store alone, so it is the
wrong example for tracing the search and the right one for tracing
the saturation.

**The disproof returned**, as printed:

```
impIn | blocked : [◯p] ⇒ ◯p ⊃ p
  joinAtF[irr 1] | blocked : [◯p] ⇒ p
    · irr premise j=0
      axI | [] ; [◯p] → p
```

i.e. the FRJW disproof

```
    ─────────────────── Ax^I   [p prime;  Θ = (Ĝ_at ∖ p) ++ Ĝ_imp ++ Ĝ_◯ = [◯p]]
     [] ; [◯p] → p
    ─────────────────── ⋈^At_F   [one premise; p ∉ Ξ^at = []; (J1) vacuous; (J2) vacuous]
     blocked : [◯p] ⇒ p
    ───────────────────────── ⊃∈   [◯p ∈ Cl([◯p])]
     blocked : [◯p] ⇒ ◯p ⊃ p
```

By `soundnessW` this is a Kripke countermodel to `◯p ⊃ p`: a root
forcing `◯p` and refuting `p`.

**The correlation with the proof side.**  On the disproof side the
"proof loop" is the saturation, and the proof states that matter are
those of the theorems that certify the store, not of `searchW`.  Three
layers, for this tree:

1. *Each row carries its disproof.*  The emitters fire FRJW
   constructors at stored premises under `dite`-guards on the rule's
   side conditions, so `blocked : [◯p] ⇒ ◯p ⊃ p` is stored WITH the
   three-node term above as its `d` field; the printer read it off.
   No search, no reconstruction.
2. *The store is closed* (`closureDB_closed G : DBClosed G (closureDB
   G)`, `wip/gbu_frjw_saturate.lean:2354–2378`): for each of the 21
   FRJW rules, the rule fired at STORED premises has a stored subsumer.
   For this tree the three clauses used are `DBClosed.axI`,
   `DBClosed.joinAtF`, `DBClosed.impIn`, each discharged by the
   coverage lemma of its emitter (`cov_axI`, `cov_joinAtF`, `cov_impIn`)
   through `stored_of_emitted` and the pigeonhole `sat_fixed`.
3. *Closed implies complete up to subsumption* (`tC_of_closed`), by the
   T-C induction on the disproof.  For this tree the induction visits
   exactly the three cases below, innermost first.

The four T-C snapshots (method as §4; anchors
`wip/gbu_frjw_closure.lean`, at `b2f2525`; the `x✝` names are the
tag and context indices the pattern match left unnamed):

**`tCi`, case `axI`** (anchor `closure:1628`, on entry):

```
G : Form
db : List (WRow G)
hcl : DBClosed G db
x✝ : List Form
F : Form
hF : F.isPrime = true
hg : F ∈ sfR G
hTh : x✝ ≐ rm (gAt G) F ++ gImp G ++ gCirc G
⊢ ∃ r ∈ db, WSubsumes (WSeq.irr [] x✝ F) r.s
```

No premise, so no ascent: `hcl.axI F hF hg` gives the stored row for
`[] ; (Ĝ_at ∖ F) ++ Ĝ_imp ++ Ĝ_◯ → F` directly, and `downIrr (CtxEq.refl
_) hTh.subset` transports it to the `≐`-variant `x✝`.  On the run:
`F = p`, `x✝ = [◯p]`.

**`tCr`, case `joinAtF`** (anchor `closure:1547`, after the context
inclusion):

```
G : Form
db : List (WRow G)
hcl : DBClosed G db
x✝ : List Form
F : Form
n✝ : ℕ
stab th : Fin (n✝ + 1) → List Form
rhs : Fin (n✝ + 1) → Form
prem : (j : Fin (n✝ + 1)) → FRJWi G (stab j) (th j) (rhs j)
hJ1 : ∀ (i j : Fin (n✝ + 1)), i ≠ j → stab i ⊆ stab j ++ th j
hJ2 : ∀ (A B : Form), (A.imp B ∈ unionAll fun j => impPart (stab j)) → A ∈ upsilon rhs
hF : F.isPrime = true
hFnot : F ∉ unionAll fun j => atPart (stab j)
hg : F ∈ sfR G
hΓ : x✝ ≐ joinCtxAtF stab th rhs F
pk : IrrPick G db stab th rhs := irrPick ⋯
hsubctx : joinCtxAtF stab th rhs F ⊆ joinCtxAtF pk.stab' pk.th' rhs F
⊢ ∃ r ∈ db, WSubsumes (WSeq.reg Tag.blocked x✝ F) r.s
```

The ascent for a FAMILY of premises: `pk := irrPick (fun j => tCi hcl
(prem j))` packages, for every `j`, a stored subsumer of premise `j`
(`pk.stab'`, `pk.th'`, `pk.mem`, and the zone relations `pk.hst`,
`pk.hth`), skolemised without choice through `List.find?` over the
decidable subsumption test.  `hsubctx` is the T-B fact that the join's
context at the stored family contains the original's.  The `exact`
that follows refires `⋈^At_F` at the stored family
(`hcl.joinAtF pk.stab' pk.th' rhs F pk.mem …`), transferring (J1) and
(J2) across the premise swap with `hJ1_of_swap`, `hJ2_strict_of_swap`,
and descends with `downReg`.  On the run: `n✝ = 0`, one premise,
`stab 0 = []`, `th 0 = [◯p]`, `rhs 0 = p`, `F = p`, `x✝ = [◯p]`.

**`tCr`, case `impIn`, before and after the ascent** (anchors
`closure:1507` on entry, `closure:1508` after `regUp`):

```
G : Form
db : List (WRow G)
hcl : DBClosed G db
x✝¹ : Tag
x✝ : List Form
A B : Form
d : FRJWr G x✝¹ x✝ B
hA : Clo x✝ A
hg : A.imp B ∈ sfR G
⊢ ∃ r ∈ db, WSubsumes (WSeq.reg x✝¹ x✝ (A.imp B)) r.s
```

```
G : Form
db : List (WRow G)
hcl : DBClosed G db
x✝¹ : Tag
x✝ : List Form
A B : Form
d : FRJWr G x✝¹ x✝ B
hA : Clo x✝ A
hg : A.imp B ∈ sfR G
t' : Tag
Γ' : List Form
hmem : WSeq.reg t' Γ' B ∈ List.map (fun x => x.s) db
hle : tagLeB x✝¹ t' = true
hΓ : x✝ ⊆ Γ'
⊢ ∃ r ∈ db, WSubsumes (WSeq.reg x✝¹ x✝ (A.imp B)) r.s
```

Between the two: `regUp (tCr hcl d)`, the induction hypothesis at the
premise (the `joinAtF` node) unpacked into a stored subsumer `t' : Γ'
⇒ B` with `hle`, `hΓ`.  After: refire `⊃∈` at the subsumer,
`hcl.impIn t' Γ' A B hmem (clo_mono hΓ hA) hg` (the side condition `A
∈ Cl(x✝)` is transported to `Cl(Γ')` by monotonicity), and descend
with `downReg hle hΓ`.  On the run: `x✝¹ = blocked`, `x✝ = [◯p]`, `A =
◯p`, `B = p`, and the subsumer found is the round-2 row `blocked : [◯p]
⇒ p` itself (`t' = blocked`, `Γ' = [◯p]`).

So the disproof run's "loop" is: rounds 1–3 of the saturation
manufacture the tree bottom-up (`Ax^I` in round 1, `⋈^At_F` in round
2, `⊃∈` in round 3), the root scan finds the top node, and the T-C
induction, read top-down, is the proof that nothing derivable was
missed: each node's premise has a stored subsumer (`regUp`/`irrPick`),
the rule refired there is a `DBClosed` clause, and subsumption
transports the result back.

### 7.3 A second proof run: `G₂ = ◯p ⊃ (◯p ∧ ◯p)`

Included because it exercises the third measure component and the
axiom at a cell with a modal member.  Store: 5 rounds, 14 rows, root
scan `none`.  Derivation:

```
rimpNI | (reg, [], ◯p ⊃ ◯p ∧ ◯p) | wgC=(2, 2, 8) | cloB Ψ ◯p=false  Ψ⊆Ĝ=true  ◯∈Ψ=false  focus=-
  randR | (reg, [◯p], ◯p ∧ ◯p) | wgC=(1, 2, 7) | cloB=n/a  Ψ⊆Ĝ=true  ◯∈Ψ=true  focus=-
    ax | (reg, [◯p], ◯p) | wgC=(1, 2, 4) | cloB=n/a  Ψ⊆Ĝ=true  ◯∈Ψ=true  focus=◯p
    ax | (reg, [◯p], ◯p) | wgC=(1, 2, 4) | cloB=n/a  Ψ⊆Ĝ=true  ◯∈Ψ=true  focus=◯p
```

| step | cell | `wgC` | proof states (§4) | rule, payment |
|---|---|---|---|---|
| 1 | `(true, [], G₂)` | `(2, 2, 8)` | S8 → S8-crit → S8b(⊃), `cloB [] ◯p = false` | `R⊃ₙ`, component 1: 2 → 1 |
| 2 | `(true, [◯p], ◯p ∧ ◯p)` | `(1, 2, 7)` | S8 (`hax`: the goal is not in `[◯p]`); `splitHatT` → `hall` (`◯p` is `Ĝ`-shaped); S8-crit; `cases C` = `and` → S8b(∧) | `R∧`, component 3 twice: 7 → 4, with `gbuInv2` for both premises' negative facts |
| 3, 3′ | `(true, [◯p], ◯p)` | `(1, 2, 4)` | S0b; `cases reg` = `true`; `intro`; `byDec (◯p ∈ [◯p])` positive: `ax`.  S8 is NOT reached | `ax` |

At step 2 the modal member `◯p` is in the context but the goal is a
conjunction, so the `L◯` scan (which runs only under `cases C = circ`)
is never consulted; at step 3 the axiom test precedes every scan.
`unclosed` stays at 1 from step 2 on: `Sf^L G₂ = [◯p, p]`, and `p` is
never captured by `Cl([◯p])`.

### 7.4 What the runs certify, and what is reading

Checked by the runs (interpreter level): the per-round row sets and
rule names; the round counts (4, 5, 5) and store sizes (8, 9, 14); that
the driver's loop reaches a `stepNew`-empty fixpoint whose sequent
list equals `closureDB G`'s in all three cases; the root-scan verdicts;
which side `decideGbuWData` returned and the whole returned tree; the
`wgC` triples and guard columns, computed by the repository's own
`unclosed`, `tpC`, `seqSize`, `cloB`, `gHat`, `isCirc`.  Kernel-checked
in the trace file: `roundsEq`, that the driver's round decomposition
is `stepNew`'s definition.  Kernel-checked in the repository: every
statement of §1.7.

My reading, not established by any run: the "proof states passed"
columns (the correspondence between a trace row and the §4 snapshot
is by inspection of the branch conditions, which the guards column
makes checkable but does not itself assert); the attribution of each
drop to a lexicographic component; the causal glosses ("because the
store's `p`-rows have empty zones").

---

## 8. The complexity comparison with Fiorentini–Ferrari

The full comparison is `docs/frjw-complexity-comparison.md` (904
lines; the paper's arXiv source read directly, the IPC baseline
recovered at `05994d5`, every number with its method).  What follows
is its content in the form this document needs; the details, the
per-file tables and the sources are there.

### 8.1 The two fixed points

The paper: thirty printed pages for the duality route (§2–§5),
thirty-eight numbered items, ten FRJ(G) rule schemas and fourteen
GBU(G) rule schemas, two termination measures of three components
each.  The IPC mechanisation here (`05994d5`, nine files, 3712 lines):
FRJ(G) transcribed in twelve constructors, soundness and completeness
PROVED, with completeness taken by the paper's cheap §6 route (a
direct construction from a countermodel, 746 lines) rather than
through the duality, so GBU(G), the saturated database and `Search`
were never built for IPC.

### 8.2 What `◯` adds, by layer

| layer | IPC here | `◯` here | ratio | what forces it |
|---|---|---|---|---|
| syntax, closure, models | 1044 | 1298 + `RefAt` 510 | 1.7× | constraint models (`Rm`, fallible worlds), certificates |
| the disproof calculus | 191 (12 rules) | 374 (21 rules; definition closure ≈ 1610) | 2.0× | nine new rules: `◯∈`, `⋈^◯`, `⋈^◯_P`, `◯∉`, `Ax^I◯`, `Lift`, and the promise/fallible join pairs; tags, `Covers`, `RefAt`, `KeptChain` |
| soundness | 515 | 1906 | 3.7× | the modal cone, `tag_cone`, a second size induction inside the join case founded on `refAt_refutes_sf` |
| completeness of the disproof calculus | 746 (direct route) | 9954 (the whole duality: search 2671 + closure/saturation 4237 + `Gbu◯` 3046) | 13.3× | **the direct route is unavailable for `◯`** |
| the proof calculus | 523 (16 rules) | 2524 (24 rules) | 2.7× | `L◯`, `L◯ᵢ`, `R◯`, `R◯ᵢ`, `L⊃ᵢ` and the three `◯`-goal left rules |
| termination of backward search | ~70 lines | REFUTED for the naive extension, then re-won with the store | | `not_wf_stepC`: a two-cycle `Γ ⇒g Z ↦ Γ →g ◯Z ↦ Γ ⇒g Z` |

The single largest cost is the second-to-last row, and its cause is
the first thing to say about `◯`: the paper's cheap completeness
route is a triple induction on (height of the world, sequent phase,
goal size), and for `◯` no lexicographic order of those three works.
The `◯`-body edge (`I(◯Z) → R(Z)` at the same world, forced when the
root's cone is the root itself) needs regular-after-irregular; the
Υ-edge of the joins (antecedents of stable implications, of unbounded
size relative to the goal) needs irregular-before-regular; and the
call graph at a fixed world has the cycle `I(◯Z) → R(Z) → I(Y) →
I(◯Z)`.  The resolving order depends on the model, "and that is
precisely what saturation is" (`docs/frj-w4.md` §10).  This is a
documented argument, not a kernel-checked theorem (UNCERTAIN as a
formal claim; what would settle it is a `no_measure_stepC`-shaped
statement for the completeness visit's call relation).  What IS
kernel-checked on this route: the paper's theorem survives only under
a `◯`-freeness gate (`FRJ/Minimal.lean:483`), and the naive `◯`
extension of FRJ(G) is REFUTED outright (`frj_incompleteness_80/81`).

The other forcing facts are all kernel-checked and are listed in
§5.1 of the comparison: `no_measure_stepC` (no function of the
sequent, into any well-founded order, measures backward `Gbu◯`
search), `rcircNI_not_invertible` and `not_gbuR_omegaNI` (which put
`L⊃ᵢ` into the irregular judgment and so created the corner of §6),
`valid_neg_circ_bot_of_infallible` (fallible worlds are needed),
`no_irregular_circ_imp_self` (the hole that `Lift` fills).

### 8.3 The split of the modal development

At `b2f2525` the orbit is 39 567 lines, of which ≈ 34 730 are
`◯`-attributable (7.2× the IPC baseline of 4837).  By the
comparison's measurement (whole files assigned where a file has one
role, blocks measured where it does not, estimates flagged):

| bucket | lines | share |
|---|---|---|
| intrinsic to `◯` (rules and soundness 4051, `Gbu◯` and measure 3046, searcher and bank 2671, closure and saturation 4237) | ≈ 14 000 | ≈ 40% |
| formalisation overhead (lists not `Finset`s and the `≐` transports, `Fin` families and their reindexing, choice avoidance, the `Clo` decider) | ≈ 2 000 | ≈ 6%, a floor |
| historical residue (the FRJ◯ line's dead theorems, the superseded FRJV line, `searchO`, the store measure, the `_mono` archive, the corner's dead kit, the second completeness route) | ≈ 14 150 | ≈ 41% |
| unclassified (engine infrastructure, probes, the LJF◯ dependency) | ≈ 4 600 | ≈ 13% |

So Matthew's impression is supported by the numbers, and the reason
is not that the simplification failed.  Stages 1–3 and the C-items
cut the three core files from 5465 to 4962 lines and the search file
by 39%; what they did not touch is the larger residue, two superseded
calculi (16 633 lines together), a retired search apparatus and a
second completeness route, each retained for a stated reason (FRJ◯
is the subject of the #80/#81 incompleteness theorems; FRJV holds the
ρ12⊬ρ15 banked result and is imported by `gbu_search`; `searchO`
holds the `Gcc` countermodel; the LJF◯ route's independence is
evidence).  The intrinsic part, ≈ 14 000 lines, is 2.9× the whole IPC
baseline and 19× the IPC completeness proof; that, rather than the
7.2× headline, is what `◯` costs.  The comparison's recommendations
for readability, in order: separate the FRJ◯ and FRJV lines
physically into an archive subtree with pins intact (≈ 16 600 lines
out of the reader's way, no mathematical change, one supersession
check per file); promote the W-chain out of `wip/`; fix the stale
records it found (done at this commit: the "six new constructors"
docstring, the OPEN ledger rows for Theorems 8–10, the nine-vs-eleven
`_mono` count; the fourth, "Lemma 9 has 10 clauses", is checked in
§8.4); retire the corner's dead kit and `SaturateV` after their
checks.

### 8.4 One record checked against the source

The comparison reports that the paper's invertibility lemma
(`lemma:gbuInv`, the journal's Lemma 9) has nine clauses where the
ledger in `wip/gbu_circ.lean` said ten.  Checked against
`frj-corr.tex` (the label is at source line 3828; the enumerate that
follows carries `\item\label{lemma:gbuInv:1}` through
`\label{lemma:gbuInv:9}` and then `\end{enumerate}`): nine.  The
mechanisation's `gbuInv1`–`gbuInv10` are ten names because clause
(iii), the `∨`-left inversion, is split by disjunct into `gbuInv3L`
and `gbuInv3R`.  The ledger row is corrected at this commit.

## 9. What is not claimed

1. **A proof object, not a practical procedure.**  `decidePLL` and
   `decideGbuWData` compute, and `wip/decidepll_smoke_out.txt` records
   7/7 PASS on five formulas with `|Sf^R(G)| ≤ 3`, twice over.  They
   compute because `closureDB G` saturates the ENTIRE well-formed
   universe of `G` before any cell is searched, and that universe is
   exponential in `|Ĝ|`; the strength law `(p ⊃ ◯q) ⊃ (◯p ⊃ ◯q)`
   (`|Sf^R| = 5`) does not finish in eight minutes in the interpreter.
   A timeout is a FLAG, never a verdict.  Where the wall is has not
   been measured (UNCERTAIN; a fuelled sweep would settle it).
2. **No complexity claim of any kind**, upper or lower.
3. **The `#eval` evidence taints nothing and proves nothing.**  The
   `#guard_msgs` pins are the kernel gates; every trace and smoke file
   is labelled untrusted in its own header.
4. **PLL decidability is not new.**  What is new is the route: a
   constructive, choice-free decision object returning a proof or a
   disproof, without the finite model property.  The pins
   `[propext, Quot.sound]` with no `Classical.choice` are the evidence
   that this is not cosmetic.
5. **The `◯`-extension is ours; the duality is not.**  Fiorentini and
   Ferrari, ACM TOCL 21(3), 2020, for IPC.  Nothing is attributed to
   any paper this repository has not read.
6. **Two routes to `Gbu◯` completeness coexist on purpose**: the
   dichotomy (`gbuw_complete`) and the LJF◯ translation
   (`gbuC_complete`, `wip/gbu_ljfo.lean`); their independence is
   evidence, not redundancy (`docs/frjw-compaction.md`, deferred
   items).
7. **The snapshots of §4 are of the proof at `b2f2525`.**  The
   compaction may continue (the stage-4 brief lists further items);
   the anchors move with it, the names do not.

---

## 10. The syntactic bridge: the crown decides natural-deduction provability

*Added 2026-09-02 (late afternoon), on Matthew's instruction "prove the
FRJ.Kripke bridge to `finite_model_property` next".  Item 1 of §9 is
unchanged; item 4 is now sharper.*

### 10.1 What the crown's `PLL` is

`PLL` in the crown is semantic: `PLL A := ∀ K : Kripke, K.valid A`
(`FRJ/Basic.lean:567`), validity at the root of every `FRJ.Kripke`
model, and those are finite rooted POSETS (`le_antisymm` is a field)
with `Rm ⊆ ≤` and fallible worlds.  Natural-deduction provability,
`Nonempty (LaxND [] φ)` (`LaxLogic/PLLNDCore.lean:72`), is connected to
it in one direction by `FRJ.Bridge.valid_of_derivable`: a `LaxND`
theorem is valid in every `FRJ.Kripke`.  The other direction, from
semantic `PLL` to a derivation, is what makes `decidePLL` a decision
procedure for the logic rather than for a model class.

### 10.2 The FMP route, and why it was not taken

The finite model property on the LaxLogic side,

    finite_model_property : Nonempty (LaxND [] φ) ↔
        ∀ C : ConstraintModel, Finite C.W → ∀ w, C.force w φ     -- PLLFiniteModel.lean:288

gives, for an unprovable `φ`, a finite countermodel `C`.  To reach
`FRJ.PLL` one would have to present `C` as an `FRJ.Kripke`, and `C`'s
order is only a preorder (the filtration's `Ri` is inclusion of the
`T`-component alone, `PLLFiniteModel.lean:171`, and the canonical
model's order has the same shape).  The natural repair, quotienting by
`≤`-equivalence, does NOT preserve `◯`-forcing.  The witness is a
four-world constraint model, kernel-checked at `wip/quot_cm.lean`
(pins `[propext]`):

    worlds  b ≈ b'  (≤ both ways), both below t and t' (incomparable, maximal)
    Rm      reflexive, b → t, b' → t'
    V p     = {t, t'}

    fact1 : C4.Ri b b' ∧ C4.Ri b' b
    fact2 : C4.force b (◯p)
    fact3 : ¬ ∃ c, C4.Rm b c ∧ C4.Rm b' c ∧ C4.force c p

`b` forces `◯p` (each of `b, b', t, t'` has an `Rm`-successor forcing
`p`), but `b` and `b'` have no common `Rm`-successor forcing `p`, so in
the quotient the class `[b]` has no `Rm`-witness class at all under the
`∀∃` lift of `Rm` (the only lift that is transitive), and `[b]` refutes
`◯p`.  The quotient forces less than the model it came from; a
correspondence lemma cannot hold, and the implication clause needs the
correspondence in both directions.  Whether SOME finite poset model
always exists was, at that point, a genuine question; the route below
answers it as a corollary.

### 10.3 The route taken: `Gbu◯` is sound for natural deduction

Every rule of `Gbu◯(G)` (§1.4) is admissible in `LaxND`: the
intuitionistic rules are the natural-deduction rules under the
membership-based `iden`, `L⊃` is `⊃E` followed by a cut (`⊃I` then
`⊃E`), the `◯`-goal restriction of `L◯` is exactly `laxElim`'s
restriction (its conclusion is `◯ψ`), `R◯` is `laxIntro`, and the
`≐`-contexts are handled by `LaxND.rename`.  So there is a total
translation, constructor for constructor:

```lean
mutual
def laxOfR {G : Form} : ∀ {Γ : List Form} {C : Form},
    GbuRC G Γ C → LaxND (Γ.map toPLL) (toPLL C)
def laxOfI {G : Form} : ∀ {Γ : List Form} {C : Form},
    GbuIC G Γ C → LaxND (Γ.map toPLL) (toPLL C)
end                                                          -- wip/gbu_laxnd.lean

theorem laxND_of_provableGbuC (h : ProvableGbuC G) : Nonempty (LaxND [] (toPLL G))
```

24 cases, 150 lines, compiled first time, pinned `[propext, Quot.sound]`.
Composed with the dichotomy and FRJW soundness
(`wip/gbu_frjw_laxnd.lean`, all pinned `[propext, Quot.sound]`):

```lean
theorem laxND_of_PLL (h : PLL (ofPLL φ)) : Nonempty (LaxND [] φ)
  -- PLL ⟹ no FRJW disproof (soundnessW) ⟹ Gbu◯ proof (gbuw_complete) ⟹ LaxND (laxOfR)

theorem PLL_iff_laxND : PLL (ofPLL φ) ↔ Nonempty (LaxND [] φ)
theorem PLL_iff_laxND' : PLL A ↔ Nonempty (LaxND [] (toPLL A))

theorem finite_poset_model_property :
    Nonempty (LaxND [] φ) ↔ ∀ K : Kripke, K.valid (ofPLL φ)

def decideLaxND (φ : PLLFormula) : Decidable (Nonempty (LaxND [] φ))
  -- decidePLL (ofPLL φ) transported along PLL_iff_laxND
```

So the crown decides natural-deduction provability, choice-free, and
PLL has the finite POSET model property, which the filtration proof of
`finite_model_property` does not give.  The FMP bridge Matthew asked for
is therefore obtained, in the stronger form, from the syntactic side.

### 10.4 What this says about the LJF◯ route

`gbuC_complete : Nonempty (LaxND [] φ) → ProvableGbuC (ofPLL φ)`
(`wip/gbu_ljfo.lean:816`) is the direction natural deduction → `Gbu◯`
through focusing.  `laxND_of_provableGbuC` is its converse, `Gbu◯` →
natural deduction, by direct translation.  Together they are a
purely syntactic proof that `Gbu◯` characterises PLL, with no model in
sight; the dichotomy gives the same characterisation through the FRJ
models.  That is the partner Matthew asked for before the LJF◯ route
could be publishable: it exists, it is 150 lines, and it was the
missing direction all along.  The LJF◯ route itself stays in `wip/`,
as decided; it is not needed by the crown for anything, and this
bridge does not use it.
