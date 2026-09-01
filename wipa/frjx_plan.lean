/-
# FRJX — the plan: completeness of `Gbu◯(G)` for PLL

Campaign FRJX, branch `FRJX`.  **STAGE 1: statements only.**  Every theorem
below is `sorry`ed and therefore ASSERTED; none is proved, and none may be
built on until Matthew has reviewed the statements.

## The route

On the `◯`-free fragment completeness of `Gbu(G)` is already machine-checked,
and its shape is

    soundnessV                    :  a FRJV disproof of G  →  ¬ PLL G
    provableGbu_of_not_provableV  :  no FRJV disproof of G  →  Gbu(G) proves G

so `PLL G → ProvableGbu G` by composition.  The modal case fails at exactly
one point: FRJV has no IRREGULAR disproof of `◯(◯Z ⊃ Z)`
(`no_irregular_circ_imp_self`), while `Gbu◯` cannot prove `∅ →g ◯(◯p ⊃ p)`
either and must not (`not_gbuIC_Gcc`).  Both sides of the irregular duality
are empty, and `searchO`'s two supplies are jointly unsatisfiable in
consequence (`residues_unsatisfiable`).

FRJX closes that hole with ONE extra clause on DERIVABILITY, `(Lift)`:

    Γ ⇒ C        Θ ⊆ Ĝ,  Θ ⊆ Cl(Γ)
    ────────────────────────────────
              ∅ ; Θ → C

## Screening already done, before this plan was written

A first draft made `(Lift)` a closure property of the DATABASE and kept
`Saturated G D`.  That is refuted — `not_saturated_liftClosed` in
`wip/frjx_screen.lean`, `[propext, Quot.sound]`.  `Saturated` carries
`IsDatabase`, so every member must be FRJV-derivable; saturation forces a
regular row for `Gcc = ◯(◯p ⊃ p)`, lift-closure then forces the irregular
row `∅ ; ∅ → Gcc`, and no such FRJV disproof exists.  Keeping `Saturated`
unchanged would have been `CleanReg` again, one level up.

So `(Lift)` extends derivability.  It does NOT need a new inductive
CALCULUS: it is enough to extend the derivable-sequent predicate, which is
six lines and leaves `FRJVr`/`FRJVi` untouched.

## The cost, stated up front

`Saturated G D` is replaced by `SaturatedOver (LiftClosure G) D`, and every
existing lemma indexed by `Saturated` must be re-proved over it.  The port
surface is about fifteen lemmas — `gbuInv2/5/6/7/8/9/10`,
`refutedCleanly_at/_or/_circ`, `gbuSuccCirc/AtF/OrF`, `evalI_axI`,
`unrefutedBelow_of_gHat`.  §2 is the single inversion lemma that makes each
port mechanical; if §2 is awkward the whole plan should be re-scoped before
Stage 2 begins.
-/
import wip.gbu_search_circ
import wipa.frjx_screen

namespace FRJ.Gbu.X

open FRJ FRJ.Gbu

/-! ## §0 The extension

`LiftClosure G` is the least extension of `FDerivable G` closed under
`(Lift)`.  `SaturatedOver` is `Saturated` with its base relation made a
parameter — the ONLY change, and the one `not_saturated_liftClosed` forces. -/

/-! ## §1 Anti-vacuity — discharge this FIRST

Four statements.  Together they say the hypotheses of every theorem below
are jointly satisfiable, which is what `CleanReg` and the refuted first
draft both failed.  If any of the four is false the campaign stops and that
is the result. -/

-- (X1) `liftClosure_reg` is PROVED in `wip/frjx_screen.lean` — the screen
-- needed it, so it is banked rather than planned.

/-- **(X2)** The closure is regular-sound — by `(X1)` and `lemma39R`, which
extracts a model from an FRJV regular disproof. -/
theorem regSound_liftClosure (G : Form) : RegSound (LiftClosure G) := by
  sorry

/-- **(X3)** The closure is saturated over itself; `Subsumes` is reflexive,
so this is where the parametrisation pays. -/
theorem saturatedOver_liftClosure (G : Form) :
    SaturatedOver (LiftClosure G) (LiftClosure G) :=
  saturatedOver_self G

/-- **(X4)** …and lift-closed, by the `lift` constructor. -/
theorem liftClosed_liftClosure (G : Form) :
    ∀ (Γ Θ : List Form) (C : Form), LiftClosure G (.reg Γ C) →
      (∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) → LiftClosure G (.irr [] Θ C) :=
  fun _ _ _ hreg hΘ => .lift hreg hΘ

/-! ## §2 The inversion that makes the ports mechanical

Every existing lemma indexed by `Saturated` extracts an `FRJVi` from an
irregular member.  Over `LiftClosure` an irregular member is EITHER an FRJV
disproof as before OR a lifted regular one, and in the second case the
regular disproof is available.  One lemma, fifteen ports. -/

/-- **(X5)** Inversion of an irregular row of the closure. -/
theorem liftClosure_irr {G : Form} {St Th : List Form} {C : Form}
    (h : LiftClosure G (.irr St Th C)) :
    Nonempty (FRJVi G St Th C) ∨
      (St = [] ∧ ∃ Γ, FDerivable G (.reg Γ C) ∧
        ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G) := by
  sorry

/-! ## §3 What the repair buys

`(X6)` is the whole payoff; §3.2 and §3.3 are its corollaries and were the
search's two unmet needs. -/

/-- **(X6)** Over a `Ĝ`-context, `(Lift)` makes irregular disprovability at
least as strong as regular disprovability.  Take `Θ := Ω`; the zone
conditions `∅ ⊆ Ω ⊆ ∅ ++ Ω` are immediate. -/
theorem evalI_of_evalR {G : Form} {D : FSeq → Prop}
    (hlift : ∀ (Γ Θ : List Form) (C : Form), D (.reg Γ C) →
      (∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) → D (.irr [] Θ C))
    {Ω : List Form} {C : Form} (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (h : EvalR D Ω C) : EvalI D Ω C := by
  sorry

/-- **(X7) `(∨-inv)`.**  If both disjuncts are regularly disprovable over a
critical context with dead antecedents, so is the disjunction — `⋈^∨` on the
two lifted premises.  There was no route to this before: the `∨`-joins take
irregular premises. -/
theorem evalR_or {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : ∀ (Γ Θ : List Form) (C : Form), D (.reg Γ C) →
      (∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) → D (.irr [] Θ C))
    {Ω : List Form} {C₁ C₂ : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G) (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (h₁ : EvalR D Ω C₁) (h₂ : EvalR D Ω C₂) : EvalR D Ω (.or C₁ C₂) := by
  sorry

/-- **(X8) `(★)`.**  Lemma 9 clause 12, restricted.  The unrestricted clause
is refuted (`rcirc_not_invertible`) but its counterexample carries a `◯` in
the context, so it does not reach a critical `◯`-free one.  By `(X6)` then
`gbuSuccCirc`. -/
theorem evalR_circ {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : ∀ (Γ Θ : List Form) (C : Form), D (.reg Γ C) →
      (∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) → D (.irr [] Θ C))
    {Ω : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G) (hgoal : Form.circ Z ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (h : EvalR D Ω Z) : EvalR D Ω (.circ Z) := by
  sorry

/-! ## §4 The search

Three modes as in `searchO`, but the clean mode's query is the PLAIN regular
one, `¬ D ▷ (Ω ⇒g C)`.  That is strictly stronger than the clean query
`searchO` carried, and `(X7)`/`(X8)` are what make it propagable.

The `irr` clause keeps `UnrefutedBelow` unchanged.  Strengthening it to
carry `¬ EvalR` too is NOT possible — the `∨` entry from the regular mode
cannot supply it — and is not needed: the critical modal cell is the `cirr`
mode's job. -/

def SearchOkX (G : Form) (D : FSeq → Prop) : Mode × List Form × Form → Prop
  | (.reg, Ψ, C) =>
      (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G → ¬ EvalR D Ψ C → Nonempty (GbuRC G Ψ C)
  | (.irr, Ω, C) =>
      (∀ X ∈ Ω, X ∈ sfL G) → (C.isCirc = false → ∀ X ∈ Ω, X ∈ gHat G) →
        C ∈ sfR G → UnrefutedBelow G D Ω C → Nonempty (GbuIC G Ω C)
  | (.cirr, Ω, C) =>
      (∀ X ∈ Ω, X ∈ gAt G ++ gImp G) → C ∈ sfR G →
        (∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A) →
        ¬ EvalR D Ω C → Nonempty (GbuIC G Ω C)

/-! ### §4.1 The clean mode, one statement per goal shape -/

/-- **(X9)** Prime goal: a critical context with dead antecedents regularly
disproves every prime formula not in it, so the case closes by contradiction
and never recurses. -/
theorem cirr_prime {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {C : Form} (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hp : C.isPrime = true) (hgoal : C ∈ sfR G) (hax : C ∉ Ω)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A) : EvalR D Ω C := by
  sorry

/-- **(X10)** `∧`: the query propagates to both conjuncts (port of
`gbuInv2`). -/
theorem cirr_and {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {C₁ C₂ : Form} (hgoal : Form.and C₁ C₂ ∈ sfR G)
    (h : ¬ EvalR D Ω (.and C₁ C₂)) : ¬ EvalR D Ω C₁ ∧ ¬ EvalR D Ω C₂ := by
  sorry

/-- **(X11)** `⊃` with the antecedent closed by the context: propagates to
the consequent (port of `gbuInv5`). -/
theorem cirr_imp_clo {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (hA : Clo Ω A) (h : ¬ EvalR D Ω (.imp A B)) : ¬ EvalR D Ω B := by
  sorry

/-- **(X12)** `⊃` with the antecedent NOT closed: propagates to the REGULAR
mode at `A :: Ω` (port of `gbuInv6`).  This is the case that needed the
refuted supply `CleanReg`; carrying the plain regular query removes it. -/
theorem cirr_imp_notClo {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {A B : Form} (hgoal : Form.imp A B ∈ sfR G)
    (h : ¬ EvalR D Ω (.imp A B)) : ¬ EvalR D (A :: Ω) B := by
  sorry

/-- **(X13)** `◯`: the premise of `rcircI` is IRREGULAR and `gbuSuccCirc`
transfers the query to it, so the goal returns to the `irr` mode with
`UnrefutedBelow` intact.  (Proved on `frj-dev` as `cirr_circ_to_irr` over
`Saturated`; this is its port.) -/
theorem cirr_circ {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D)
    {Ω : List Form} {Z : Form} (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.circ Z ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (hne : ¬ EvalR D Ω (.circ Z)) : UnrefutedBelow G D Ω Z := by
  sorry

/-! ### §4.2 The residue that was NOT a residue

`(X14)` stood here: at a critical context whose implication has an
undisproved, `◯`-carrying, oversized antecedent, `Ω →g ◯Z` is derivable.
It is **REFUTED** — `not_X14` in `wipx/frjx_screen.lean`,
`[propext, Quot.sound]` — and so is its natural correction ("the node is
never reached"), by the same cell at `Z := p`.

No statement replaces it, because none is needed: the node is discharged by
`R◯ᵢ` then `Ax` (`gbuIC_omegaX_circp`).  The `hsz` residue was an artefact
of `searchO` trying the `Υ` queries BEFORE the right rules; reversing that
order removes it.  No rule changes. -/

/-! ## §5 The search, and completeness -/

/-- **(X15) Theorem 8X** — the modal search over a saturated lift-closed
database, with NO named supplies.  This is the theorem `searchO` should have
been. -/
theorem searchX {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : ∀ (Γ Θ : List Form) (C : Form), D (.reg Γ C) →
      (∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) → D (.irr [] Θ C))
    (decI : ∀ Ω C, Decidable (EvalI D Ω C))
    (decR : ∀ Ψ C, Decidable (EvalR D Ψ C)) :
    ∀ p : Mode × List Form × Form, SearchOkX G D p := by
  sorry

/-- **(X16)** The root instance. -/
theorem provableGbuC_of_not_evalR {G : Form} {D : FSeq → Prop}
    (hsat : SaturatedOver (LiftClosure G) D)
    (hlift : ∀ (Γ Θ : List Form) (C : Form), D (.reg Γ C) →
      (∀ X ∈ Θ, Clo Γ X ∧ X ∈ gHat G) → D (.irr [] Θ C))
    (decI : ∀ Ω C, Decidable (EvalI D Ω C))
    (decR : ∀ Ψ C, Decidable (EvalR D Ψ C))
    (hroot : ¬ EvalR D [] G) : ProvableGbuC G := by
  sorry

/-- **(X17)** Regular soundness turns validity into the root hypothesis. -/
theorem not_evalR_of_pll {G : Form} {D : FSeq → Prop} (hsound : RegSound D)
    (h : PLL G) : ¬ EvalR D [] G := by
  sorry

/-- **(X18) THE TARGET.**  `Gbu◯(G)` is complete for PLL.  Composes
`(X17)` with `(X16)` at the database `(X2)`–`(X4)` supply; the decidability
hypotheses are expected to cost `Classical.choice`, which is acceptable for
a metatheorem and will be reported, not hidden. -/
theorem gbuC_complete {G : Form}
    (decI : ∀ Ω C, Decidable (EvalI (LiftClosure G) Ω C))
    (decR : ∀ Ψ C, Decidable (EvalR (LiftClosure G) Ψ C))
    (h : PLL G) : ProvableGbuC G := by
  sorry

/-- **(X19)** With soundness (`pll_of_provableGbuC`, already proved) the
campaign's end state is one displayed equivalence. -/
theorem gbuC_iff_pll {G : Form}
    (decI : ∀ Ω C, Decidable (EvalI (LiftClosure G) Ω C))
    (decR : ∀ Ψ C, Decidable (EvalR (LiftClosure G) Ψ C)) :
    ProvableGbuC G ↔ PLL G := by
  sorry

end FRJ.Gbu.X
