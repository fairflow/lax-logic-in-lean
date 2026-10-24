import wip.p2llND
import wip.p2llJND

/-!
# The definability campaign: the seven statements

File 4 of the P2LL definability campaign (`wip/p2ll-STATUS.md`).  Each
statement below is a `def … : Prop`, its text fixed before any proof (the
`FRJO` pattern for OPEN claims, `TOOLS.md`): a `sorry` would assert, and an
open case is data, never a sorried theorem (CLAUDE.md rule 1).  Each docstring
records the status, PROVED (with the theorem name) or REFUTED (with the
refuting cell); the proofs live in `wip/p2llInterp.lean` (I₁, Fix, I₂:
`interpToJ`, `fixOfIsJ`, `interpToP2LL`, 2026-10-24) and the refutations in
`wip/p2llBoolSem.lean` (RTP, RTJ, MP, MJ as stated, 2026-10-24: each fails
only on formulas outside the fragment its calculus owns, see §8 of the status
note; the restricted statements are proposed there).  The cells already PROVED
are in `wip/p2llND.lean` (F1, C5, C7) and `wip/p2llJND.lean` (C1, C2, C3, F2);
the PLL-level refuter C6 is `wip/p2llOrCell.lean`.

Notation of the statements (plan §1.6, `wip/p2llSyntax.lean`):

    φ°  = toJ φ        ◯φ ↦ ∀°q.((φ° → q) → q)                (P2LL into the guarded calculus)
    φ*  = rel φ        ∀°.ψ ↦ ∀.((◯q → q) → ψ*)                (the guarded calculus into P2LL)
    G(Θ) = guards Θ    [◯s → s : s ∈ Θ]                       (the relativisation of the declarations)

The two interpretation theorems are the "derivability-preserving both ways";
the two round trips are the faithfulness of each translation; the two
biconditionals follow from them.  Proof routes are in `wip/p2ll-STATUS.md` §4.
All seven statements are about locally closed formulas: every formula a
derivation of either calculus concludes is locally closed (`LaxND2.lc`,
`JND.lc`), and the round trips and biconditionals assume `LC` explicitly.
-/

namespace P2LL

open Fm

/-- (I₁) P2LL interprets into the guarded calculus:

    Γ ⊢_P2LL φ   ⟹   Θ ; Γ° ⊢_J φ°   for every Θ.

Route: induction on the derivation; `laxIntro`/`laxElim` are C1/C2; `∀E`
needs `toJ (ψ.opn χ) = (toJ ψ).opn (toJ χ)` for locally closed `χ`, through
`shiftAt`.  PROVED: `interpToJ` (`wip/p2llInterp.lean`, by `toJD`), pin
`[propext]`. -/
def InterpToJ : Prop :=
  ∀ (Γ : List Fm) (φ : Fm), LaxND2 Γ φ →
    ∀ Θ : List String, Nonempty (JND IsJ Θ (Γ.map toJ) (toJ φ))

/-- (Fix) J-formulas denote fixed points:

    IsJ Θ χ,  LC χ   ⟹   G(Θ) ⊢_P2LL ◯χ* → χ*.

Route: induction on `IsJ`; the variable case is the guard, `⊤` is trivial,
`φ → J` and `J ∧ J` are PLL derivations, the binder cases use monotonicity of
`◯` and the cofinite `∀I`.  PROVED: `fixOfIsJ` (`wip/p2llInterp.lean`, by
`fixD`), pin `[propext]`. -/
def FixOfIsJ : Prop :=
  ∀ (Θ : List String) (χ : Fm), IsJ Θ χ → LC χ →
    Nonempty (LaxND2 (guards Θ) (.imp (.circ (rel χ)) (rel χ)))

/-- (I₂) The guarded calculus interprets into P2LL:

    Θ ; Γ ⊢_J φ   ⟹   G(Θ), Γ* ⊢_P2LL φ*.

Route: induction on the derivation; `∀°I` is `∀I` plus `→I` on the new guard;
`∀°E` is `∀E` at `χ*` discharged by (Fix).  PROVED: `interpToP2LL`
(`wip/p2llInterp.lean`, by `relD`), pin `[propext]`. -/
def InterpToP2LL : Prop :=
  ∀ (Θ : List String) (Γ : List Fm) (φ : Fm), JND IsJ Θ Γ φ →
    Nonempty (LaxND2 (guards Θ ++ Γ.map rel) (rel φ))

/-- (RTP) The round trip on the P2LL side, Proposition C generalised to every
formula by congruence:

    LC φ   ⟹   φ ⊢_P2LL (φ°)*   and   (φ°)* ⊢_P2LL φ.

The one-◯ instance is PROVED (C7, `LaxND2.circ_to_circNuc`,
`LaxND2.circNuc_to_circ`).  REFUTED AS STATED (`roundTripP2LL_false`,
`wip/p2llBoolSem.lean`): `φ` ranges over the whole shared formula type, and
at `φ := ∀°q.q` (`allJ (bvar 0)`), inert in P2LL, the first half fails
(`rtp_fails₁`); at `∀°q.(q → q)` the second half fails (`rtp_fails₂`).  The
intended statement restricts `φ` to `allJFree`; proposed in the status note
§8, not yet adopted. -/
def RoundTripP2LL : Prop :=
  ∀ φ : Fm, LC φ →
    Nonempty (LaxND2 [φ] (rel (toJ φ))) ∧ Nonempty (LaxND2 [rel (toJ φ)] φ)

/-- (RTJ) The round trip on the guarded side:

    LC φ   ⟹   Θ ; φ ⊢_J (φ*)°   and   Θ ; (φ*)° ⊢_J φ.

Route: the `∀°` case instantiates at `◯°s` for a fresh plain `s` (a J-formula
by the `allJ` and `imp` clauses) and uses `◯°s ⊣⊢ s` under the hypothesis
`◯°s → s`; needs substitution of equivalents.  REFUTED AS STATED
(`roundTripJ_false`, `wip/p2llBoolSem.lean`): at `φ := ◯⊥`, inert in the
guarded calculus, the first half fails (`rtj_fails₁`); at `◯⊤` the second
(`rtj_fails₂`).  The intended statement restricts `φ` to `circFree`; proposed
in the status note §8, not yet adopted. -/
def RoundTripJ : Prop :=
  ∀ (Θ : List String) (φ : Fm), LC φ →
    Nonempty (JND IsJ Θ [φ] (toJ (rel φ))) ∧ Nonempty (JND IsJ Θ [toJ (rel φ)] φ)

/-- (MP) Mutual interpretability, seen from P2LL:

    Γ ⊢_P2LL φ   ⟺   [] ; Γ° ⊢_J φ°      (Γ, φ locally closed).

From (I₁), (I₂) and (RTP).  REFUTED AS STATED (`mutualP2LL_false`,
`wip/p2llBoolSem.lean`): at `Γ := []`, `φ := ∀°q.(q → q)` the right side holds
(`jd_allJ_refl`) and the left fails (`mp_fails`).  The intended statement
restricts `Γ` and `φ` to `allJFree`; proposed in the status note §8. -/
def MutualP2LL : Prop :=
  ∀ (Γ : List Fm) (φ : Fm), (∀ ψ ∈ Γ, LC ψ) → LC φ →
    (Nonempty (LaxND2 Γ φ) ↔ Nonempty (JND IsJ [] (Γ.map toJ) (toJ φ)))

/-- (MJ) Mutual interpretability, seen from the guarded calculus:

    Θ ; Γ ⊢_J φ   ⟺   G(Θ), Γ* ⊢_P2LL φ*      (Γ, φ locally closed).

From (I₂), (I₁) and (RTJ), discharging the translated guards `◯°s → s` by
`∀°E` at the declared `s`.  REFUTED AS STATED (`mutualJ_false`,
`wip/p2llBoolSem.lean`): at `Θ := []`, `Γ := []`, `φ := ◯⊤` the right side
holds (`pd_circ_top`) and the left fails (`mj_fails`).  The intended statement
restricts `Γ` and `φ` to `circFree`; proposed in the status note §8. -/
def MutualJ : Prop :=
  ∀ (Θ : List String) (Γ : List Fm) (φ : Fm), (∀ ψ ∈ Γ, LC ψ) → LC φ →
    (Nonempty (JND IsJ Θ Γ φ) ↔ Nonempty (LaxND2 (guards Θ ++ Γ.map rel) (rel φ)))

end P2LL

/-! The statements are definitions of propositions and carry no axioms; the
pins record that none of them is sorried.  The pins of the PROOFS are in
`wip/p2llInterp.lean`, those of the REFUTATIONS in `wip/p2llBoolSem.lean`. -/

#axioms_within P2LL.InterpToJ []
#axioms_within P2LL.FixOfIsJ []
#axioms_within P2LL.InterpToP2LL []
#axioms_within P2LL.RoundTripP2LL []
#axioms_within P2LL.RoundTripJ []
#axioms_within P2LL.MutualP2LL []
#axioms_within P2LL.MutualJ []
