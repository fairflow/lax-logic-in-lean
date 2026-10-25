import wip.p2llND
import wip.p2llJND

/-!
# The definability campaign: the seven statements

File 4 of the P2LL definability campaign (`wip/p2ll-STATUS.md`).  Each
statement below is a `def … : Prop`, its text fixed before any proof (the
`FRJO` pattern for OPEN claims, `TOOLS.md`): a `sorry` would assert, and an
open case is data, never a sorried theorem (CLAUDE.md rule 1).  Each docstring
records the status, PROVED (with the theorem name) or OPEN, and any change of
wording with its date.  The proofs of I₁, Fix, I₂ are `interpToJ`, `fixOfIsJ`,
`interpToP2LL` in `wip/p2llInterp.lean` (2026-10-24).  RTP, RTJ, MP, MJ were
first stated on 2026-10-24 over the whole shared formula type; that wording is
REFUTED (`wip/p2llBoolSem.lean`: each fails only on formulas outside the
fragment its calculus owns, status note §8) and was replaced on 2026-10-25
(Matthew's decision, status note §9) by the text below, with the fragment
hypotheses `allJFree` (P2LL side) and `circFree` (guarded side); the old
wording is kept in `wip/p2llBoolSem.lean` as `…Unrestricted`, the record of
the refutation.  The cells already PROVED are in `wip/p2llND.lean` (F1, C5,
C7) and `wip/p2llJND.lean` (C1, C2, C3, F2); the PLL-level refuter C6 is
`wip/p2llOrCell.lean`.

Notation of the statements (plan §1.6, `wip/p2llSyntax.lean`):

    φ°  = toJ φ        ◯φ ↦ ∀°q.((φ° → q) → q)                (P2LL into the guarded calculus)
    φ*  = rel φ        ∀°.ψ ↦ ∀.((◯q → q) → ψ*)                (the guarded calculus into P2LL)
    G(Θ) = guards Θ    [◯s → s : s ∈ Θ]                       (the relativisation of the declarations)

The two interpretation theorems are the "derivability-preserving both ways";
the two round trips are the faithfulness of each translation on its own
fragment; the two biconditionals follow from them.  Proof routes are in
`wip/p2ll-STATUS.md` §4 and §9.  All seven statements are about locally closed
formulas: every formula a derivation of either calculus concludes is locally
closed (`LaxND2.lc`, `JND.lc`), and the round trips and biconditionals assume
`LC` explicitly.
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
P2LL formula by congruence:

    LC φ,  allJFree φ   ⟹   φ ⊢_P2LL (φ°)*   and   (φ°)* ⊢_P2LL φ.

The one-◯ instance is PROVED (C7, `LaxND2.circ_to_circNuc`,
`LaxND2.circNuc_to_circ`).  Wording replaced 2026-10-25: the wording of
2026-10-24 lacked `allJFree φ` and is REFUTED (`RoundTripP2LLUnrestricted`,
`roundTripP2LL_false`, cells `rtp_fails₁`, `rtp_fails₂` in
`wip/p2llBoolSem.lean`).  OPEN. -/
def RoundTripP2LL : Prop :=
  ∀ φ : Fm, LC φ → allJFree φ →
    Nonempty (LaxND2 [φ] (rel (toJ φ))) ∧ Nonempty (LaxND2 [rel (toJ φ)] φ)

/-- (RTJ) The round trip on the guarded side:

    LC φ,  circFree φ   ⟹   Θ ; φ ⊢_J (φ*)°   and   Θ ; (φ*)° ⊢_J φ.

Route: the `∀°` case instantiates at `◯°s` for a fresh plain `s` (a J-formula
by the `allJ` and `imp` clauses) and uses `◯°s ⊣⊢ s` under the hypothesis
`◯°s → s`; needs substitution of equivalents.  Wording replaced 2026-10-25:
the wording of 2026-10-24 lacked `circFree φ` and is REFUTED
(`RoundTripJUnrestricted`, `roundTripJ_false`, cells `rtj_fails₁`,
`rtj_fails₂` in `wip/p2llBoolSem.lean`).  OPEN. -/
def RoundTripJ : Prop :=
  ∀ (Θ : List String) (φ : Fm), LC φ → circFree φ →
    Nonempty (JND IsJ Θ [φ] (toJ (rel φ))) ∧ Nonempty (JND IsJ Θ [toJ (rel φ)] φ)

/-- (MP) Mutual interpretability, seen from P2LL:

    Γ ⊢_P2LL φ   ⟺   [] ; Γ° ⊢_J φ°      (Γ, φ locally closed P2LL formulas).

From (I₁), (I₂) and (RTP).  Wording replaced 2026-10-25: the wording of
2026-10-24 lacked `allJFree` on `φ` and on `Γ` and is REFUTED
(`MutualP2LLUnrestricted`, `mutualP2LL_false`, cells `jd_allJ_refl`,
`mp_fails` in `wip/p2llBoolSem.lean`).  OPEN. -/
def MutualP2LL : Prop :=
  ∀ (Γ : List Fm) (φ : Fm), (∀ ψ ∈ Γ, LC ψ ∧ allJFree ψ) → LC φ → allJFree φ →
    (Nonempty (LaxND2 Γ φ) ↔ Nonempty (JND IsJ [] (Γ.map toJ) (toJ φ)))

/-- (MJ) Mutual interpretability, seen from the guarded calculus:

    Θ ; Γ ⊢_J φ   ⟺   G(Θ), Γ* ⊢_P2LL φ*      (Γ, φ locally closed guarded formulas).

From (I₂), (I₁) and (RTJ), discharging the translated guards `◯°s → s` by
`∀°E` at the declared `s`.  Wording replaced 2026-10-25: the wording of
2026-10-24 lacked `circFree` on `φ` and on `Γ` and is REFUTED
(`MutualJUnrestricted`, `mutualJ_false`, cells `pd_circ_top`, `mj_fails` in
`wip/p2llBoolSem.lean`).  OPEN. -/
def MutualJ : Prop :=
  ∀ (Θ : List String) (Γ : List Fm) (φ : Fm), (∀ ψ ∈ Γ, LC ψ ∧ circFree ψ) → LC φ → circFree φ →
    (Nonempty (JND IsJ Θ Γ φ) ↔ Nonempty (LaxND2 (guards Θ ++ Γ.map rel) (rel φ)))

end P2LL

/-! The statements are definitions of propositions and carry no axioms; the
pins record that none of them is sorried.  The pins of the PROOFS are in
`wip/p2llInterp.lean` and `wip/p2llRoundTrip.lean`, those of the REFUTATIONS
of the 2026-10-24 wording in `wip/p2llBoolSem.lean`. -/

#axioms_within P2LL.InterpToJ []
#axioms_within P2LL.FixOfIsJ []
#axioms_within P2LL.InterpToP2LL []
#axioms_within P2LL.RoundTripP2LL []
#axioms_within P2LL.RoundTripJ []
#axioms_within P2LL.MutualP2LL []
#axioms_within P2LL.MutualJ []
