import wip.p2llND
import wip.p2llJND

/-!
# The definability campaign: the statements that are OPEN

File 4 of the P2LL definability campaign (`wip/p2ll-STATUS.md`).  Each
statement below is a `def … : Prop` with NO proof (the `FRJO` pattern for OPEN
claims, `TOOLS.md`): a `sorry` would assert, and an open case is data, never a
sorried theorem (CLAUDE.md rule 1).  The cells already PROVED are in
`wip/p2llND.lean` (F1, C5, C7) and `wip/p2llJND.lean` (C1, C2, C3, F2); the
PLL-level refuter C6 is `wip/p2llOrCell.lean`.

Notation of the statements (plan §1.6, `wip/p2llSyntax.lean`):

    φ°  = toJ φ        ◯φ ↦ ∀°q.((φ° → q) → q)                (P2LL into the guarded calculus)
    φ*  = rel φ        ∀°.ψ ↦ ∀.((◯q → q) → ψ*)                (the guarded calculus into P2LL)
    G(Θ) = guards Θ    [◯s → s : s ∈ Θ]                       (the relativisation of the declarations)

The two interpretation theorems are the "derivability-preserving both ways";
the two round trips are the faithfulness of each translation; the two
biconditionals follow from them.  Proof routes are in `wip/p2ll-STATUS.md` §4.
-/

namespace P2LL

open Fm

/-- (I₁) P2LL interprets into the guarded calculus:

    Γ ⊢_P2LL φ   ⟹   Θ ; Γ° ⊢_J φ°   for every Θ.

Route: induction on the derivation; `laxIntro`/`laxElim` are C1/C2; `∀E`
needs `toJ (ψ.opn χ) = (toJ ψ).opn (toJ χ)` for locally closed `χ`, through
`shiftAt`.  OPEN. -/
def InterpToJ : Prop :=
  ∀ (Γ : List Fm) (φ : Fm), LaxND2 Γ φ →
    ∀ Θ : List String, Nonempty (JND IsJ Θ (Γ.map toJ) (toJ φ))

/-- (Fix) J-formulas denote fixed points:

    IsJ Θ χ,  LC χ   ⟹   G(Θ) ⊢_P2LL ◯χ* → χ*.

Route: induction on `IsJ`; the variable case is the guard, `⊤` is trivial,
`φ → J` and `J ∧ J` are PLL derivations, the binder cases use monotonicity of
`◯` and the cofinite `∀I`.  OPEN. -/
def FixOfIsJ : Prop :=
  ∀ (Θ : List String) (χ : Fm), IsJ Θ χ → LC χ →
    Nonempty (LaxND2 (guards Θ) (.imp (.circ (rel χ)) (rel χ)))

/-- (I₂) The guarded calculus interprets into P2LL:

    Θ ; Γ ⊢_J φ   ⟹   G(Θ), Γ* ⊢_P2LL φ*.

Route: induction on the derivation; `∀°I` is `∀I` plus `→I` on the new guard;
`∀°E` is `∀E` at `χ*` discharged by (Fix).  OPEN. -/
def InterpToP2LL : Prop :=
  ∀ (Θ : List String) (Γ : List Fm) (φ : Fm), JND IsJ Θ Γ φ →
    Nonempty (LaxND2 (guards Θ ++ Γ.map rel) (rel φ))

/-- (RTP) The round trip on the P2LL side, Proposition C generalised to every
formula by congruence:

    LC φ   ⟹   φ ⊢_P2LL (φ°)*   and   (φ°)* ⊢_P2LL φ.

The one-◯ instance is PROVED (C7, `LaxND2.circ_to_circNuc`,
`LaxND2.circNuc_to_circ`).  OPEN in general. -/
def RoundTripP2LL : Prop :=
  ∀ φ : Fm, LC φ →
    Nonempty (LaxND2 [φ] (rel (toJ φ))) ∧ Nonempty (LaxND2 [rel (toJ φ)] φ)

/-- (RTJ) The round trip on the guarded side:

    LC φ   ⟹   Θ ; φ ⊢_J (φ*)°   and   Θ ; (φ*)° ⊢_J φ.

Route: the `∀°` case instantiates at `◯°s` for a fresh plain `s` (a J-formula
by the `allJ` and `imp` clauses) and uses `◯°s ⊣⊢ s` under the hypothesis
`◯°s → s`; needs substitution of equivalents.  OPEN. -/
def RoundTripJ : Prop :=
  ∀ (Θ : List String) (φ : Fm), LC φ →
    Nonempty (JND IsJ Θ [φ] (toJ (rel φ))) ∧ Nonempty (JND IsJ Θ [toJ (rel φ)] φ)

/-- (MP) Mutual interpretability, seen from P2LL:

    Γ ⊢_P2LL φ   ⟺   [] ; Γ° ⊢_J φ°      (Γ, φ locally closed).

From (I₁), (I₂) and (RTP).  OPEN. -/
def MutualP2LL : Prop :=
  ∀ (Γ : List Fm) (φ : Fm), (∀ ψ ∈ Γ, LC ψ) → LC φ →
    (Nonempty (LaxND2 Γ φ) ↔ Nonempty (JND IsJ [] (Γ.map toJ) (toJ φ)))

/-- (MJ) Mutual interpretability, seen from the guarded calculus:

    Θ ; Γ ⊢_J φ   ⟺   G(Θ), Γ* ⊢_P2LL φ*      (Γ, φ locally closed).

From (I₂), (I₁) and (RTJ), discharging the translated guards `◯°s → s` by
`∀°E` at the declared `s`.  OPEN. -/
def MutualJ : Prop :=
  ∀ (Θ : List String) (Γ : List Fm) (φ : Fm), (∀ ψ ∈ Γ, LC ψ) → LC φ →
    (Nonempty (JND IsJ Θ Γ φ) ↔ Nonempty (LaxND2 (guards Θ ++ Γ.map rel) (rel φ)))

end P2LL

/-! The statements are definitions of propositions and carry no axioms; the
pins record that none of them is sorried. -/

#axioms_within P2LL.InterpToJ []
#axioms_within P2LL.FixOfIsJ []
#axioms_within P2LL.InterpToP2LL []
#axioms_within P2LL.RoundTripP2LL []
#axioms_within P2LL.RoundTripJ []
#axioms_within P2LL.MutualP2LL []
#axioms_within P2LL.MutualJ []
