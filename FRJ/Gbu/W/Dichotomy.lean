/-
# The Gbu◯ / FRJW dichotomy — the STATEMENT layer

Drafted 2026-09-01 and approved by Matthew with one revision folded in:
the regular database sequent carries its `Tag` EXPLICITLY (his call:
"might it not be useful to have t as an explicit parameter so you can
branch on it if needed?").  The tagless first draft was in fact
defective: the manufacture lemmas for `◯∈`/`◯∉` and the promise joins
need a TAG-AWARE (DB2), which an existentially buried tag cannot
express — the old design's `regC` stratum was the workaround, and the
explicit tag dissolves it.  `WSubsumes` follows the engine's retention
order `tagLeB` (blocked ≤ chain D ≤ barren), so the abstract database
and `wOps`'s fixpoint share one subsumption relation.

STATUS: statement only.  The target theorems are OPEN and get NO
declaration here (a sorry ASSERTS):

    searchW : WSaturated G D → (∀ Ω C, Decidable (WEvalI D Ω C)) →
              ∀ p : Bool × List Form × Form, WSearchOk G D p

(TYPE-valued after Matthew's 2026-09-01 approval: `searchW` is a `def`
delivering derivations, not a `Nonempty` certificate)

with NO further hypotheses — the ◯-free Theorem 8 shape, the
`SearchOkO` reg/irr clauses verbatim, and neither of the old supplies:
(S1) `BigAnte` is dissolved by the licenced `L⊃ᵢ` adaptation (every
left-context implication has its antecedent in `Sf^R G` by signed
closure), and (S3) `CleanReg` disappears with the clean mode (`Lift` is
tag-free, so the `R⊃ₙᵢ` release goes to the PLAIN regular mode; the
◯-goal hand-off was already `cirr_circ_to_irr`).  Root corollary:

    gbu_frjw_dichotomy : … → ProvableGbuC G ∨ DisprovableW G

exclusive by `FRJ/Gbu/W/Exclusion.lean`; the Type-level
`decideGbuW : ∀ G, ProvableGbuC G ⊕ DisprovableW G` further needs the
engine-completeness lemma (`wOps` saturation reaches a `WSaturated`
fixpoint with decidable queries) — deliberately not part of this layer.

Screening protocol before any proof build: `lake exe wscreen`
(`tools/WScreen.lean`) — on every PLL-invalid cell the engine's
database must supply the covering row (a bounded miss is a `flag`,
never dropped); a hit on a PLL-valid cell is a soundness ALARM.
-/
import FRJ.CalculusW
import FRJ.Search.Engine
import FRJ.Gbu.Circ

namespace FRJ.Gbu.W

open FRJ Form FRJ.Search

/-! ## The W-database -/

/-- A W-database sequent.  The regular clause carries its `Tag`
explicitly — queries that do not care quantify it away; the manufacture
lemmas branch on it.  No clean stratum: `Lift` is tag-free, so the
`regC` workaround of `FSeq` has no W-analogue. -/
inductive WSeq where
  | reg (t : Tag) (Γ : List Form) (C : Form)
  | irr (Ξ Θ : List Form) (C : Form)

/-- Derivability of a database sequent in the W-family. -/
def WDerivable (G : Form) : WSeq → Prop
  | .reg t Γ C => Nonempty (FRJWr G t Γ C)
  | .irr Ξ Θ C => Nonempty (FRJWi G Ξ Θ C)

/-- `s₁ ⊑ s₂`: tag-aware on the regular stratum, following the
engine's retention order `tagLeB` (`blocked ≤ chain D ≤ barren`;
`chain` comparable only at equal pledge). -/
def WSubsumes : WSeq → WSeq → Prop
  | .reg t₁ Γ₁ C₁, .reg t₂ Γ₂ C₂ =>
      C₁ = C₂ ∧ tagLeB t₁ t₂ = true ∧ Γ₁ ⊆ Γ₂
  | .irr Ξ₁ Θ₁ C₁, .irr Ξ₂ Θ₂ C₂ =>
      C₁ = C₂ ∧ Ξ₁ ≐ Ξ₂ ∧ Θ₁ ⊆ Θ₂
  | _, _ => False

/-- (DB1) + tag-aware (DB2). -/
def WSaturated (G : Form) (D : WSeq → Prop) : Prop :=
  (∀ s, D s → WDerivable G s) ∧
  (∀ s, WDerivable G s → ∃ s', D s' ∧ WSubsumes s s')

/-! ## The queries -/

/-- The plain regular query (tag forgotten, matching `DisprovableW`). -/
def WEvalR (D : WSeq → Prop) (Ψ : List Form) (C : Form) : Prop :=
  ∃ t Γ, D (.reg t Γ C) ∧ ∀ X ∈ Ψ, Clo Γ X

/-- The PLEDGED regular query — what `regC`/`EvalRC` were
approximating; definable because the tag is explicit, needing no
stratum of its own.  Subsumption keeps it answerable: `barren` tops
the order and `Covers` is monotone in `Γ`. -/
def WEvalRP (D : WSeq → Prop) (Ψ : List Form) (C : Form) : Prop :=
  ∃ t Γ, D (.reg t Γ C) ∧
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C) ∧
    ∀ X ∈ Ψ, Clo Γ X

/-- The irregular query. -/
def WEvalI (D : WSeq → Prop) (Ω : List Form) (C : Form) : Prop :=
  ∃ Ξ Θ, D (.irr Ξ Θ C) ∧ Ξ ⊆ Ω ∧ Ω ⊆ Ξ ++ Θ

/-- (BSr1) with the `Ĝ` ancestor: every irregular W-row has `Ĝ`-bounded
zones, so bare `¬ WEvalI` is vacuous at a non-`Ĝ` context; the ancestor
threads the cell where the row manufacture lands. -/
def WUnrefutedBelow (G : Form) (D : WSeq → Prop) (Ω : List Form)
    (C : Form) : Prop :=
  ¬ WEvalI D Ω C ∧
    ∃ Ω₀ : List Form, (∀ X ∈ Ω₀, X ∈ gHat G) ∧ (∀ X ∈ Ω₀, Clo Ω X) ∧
      ¬ WEvalI D Ω₀ C

/-! ## The cell-level dichotomy statement -/

/-- `WSearchOk G D (reg?, Ψ, C)`: at a well-formed cell, either the
database refutes it or `Gbu◯` derives it.  The reg and irr clauses of
`SearchOkO`, over the W-database, with no supply hypotheses — and
TYPE-VALUED (Matthew 2026-09-01): the conclusions are the derivations
themselves, so `searchW` is a `def` that DELIVERS terms and
`decideGbuW`'s `⊕` inherits them; the `¬WEval` hypotheses are consumed
propositionally, so no choice is needed.  Data any consumer inspects
lives in indices and results; `∃` is reserved for facts consumed
propositionally. -/
def WSearchOk (G : Form) (D : WSeq → Prop) :
    Bool × List Form × Form → Type
  | (true, Ψ, C) =>
      (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G →
      ¬ WEvalR D Ψ C → GbuRC G Ψ C
  | (false, Ω, C) =>
      (∀ X ∈ Ω, X ∈ sfL G) →
      (C.isCirc = false → ∀ X ∈ Ω, X ∈ gHat G) →
      C ∈ sfR G →
      WUnrefutedBelow G D Ω C → GbuIC G Ω C

end FRJ.Gbu.W
