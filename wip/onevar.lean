import LaxLogic.PLL.UI.G4UITrunc
import LaxLogic.PLL.G4.G4HCut
import LaxLogic.PLL.G4.G4HComp
import LaxLogic.PLL.Semantics.Completeness
import LaxLogic.PLL.Semantics.Kripke
import LaxLogic.PLL.G4.G4Space
import LaxLogic.PLL.G4.G4Dec

/-!
# One-variable probe of the sole open descent lemma

EXPLORATION (not a proof that must succeed).  Tests whether the sole
`sorry` of the uniform-interpolation development
(`wip/absorb_base.lean:2259`, `cascade_low_pos_box`) becomes provable
when every formula uses only ONE propositional variable `p`.

Library imports only — compiles with `lake env lean wip/onevar.lean`
without the wipdeps olean recipe (does NOT import `absorb_base`).

The threshold hypothesis `defect S Γ * ((jumpGoals S).card + 2) ≤ c`
of the original is restated with an opaque `J : Nat` standing for
`(jumpGoals S).card`, so we need not import `absorb_base`.
-/

open PLLFormula
namespace PLLND

/-! ## Step A — variable-free collapse of the interpolants

Under the one-variable hypotheses every `prop q` leaf in the
`itpE`/`itpA` recursion has `q = p`, and every such branch is guarded
to DROP when `q = p` (see `PLLG4UITrunc.lean` lines 234-239, 302-303,
317-322, 382-384), so the interpolants carry no atom at all.

`itp_pfree` (PLLG4UITrunc.lean:1961, ~500 lines) already proves the
hard half, `p ∉ atoms`.  Combined with the atoms UPPER BOUND
`(itpX …).atoms ⊆ S,Γ,C-atoms ⊆ {p}` (the same-shape induction; taken
here as the hypothesis `hub`, empirically confirmed — see the probe
note at the bottom) this forces `atoms = ∅` via the combinator below.

Empirical confirmation: over 14 one-variable configurations (defect up
to 5, deep ◯-goals, ⊃-goals, Γ-growth, chained structures) every
`(itpA p S fuel b Γ C).atoms` computed to `∅` for `b < 5`. -/

/-- `s ⊆ {p}` and `p ∉ s` force `s = ∅`. -/
theorem atoms_empty_of_subset_singleton {s : Finset String} {p : String}
    (hsub : s ⊆ {p}) (hp : p ∉ s) : s = ∅ := by
  rcases Finset.subset_singleton_iff.mp hsub with h | h
  · exact h
  · exact absurd (h ▸ Finset.mem_singleton_self p) hp

/-- **Variable-free collapse, A-side.**  Given the atoms upper bound
(here a hypothesis; provable by the `itp_pfree`-parallel induction),
the ∀-interpolant is variable-free.  The `p ∉ atoms` half is the
library's `itp_pfree`. -/
theorem atomsA_empty (p : String) (S : Finset PLLFormula) (fuel b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula)
    (hub : (itpA p S fuel b Γ C).atoms ⊆ {p}) :
    (itpA p S fuel b Γ C).atoms = ∅ :=
  atoms_empty_of_subset_singleton hub ((itp_pfree p S fuel).2 b Γ C)

/-- **Variable-free collapse, E-side.** -/
theorem atomsE_empty (p : String) (S : Finset PLLFormula) (fuel b : Nat)
    (Γ : List PLLFormula)
    (hub : (itpE p S fuel b Γ).atoms ⊆ {p}) :
    (itpE p S fuel b Γ).atoms = ∅ :=
  atoms_empty_of_subset_singleton hub ((itp_pfree p S fuel).1 b Γ)

/-! ## Step B infrastructure — fuel alignment and list weakening

Two mechanical helpers used to reduce the goal, via two cuts, to the
single "descent" sequent that is the real hard core (Step C). -/

/-- `itpA` ascends in fuel, iterated to `fh ≤ fuel` (mirrors
`itp_budget_mono_le`'s A-side, but on the fuel parameter, using the
single-step `itp_fuel_mono`). -/
theorem itpA_fuel_le (p : String) (S : Finset PLLFormula) {fh fuel : Nat}
    (h : fh ≤ fuel) (b : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    G4c [itpA p S fh b Γ C] (itpA p S fuel b Γ C) := by
  induction h with
  | refl => exact G4c.iden (.head _)
  | @step m _ ih =>
      exact G4c.cut ih
        ((((itp_fuel_mono p S m).2 b Γ C).weaken _).perm (List.Perm.swap _ _ _))

/-- Weakening by a whole prefix list. -/
theorem weakenPre : ∀ (Δ : List PLLFormula) {Γ : List PLLFormula}
    {C : PLLFormula}, G4c Γ C → G4c (Δ ++ Γ) C
  | [], _, _, d => d
  | ψ :: Δ, _, _, d => (weakenPre Δ d).weaken ψ

/-! ## The descent (Step C, the hard core) — REDUCED TO ITS SEMANTIC CORE

The whole difficulty is the BUDGET DESCENT: `itpA (c+1) ⊢ itpA c`.
`itp_budget_mono` (PLLG4UITrunc.lean:1327) gives the reverse ASCENT
(`itpA c ⊢ itpA (c+1)`) unconditionally; the descent says the ascending
budget sequence has already STABILISED at `c`.  It is false in general
(`wip/absorb_base.lean:2259`, the sole open `sorry`).

WHAT THE ONE-VARIABLE HYPOTHESES BUY.  The interpolants are variable-free
(Step A), and empirically (zoo of `PLLExec.lean`; and `val3` below) the
budget-ascending sequence `itpA b` STABILISES at `b = 1`: `itpA b ≡ itpA 1`
for every `b ≥ 1`, so the descent is believed true for all `c ≥ 1` — no
countermodel found.  (Machine-checked `val3` samples, `fuel = 60`,
`S = {◯p⊃p, p, ◯p}`, reproducible in `wip/scratch_val3.lean`:
  `val3 (itpA b [◯p⊃p] p)      = [0,1,1,1,1,1]`  (b = 0..5)
  `val3 (itpA b [◯p⊃p,◯p] p)   = [1,2,2,2,2,2]`
  `val3 (itpE b [◯p⊃p,◯p])     = [2,2,2,2,2,2]`.)

WHY NO FINITE ALGEBRA CLOSES IT (correction to an earlier plan).  It is
tempting to read off derivability from `val3` (evaluation in the 3-chain
`⊥ ⊏ ◯⊥ ⊏ ⊤`, nucleus `j = max·1`).  `val3` is SOUND (it is one valid
lax algebra), but it is NOT COMPLETE for the closed fragment, so
`val3 x ≤ val3 y → G4c [x] y` is FALSE.  Machine-checked counterexample
(`wip/scratch_val3.lean`): with `x = ◯⊥ ⊃ ⊥ (= ¬◯⊥)` and `y = ⊥`,
  `val3 x = val3 y = 0`   (so `val3` would license `G4c [¬◯⊥] ⊥`),
but the identity-nucleus 3-chain (equally sound) gives `¬◯⊥ ↦ 2`,
`⊥ ↦ 0`, so `¬◯⊥ ⊬ ⊥`.  The element `¬◯⊥` escapes `{⊥,◯⊥,⊤}`; the closed
fragment's Lindenbaum algebra is the (infinite) Rieger–Nishimura lattice
with its nucleus, so no finite model — nor the finite zoo — is complete.
Semantic equality of `itpA (c+1)` and `itpA c` therefore cannot be
certified by any bounded `val3`/zoo computation; it needs entailment in
ALL constraint models.

WHAT IS DONE HERE.  `onevar_descent` is REDUCED, soundly and
`sorry`-free in its own body, to the single residual `descent_forcing`
below:
  * the `itpE (c+1)` conjunct is discharged by weakening (it is
    unnecessary — the pure descent already holds);
  * the `G4c ⇄ LaxND ⇄ constraint-model` bridge is discharged by
    `completeness` (PLLCompleteness:614) and `G4c.equiv_nd`
    (PLLG4HComp:109).
What remains is EXACTLY the F&M constraint-model statement the analysis
above identifies as the core: `force w (itpA (c+1)) → force w (itpA c)`
in every model.  That is an `itp_sound`-scale soundness-style induction
over the `itpA`/`itpE` recursion (PLLG4UITrunc:2456) using nucleus
idempotency — OPEN, not closable by a finite algebra. -/

/-- Evaluation in the 3-chain `⊥ ⊏ ◯⊥ ⊏ ⊤` with nucleus `j = max·1`
(atoms ↦ 0; irrelevant on variable-free inputs).  SOUND for `G4c` but,
as documented above, NOT complete for the closed fragment — kept only as
a computational witness of the stabilisation, never as a proof device. -/
def val3 : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and A B => min (val3 A) (val3 B)
  | .or A B => max (val3 A) (val3 B)
  | .ifThen A B => if val3 A ≤ val3 B then 2 else val3 B
  | .somehow A => max (val3 A) 1

/-- Evaluation in the 3-chain with the IDENTITY nucleus — also a sound lax
algebra.  Used only to certify that `val3` is not complete. -/
def valId : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and A B => min (valId A) (valId B)
  | .or A B => max (valId A) (valId B)
  | .ifThen A B => if valId A ≤ valId B then 2 else valId B
  | .somehow A => valId A

-- `◯` idempotent (`◯◯⊥ = ◯⊥ = 1`), `◯⊤ = ⊤`:
example : val3 (somehow (somehow falsePLL)) = 1 := rfl
example : val3 (somehow truePLL) = 2 := rfl
-- The soundness gap, machine-checked.  With `x = ¬◯⊥ = ◯⊥ ⊃ ⊥` and `y = ⊥`,
-- `val3` cannot tell them apart (both `0`), so it would license `G4c [¬◯⊥] ⊥`:
example : val3 (ifThen (somehow falsePLL) falsePLL) = val3 falsePLL := rfl
-- but the identity-nucleus model separates them (`2 ≠ 0`), so `¬◯⊥ ⊬ ⊥`.
-- Hence `val3 x ≤ val3 y → G4c [x] y` is FALSE: no single 3-chain is complete.
example : valId (ifThen (somehow falsePLL) falsePLL) ≠ valId falsePLL := by decide
/-- **The isolated minimal residual** — the force-level (F&M constraint-model)
budget-stabilisation of the ∀-interpolant, one variable.  This is *exactly* the
"SEMANTIC stabilisation lemma" the STALL note names as the sole obstruction:
`force w (itpA (b+1)) → force w (itpA b)`.  Everything else in the descent is now
discharged below `onevar_descent` — the `itpE` conjunct by weakening, and the full
`G4c ⇄ LaxND ⇄ constraint-model` bridge by `equiv_nd`/`completeness`.  What is left
is a soundness-style induction over the `itpA`/`itpE` recursion (à la `itp_sound`,
PLLG4UITrunc:2456) using nucleus idempotency; it is not closable by any finite
algebra (see the `val3` note above). -/
theorem descent_forcing (p : String) (S : Finset PLLFormula)
    (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula) (J : Nat)
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * (J + 2) ≤ c)
    (hSv : ∀ F ∈ S, F.atoms ⊆ {p})
    (hΓv : ∀ F ∈ Γ, F.atoms ⊆ {p})
    (hgv : g.atoms ⊆ {p}) :
    ∀ (M : ConstraintModel) (w : M.W),
      M.force w (itpA p S fuel (c + 1) Γ g) → M.force w (itpA p S fuel c Γ g) := by
  sorry

theorem onevar_descent (p : String) (S : Finset PLLFormula)
    (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula) (J : Nat)
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * (J + 2) ≤ c)
    (hSv : ∀ F ∈ S, F.atoms ⊆ {p})
    (hΓv : ∀ F ∈ Γ, F.atoms ⊆ {p})
    (hgv : g.atoms ⊆ {p}) :
    G4c [itpA p S fuel (c + 1) Γ g, itpE p S fuel (c + 1) Γ]
        (itpA p S fuel c Γ g) := by
  -- (1) The pure descent as a *semantic consequence* (drops `itpE`): the single
  -- hypothesis `force w (itpA (c+1))` feeds `descent_forcing`.
  have hcons : [itpA p S fuel (c + 1) Γ g] ⊨ itpA p S fuel c Γ g := by
    intro M w hw
    exact descent_forcing p S Γ fuel c g J hd1 hroom hSv hΓv hgv M w
      (hw _ (List.Mem.head _))
  -- (2) Completeness + `G4c ⇄ ND` turn it into a `G4c` derivation.
  have hpure : G4c [itpA p S fuel (c + 1) Γ g] (itpA p S fuel c Γ g) :=
    G4c.equiv_nd.mpr (completeness hcons)
  -- (3) Weaken the `itpE (c+1)` conjunct back in.
  exact (hpure.weaken (itpE p S fuel (c + 1) Γ)).perm (List.Perm.swap _ _ _)

/-- The one-variable restatement of `cascade_low_pos_box`.  Added
hypotheses `hSv`/`hΓv`/`hgv` confine every atom in play to `{p}`.

Reduced (Step B, unconditional) to `onevar_descent` by two cuts. -/
theorem cascade_low_pos_onevar (p : String) (S : Finset PLLFormula)
    (fh : Nat) (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
    (Δ : List PLLFormula) (J : Nat)
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * (J + 2) ≤ c)
    (hamb : G4c Δ (itpE p S fuel (c + 1) Γ))
    (hhead : G4c Δ (itpA p S fh (c + 1) Γ g))
    (hfh : fh ≤ fuel)
    (hSv : ∀ F ∈ S, F.atoms ⊆ {p})
    (hΓv : ∀ F ∈ Γ, F.atoms ⊆ {p})
    (hgv : g.atoms ⊆ {p}) :
    G4c Δ (itpA p S fuel c Γ g) := by
  -- Align `hhead` from fuel `fh` up to fuel `fuel`.
  have hheadF : G4c Δ (itpA p S fuel (c + 1) Γ g) :=
    G4c.cut hhead
      ((weakenPre Δ (itpA_fuel_le p S hfh (c + 1) Γ g)).perm
        List.perm_append_comm)
  -- The descent, transplanted into the ambient context `Δ`.
  have descΔ : G4c (itpA p S fuel (c + 1) Γ g ::
      itpE p S fuel (c + 1) Γ :: Δ) (itpA p S fuel c Γ g) :=
    (weakenPre Δ (onevar_descent p S Γ fuel c g J hd1 hroom hSv hΓv hgv)).perm
      List.perm_append_comm
  -- First cut removes the `itpA (c+1)` conjunct using `hheadF`.
  have step1 : G4c (itpE p S fuel (c + 1) Γ :: Δ) (itpA p S fuel c Γ g) :=
    G4c.cut (hheadF.weaken _) descΔ
  -- Second cut removes the `itpE (c+1)` conjunct using `hamb`.
  exact G4c.cut hamb step1

/-! ## Verdict

VERDICT: reduced to ONE semantic residual (`descent_forcing`); NOT false
— believed true for `c ≥ 1` under one variable, no countermodel.

Per-step status:
* Step A (variable-free collapse): mechanised as `atomsA_empty` /
  `atomsE_empty` modulo the atoms upper bound `hub` (an explicit
  hypothesis; the `p ∉ atoms` half is the library `itp_pfree`). NO sorry.
* Step B (cut reduction): mechanised UNCONDITIONALLY and compiling.
  `cascade_low_pos_onevar` reduces by two `G4c.cut`s to `onevar_descent`.
  NO sorry.
* Step C (the descent): `onevar_descent` is now mechanised `sorry`-free
  in its own body — it reduces to the residual `descent_forcing` by
  weakening away `itpE` and applying `completeness` ∘ `G4c.equiv_nd`.
  The SOLE remaining `sorry` is `descent_forcing`, the semantic core.

The exact remaining goal (the `descent_forcing` sorry), captured by
`trace_state`:
  `∀ (M : ConstraintModel) (w : M.W),
     M.force w (itpA p S fuel (c+1) Γ g) → M.force w (itpA p S fuel c Γ g)`
under `1 ≤ defect S Γ`, `defect S Γ * (J+2) ≤ c`, `S/Γ/g` atoms ⊆ {p}.

This is the F&M constraint-model budget-stabilisation of the ∀-interpolant.
It is NOT closable by any finite algebra (the `val3` note above gives the
machine-checked counterexample `¬◯⊥`); the honest route is a soundness-
style induction over the `itpA`/`itpE` recursion (à la `itp_sound`,
PLLG4UITrunc:2456) with nucleus idempotency `◯◯ ≡ ◯`. -/

-- Axiom audit: still depends on `sorryAx`, now via the single residual
-- `descent_forcing`, plus the usual classical trio.  Steps A and B and the
-- `onevar_descent` reduction (weakening + `completeness`/`equiv_nd`) are
-- all sorry-free.
#print axioms cascade_low_pos_onevar

end PLLND
