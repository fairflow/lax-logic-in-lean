import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLG4HCut
import LaxLogic.PLLG4HComp
import LaxLogic.PLLCompleteness
import LaxLogic.PLLKripke
import LaxLogic.PLLG4Space
import LaxLogic.PLLG4Dec

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

/-! ## The descent (Step C, the hard core) — STALL MARKER

The whole difficulty is the BUDGET DESCENT: `itpA (c+1) ⊢ itpA c`.
`itp_budget_mono` (PLLG4UITrunc.lean:1327) gives the reverse ASCENT
(`itpA c ⊢ itpA (c+1)`) unconditionally; the descent says the ascending
budget sequence has already STABILISED at `c`.  It is false in general
(`wip/absorb_base.lean:2259`, the sole open `sorry`).  The `itpE (c+1)`
conjunct is the ∃-mate available from the ambient.

WHAT THE ONE-VARIABLE HYPOTHESES BUY (empirical, via the algebra "zoo"
of `PLLExec.lean`, over 14 configs, defect ≤ 5):

* the interpolants are variable-free (Step A), hence live in the free
  lax algebra on 0 generators = the 3-element chain `⊥ ⊏ ◯⊥ ⊏ ⊤`;
* in that chain `◯` is IDEMPOTENT (`◯◯x ≡ ◯x`), so the deeper ◯-layers
  that higher budget builds collapse and add no semantic content;
* consequently the budget-ascending sequence `itpA b` stabilises
  SEMANTICALLY at `b = 1`: the only strict ascent is the trivial
  `⊥ = itpA 0 ⊏ itpA 1`, and `itpA b ≡ itpA 1` for every `b ≥ 1`
  (zoo `eqFails = (0,0)`, all 14 configs);
* hence the descent `itpA (c+1) ⊢ itpA c` is zoo-VALID for ALL `c ≥ 1`
  — a fortiori at the threshold `c ≥ 2` — with NO countermodel found
  (so the lemma is NOT false under one variable).  The `itpE` conjunct
  turns out unnecessary here (even the pure descent is zoo-valid at
  `c ≥ 1`); it is retained to match the parent statement.

NO SYNTACTIC SHORTCUT (checked and ruled out): the stabilisation is
only SEMANTIC.  With a non-trivial context `Γ` the interpolants differ
as ASTs — `itpA (c+1) Γ C ≠ itpA c Γ C` syntactically (measured:
`DecidableEq` returns `false` for `Γ = [◯p⊃p, ◯p]`, etc.), even though
`fullDesc = 0` there — so the descent is NOT `G4c.iden` and cannot be
closed by a `rfl`/decidable-equality collapse.  (Syntactic equality
does hold when `Γ = []`, because then `itpE b Γ = ⊤` for every `b`;
that special case is not the lemma.)

THE OBSTRUCTION (why this is left as `sorry`): the zoo is a finite set
of 7 models — `eqFails = 0` is NECESSARY but not SUFFICIENT for
derivability.  A Lean proof needs the SEMANTIC stabilisation lemma
"`force w (itpA (b+1)) → force w (itpA b)` for variable-free `itpA`,
`b ≥ 1`", proved by a soundness-style induction over the `itpA`
recursion into constraint models (à la `itp_sound`, PLLG4UITrunc:2456)
plus the 3-chain / nucleus-idempotency collapse.  That is a bounded but
substantial development (~`itp_sound` scale), not a syntactic
one-liner, and does not fit the timebox.  The bridge back to `G4c`
would be `consequence_iff_derivable` (PLLCompleteness:634) ∘ `equiv_nd`
(PLLG4HComp:110). -/
theorem onevar_descent (p : String) (S : Finset PLLFormula)
    (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula) (J : Nat)
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * (J + 2) ≤ c)
    (hSv : ∀ F ∈ S, F.atoms ⊆ {p})
    (hΓv : ∀ F ∈ Γ, F.atoms ⊆ {p})
    (hgv : g.atoms ⊆ {p}) :
    G4c [itpA p S fuel (c + 1) Γ g, itpE p S fuel (c + 1) Γ]
        (itpA p S fuel c Γ g) := by
  sorry

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

/-! ## Three-way verdict

VERDICT: **STALL** (and, importantly, NOT false — no countermodel).

Per-step status:
* Step A (variable-free collapse): mechanised as `atomsA_empty` /
  `atomsE_empty` modulo the atoms upper bound `hub` (an explicit
  hypothesis; the `p ∉ atoms` half is the library `itp_pfree`). The
  upper bound itself is the ~500-line `itp_pfree`-parallel induction,
  empirically confirmed (`atoms = ∅` in all 14 probe configs) but not
  transcribed here. NO sorry in this file's Step A.
* Step B (cut reduction): mechanised UNCONDITIONALLY and compiling.
  `cascade_low_pos_onevar` reduces by two `G4c.cut`s (plus a fuel
  alignment `itpA_fuel_le` and prefix weakening `weakenPre`) to the
  single sequent `onevar_descent`.
* Step C (the descent): the SOLE `sorry`, a clearly-marked stall.
  Empirically zoo-VALID for all `c ≥ 1` under one variable (stabilises
  at budget 1 by nucleus idempotency `◯◯ ≡ ◯` in the 3-chain). The
  obstruction to a Lean proof is the semantic stabilisation lemma
  (soundness of `itpA` into constraint models + 3-chain collapse), a
  bounded but `itp_sound`-scale development beyond the timebox.

The exact remaining goal (the `onevar_descent` sorry):
  `G4c [itpA p S fuel (c+1) Γ g, itpE p S fuel (c+1) Γ]
       (itpA p S fuel c Γ g)`
under `1 ≤ defect S Γ`, `defect S Γ * (J+2) ≤ c`, and atoms ⊆ {p}. -/

-- Axiom audit: depends on `sorryAx` via `onevar_descent` (the stall),
-- plus the usual classical trio.  The Step-B reduction and Step-A
-- collapse are themselves sorry-free.
#print axioms cascade_low_pos_onevar

end PLLND
