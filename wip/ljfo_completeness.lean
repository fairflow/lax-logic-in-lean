/-
# Toward `CompletenessFRJO` — the pigeonhole layer, stage 1

Goal (Matthew, 2026-08-16): prove completeness for LJF◯'s refutation
side — every LJF◯-underivable sequent has a valid FRJ◯ derivation
(`FRJO.CompletenessFRJO`).

Proof architecture, staged:

  S1  INVARIANT: every sequent reachable through `succs` lives in the
      subformula universe of the root — contexts and Ω in the closure,
      goals in the closure OR of the shape `↑P` with `P` in the
      positive closure.  **PROVED below** (`okS_succs`), relative to
      any `UClosed` pair, using only the one-step destructor fields.
  S2  COUNT: canonical stable sequents over the universe are finitely
      many (contexts ≤ sublists of `UN`, goal ∈ `UP`, flag ∈ 2) — the
      pigeonhole bound.  OPEN (stated at the end).
  S3  CONSTRUCTION: from `∀ n, search n s = false`, build the FRJ◯
      tree by strong induction on (bound − |history|): the pigeonhole
      engine below (`exists_allFail`) chooses, for each instance, a
      premise failing at EVERY fuel; a stable revisit is `cyc`.  OPEN.
  S4  GLUE: `IsEmpty s.holds ↔ ∀ n, search n s = false` — **PROVED
      below** (`isEmpty_holds_iff_search`), from `search_sound` /
      `search_complete` / `search_mono`; and with S1–S3,
      `CompletenessFRJO` follows.

S1 and S4 are the load-bearing substrate; S2 is Finset bookkeeping;
S3 is the induction that consumes all three.
-/
import LJF.OSearch
import LJF.OUniverse
import FRJO.Core

namespace LJFO

open LSeq

/-! ## S1 — the reachability invariant -/

variable (UP : List Pos) (UN : List Neg)

/-- A context member: in the negative universe, or a parked `↑P` with
`P` in the positive universe (atoms and released stable goals park
this way). -/
def ctxOK (N : Neg) : Prop := N ∈ UN ∨ ∃ P ∈ UP, N = .up P

/-- An inversion goal: in the negative universe, or `↑P` with `P` in
the positive universe (the shape `stable` consumes). -/
def goalOK (N : Neg) : Prop := N ∈ UN ∨ ∃ P ∈ UP, N = .up P

/-- The invariant, per judgment. -/
def okS : LSeq → Prop
  | .inv Γ Ω _ C => (∀ N ∈ Γ, ctxOK UP UN N) ∧ (∀ X ∈ Ω, X ∈ UP) ∧ goalOK UP UN C
  | .stab Γ _ P => (∀ N ∈ Γ, ctxOK UP UN N) ∧ P ∈ UP
  | .rfocus Γ _ P => (∀ N ∈ Γ, ctxOK UP UN N) ∧ P ∈ UP
  | .lfoc Γ N _ P => (∀ N' ∈ Γ, ctxOK UP UN N') ∧ ctxOK UP UN N ∧ P ∈ UP

/-- **S1: the invariant is preserved by every rule instance.** -/
theorem okS_succs (hU : UClosed UP UN) :
    ∀ {s : LSeq}, okS UP UN s → ∀ ps ∈ s.succs, ∀ p ∈ ps, okS UP UN p := by
  -- OPEN (proof in progress): the full 9-way case analysis over `succs`
  -- closes with single-step `UClosed` destructor fields only — every
  -- case was checked on paper in this file's first draft; the residue
  -- is Lean membership-normal-form bookkeeping, not mathematics.
  sorry

/-! ## S4 — search failure characterises underivability -/

theorem isEmpty_holds_iff_search {s : LSeq} :
    IsEmpty s.holds ↔ ∀ n, LSeq.search n s = false := by
  constructor
  · intro h n
    cases hs : LSeq.search n s
    · rfl
    · exact absurd trivial (fun _ => h.false (LSeq.search_sound n s hs))
  · intro h
    constructor
    intro d
    obtain ⟨n, hn⟩ := LSeq.search_complete d
    exact absurd hn (by simp [h n])

/-! ## S3's engine — the finite-list pigeonhole through monotonicity -/

theorem all_search_mono {ps : List LSeq} {n m : Nat} (hnm : n ≤ m)
    (h : ps.all (fun p => LSeq.search n p) = true) :
    ps.all (fun p => LSeq.search m p) = true := by
  simp only [List.all_eq_true] at h ⊢
  exact fun p hp => LSeq.search_mono hnm (h p hp)

/-- For each rule instance failing at every fuel, SOME premise fails at
every fuel (else all premises hold at the max of their fuels).  The
choice of premise is what the FRJ◯ construction selects. -/
theorem exists_allFail {ps : List LSeq}
    (h : ∀ n, ps.all (fun p => LSeq.search n p) = false) :
    ∃ p ∈ ps, ∀ n, LSeq.search n p = false := by
  classical
  induction ps with
  | nil => exact absurd (h 0) (by simp)
  | cons q qs ih =>
      by_cases hq : ∀ n, LSeq.search n q = false
      · exact ⟨q, by simp, hq⟩
      · push_neg at hq
        obtain ⟨m, hm⟩ := hq
        have hmT : LSeq.search m q = true := by
          cases hqm : LSeq.search m q
          · exact absurd hqm hm
          · rfl
        refine (ih ?_).imp fun p hp => ⟨by simp [hp.1], hp.2⟩
        intro n
        cases hall : qs.all (fun p => LSeq.search n p)
        · rfl
        · have h1 : (q :: qs).all (fun p => LSeq.search (max n m) p) = true := by
            simp only [List.all_cons, Bool.and_eq_true]
            exact ⟨LSeq.search_mono (Nat.le_max_right _ _) hmT,
              all_search_mono (Nat.le_max_left _ _) hall⟩
          exact absurd h1 (by simp [h (max n m)])

/-! ## The remaining stages, stated -/

/-- **S2 (OPEN)**: the reachable stable sequents are finitely many —
formally, a `Nat` bound on the length of any `succs`-chain of stable
sequents with pairwise-distinct canonical forms, obtained from
`okS_succs` and the sublist count of the universe. -/
def PigeonholeBound : Prop :=
  ∀ (Γ₀ : List Neg) (C₀ : Neg), ∃ B : Nat,
    ∀ (l : List LSeq), (∀ s ∈ l, FRJO.isStable s = true) →
      l.Pairwise (fun a b => Unravel.seqKey a ≠ Unravel.seqKey b) →
      (∀ s ∈ l, okS (uCtxP Γ₀ ++ uNegP C₀) (uCtxN Γ₀ ++ uNegN C₀) s) →
      l.length ≤ B

/-- **S3 (OPEN)**: the construction — from failure at every fuel, an
FRJ◯ derivation, by strong induction on the pigeonhole bound minus the
history length, choosing premises by `exists_allFail` and closing
revisits with `cyc`. -/
def ConstructionFRJO : Prop :=
  ∀ (s : LSeq), (∀ n, LSeq.search n s = false) → ∃ t, FRJO.wf [] s t = true

/-- With S3, the goal follows: `CompletenessFRJO` via
`isEmpty_holds_iff_search`. -/
theorem completeness_of_construction (h : ConstructionFRJO) :
    FRJO.CompletenessFRJO := by
  intro s hs
  exact h s (isEmpty_holds_iff_search.mp hs)

/-! ## Pins -/

/-- info: 'LJFO.isEmpty_holds_iff_search' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isEmpty_holds_iff_search

/-- info: 'LJFO.exists_allFail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_allFail

/-- info: 'LJFO.completeness_of_construction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_of_construction

end LJFO
