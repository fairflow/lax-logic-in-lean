/-
Route (B), node **N4**, WP12d: **`SatE2RD` is REFUTED**.

`wip/ui_routeB_r_escd.lean` reduces `PLL_UI` (through `pll_ui_R_escD`) to two
typed obligations, of which the `∃p` one is

    def SatE2RD (p : String) : Type :=
      ∀ (done Δ : List Neg) (ψ : Neg) (seen : SeenR) (b : HeightBook seen),
        Saturated done → ParkedCtxP done → PFreeCtx p Δ → PFreeN p ψ →
        ∀ {j : JD} (d : Inv (done ++ Δ) [] j ψ), BookBound seen b (hgtI d) →
          Sum (UpFrom (fun e => Inv (interpR p e [] done none seen :: Δ) [] j ψ))
              (EscD Δ seen b)

The record `seen` and the `p`-free context `Δ` are quantified INDEPENDENTLY.
They are not independent in the family: a record entry is created at a
recording site, which has a `Δ` of its own, and the escape's payload is a
derivation at that entry's station over THAT `Δ`.  Quantified apart, the
statement asks for an escape at a `Δ` that need have nothing to do with the
record, and this module shows the demand is not satisfiable.

## The counter-instance

    p     := "p"
    Qa    := ↓↑a                 M₀ := ↑a,  so Qa = ↓M₀
    X     := Qa ⊃ ↑n             a parked `simp` implication, antecedent compound
    done  := [X, ↑p]             saturated, `p`-carrying
    Δ     := []
    ψ     := Qa ⊃ ↑n             `p`-free
    seen  := [(Qa, done)]        the pair recorded, station set-equal to `done`
    b     := (hgtI refD, ())     the tightest book the invariant allows

`refD : Inv (done ++ []) [] .tru ψ` exists — assume `↓↑a`, fire `X`, get
`↑n` — and `BookBound seen b (hgtI refD)` holds.  Both branches then fail.

* **The value branch.**  At this record `interpR`'s ∃p row for `X` is `⊤`
  (`parkRowER_cut`, `BindCell.cellRows`) and the row for `↑p` is `⊤` because
  its atom IS `p`, so the ∃p interpolant is built from `nTop` alone AT EVERY
  FUEL (`ev_interpR_done`).  A one-world model with `a` true and `n` false
  satisfies it and refutes `ψ`.
* **The escape branch.**  `EscD [] seen b` asks for a derivation of
  `done ++ [] ⊢ ↑Qa`, i.e. of `↑↓↑a`; a one-world model with `a` false
  satisfies `done` and refutes it.  `EscD.there` reaches the empty record,
  where there is no escape at all.

Hence `satE2RD_refuted : SatE2RD "p" → False`.

## What is and is not refuted

REFUTED: `SatE2RD` as stated, hence the pair `(SatE2RD, SatA2RD)` that
`pll_ui_R_escD` reduces `PLL_UI` to.  The reduction stands as a theorem and
is now known to be vacuous.

NOT refuted: `interpR` itself, `SatE2R` / `SatA2R` (`seen = []`, where the
escape branch is empty and the interpolant keeps its fire rows), or uniform
interpolation for PLL.  What the instance exhibits is a STATEMENT fault of
the generalisation to an arbitrary record: nothing in it ties `seen` to `Δ`.

## The tool

Part 1 is a one-world (single-point Kripke) semantics for `LJF◯` with the
lax modality read as the identity nucleus, and its soundness for all four
judgments.  It is a refutation oracle for `Inv`: exhibit a valuation making
the hypotheses true and the goal false, and no derivation exists.  Nothing
in `LJF/` had one.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_bindcell
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · A one-world model of `LJF◯`, and soundness

A single-point Kripke model: every formula is evaluated classically, and the
lax modality is the identity nucleus `◯P = P`, which is a nucleus on the
one-point frame.  Monotonicity is vacuous, so soundness is a plain induction
on the four judgments. -/

mutual

/-- Value of a positive at the single world. -/
def evP (v : String → Bool) : Pos → Bool
  | .atom a => v a
  | .fls => false
  | .or P Q => evP v P || evP v Q
  | .down M => evN v M

/-- Value of a negative at the single world; `◯` is the identity nucleus. -/
def evN (v : String → Bool) : Neg → Bool
  | .up P => evP v P
  | .imp Q N => !(evP v Q) || evN v N
  | .and M N => evN v M && evN v N
  | .circ P => evP v P

end

/-- Every hypothesis holds. -/
def CtxT (v : String → Bool) (Γ : List Neg) : Prop := ∀ Z ∈ Γ, evN v Z = true

/-- Every pending positive holds. -/
def OmT (v : String → Bool) (Ω : List Pos) : Prop := ∀ P ∈ Ω, evP v P = true

theorem omT_nil {v : String → Bool} : OmT v [] :=
  fun _ h => absurd h List.not_mem_nil

theorem omT_singleton {v : String → Bool} {Q : Pos} (h : evP v Q = true) :
    OmT v [Q] := by
  intro P hP
  rcases List.mem_cons.mp hP with rfl | hP
  · exact h
  · exact absurd hP List.not_mem_nil

theorem ctxT_cons {v : String → Bool} {Z : Neg} {Γ : List Neg}
    (hZ : evN v Z = true) (hΓ : CtxT v Γ) : CtxT v (Z :: Γ) := by
  intro Y hY
  rcases List.mem_cons.mp hY with rfl | hY
  · exact hZ
  · exact hΓ _ hY

mutual

/-- Soundness, stable phase. -/
theorem sndS {v : String → Bool} : ∀ {Γ : List Neg} {j : JD} {P : Pos},
    Stab Γ j P → CtxT v Γ → evP v P = true
  | _, _, _, .rfoc r, hΓ => sndR r hΓ
  | _, _, _, .lfoc h lf, hΓ => sndL lf hΓ (hΓ _ h)
  | _, _, _, .laxOf s, hΓ => sndS s hΓ

/-- Soundness, right focus. -/
theorem sndR {v : String → Bool} : ∀ {Γ : List Neg} {j : JD} {P : Pos},
    RFocus Γ j P → CtxT v Γ → evP v P = true
  | _, _, _, .init h, hΓ => by
      have h1 := hΓ _ h; simp only [evN] at h1; exact h1
  | _, _, _, .or1 r, hΓ => by
      simp only [evP]; exact Bool.or_eq_true_iff.mpr (Or.inl (sndR r hΓ))
  | _, _, _, .or2 r, hΓ => by
      simp only [evP]; exact Bool.or_eq_true_iff.mpr (Or.inr (sndR r hΓ))
  | _, _, _, .rel d, hΓ => by
      simp only [evP]; exact sndI d hΓ omT_nil

/-- Soundness, left focus: a true hypothesis focuses to a true positive. -/
theorem sndL {v : String → Bool} :
    ∀ {Γ : List Neg} {N : Neg} {j : JD} {P : Pos},
      LFoc Γ N j P → CtxT v Γ → evN v N = true → evP v P = true
  | _, _, _, _, .rel d, hΓ, hN => by
      simp only [evN] at hN
      have h := sndI d hΓ (omT_singleton hN)
      simp only [evN] at h; exact h
  | _, _, _, _, .impL s lf, hΓ, hN => by
      have hs := sndS s hΓ
      simp only [evN, hs, Bool.not_true, Bool.false_or] at hN
      exact sndL lf hΓ hN
  | _, _, _, _, .and1 lf, hΓ, hN => by
      simp only [evN, Bool.and_eq_true] at hN
      exact sndL lf hΓ hN.1
  | _, _, _, _, .and2 lf, hΓ, hN => by
      simp only [evN, Bool.and_eq_true] at hN
      exact sndL lf hΓ hN.2
  | _, _, _, _, .circL d, hΓ, hN => by
      simp only [evN] at hN
      have h := sndI d hΓ (omT_singleton hN)
      simp only [evN] at h; exact h

/-- Soundness, inversion. -/
theorem sndI {v : String → Bool} : ∀ {Γ : List Neg} {Ω : List Pos} {j : JD}
    {C : Neg}, Inv Γ Ω j C → CtxT v Γ → OmT v Ω → evN v C = true
  | _, _, _, _, .impR d, hΓ, hΩ => by
      simp only [evN]
      cases hq : evP v _ with
      | false => simp
      | true =>
          simp only [Bool.not_true, Bool.false_or]
          refine sndI d hΓ ?_
          intro P hP
          rcases List.mem_cons.mp hP with rfl | hP
          · exact hq
          · exact hΩ _ hP
  | _, _, _, _, .andR d e, hΓ, hΩ => by
      simp only [evN, Bool.and_eq_true]
      exact ⟨sndI d hΓ hΩ, sndI e hΓ hΩ⟩
  | _, _, _, _, .circR d, hΓ, hΩ => by
      have h := sndI d hΓ hΩ
      simp only [evN] at h ⊢; exact h
  | _, _, _, _, .stable s, hΓ, _ => by
      simp only [evN]; exact sndS s hΓ
  | _, _, _, _, .orL d e, hΓ, hΩ => by
      have hor := hΩ _ (List.mem_cons_self ..)
      simp only [evP, Bool.or_eq_true] at hor
      rcases hor with h | h
      · exact sndI d hΓ (fun P hP => by
          rcases List.mem_cons.mp hP with rfl | hP
          · exact h
          · exact hΩ _ (List.mem_cons_of_mem _ hP))
      · exact sndI e hΓ (fun P hP => by
          rcases List.mem_cons.mp hP with rfl | hP
          · exact h
          · exact hΩ _ (List.mem_cons_of_mem _ hP))
  | _, _, _, _, .flsL, _, hΩ => by
      have h := hΩ _ (List.mem_cons_self ..)
      simp only [evP] at h; exact absurd h (by simp)
  | _, _, _, _, .downL d, hΓ, hΩ => by
      have h := hΩ _ (List.mem_cons_self ..)
      simp only [evP] at h
      exact sndI d (ctxT_cons h hΓ)
        (fun P hP => hΩ _ (List.mem_cons_of_mem _ hP))
  | _, _, _, _, .atomL d, hΓ, hΩ => by
      have h := hΩ _ (List.mem_cons_self ..)
      simp only [evP] at h
      exact sndI d (ctxT_cons (by simp only [evN, evP]; exact h) hΓ)
        (fun P hP => hΩ _ (List.mem_cons_of_mem _ hP))

end

/-- **The refutation oracle.**  A valuation satisfying the hypotheses and
refuting the goal shows the sequent has no derivation. -/
theorem no_inv_of_model {v : String → Bool} {Γ : List Neg} {j : JD} {C : Neg}
    (hΓ : CtxT v Γ) (hC : evN v C = false) (d : Inv Γ [] j C) : False := by
  have h := sndI d hΓ omT_nil
  rw [hC] at h; exact Bool.noConfusion h

/-! # Part 2 · The counter-instance

The formulas of `wip/ui_routeB_r_bindcell.lean`, with `Δ := []`. -/

namespace Refute

/-- The `∃p` goal: `p`-free, and derivable from the station. -/
def psi : Neg := .imp BindCell.Qa (.up (.atom "n"))

theorem psi_pfree : PFreeN "p" psi := by
  simp only [psi, BindCell.Qa, PFreeN, PFreeP]
  exact ⟨by decide, by decide⟩

/-- The derivation the instance is applied to: assume `↓↑a`, fire `X`. -/
def refD : Inv (BindCell.done ++ []) [] .tru psi :=
  .impR (.downL (.stable (.lfoc (by decide)
    (.impL (.rfoc (.rel (.stable (.rfoc (.init (List.mem_cons_self ..))))))
           (.rel (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..))))))))))

/-- The tightest book the invariant allows. -/
def refB : HeightBook BindCell.seen := (hgtI refD, PUnit.unit)

theorem refBook : BookBound BindCell.seen refB (hgtI refD) :=
  ⟨Nat.le_refl _, trivial⟩

/-! ## The two valuations -/

/-- `a` true, `n` false: satisfies the ∃p interpolant at this record and
refutes `ψ`. -/
def vVal : String → Bool := fun s => !(s == "n")

/-- `a` false: satisfies the station and refutes the escape's goal `↑Qa`. -/
def vEsc : String → Bool := fun s => s == "n" || s == "p"

/-! ## The interpolant at this record is `⊤`-built -/

/-- The interpolant of the residual station `[↑p]`, at every fuel: its only
row is the `p`-guard of `↑p`, which is `nTop`. -/
theorem ev_interpR_p (v : String → Bool) : ∀ (f : Nat),
    evN v (interpR "p" f [] [Neg.up (.atom "p")] none BindCell.seen) = true
  | 0 => rfl
  | f + 1 => by
      have h : interpR "p" (f + 1) [] [Neg.up (.atom "p")] none BindCell.seen
          = nAnd nTop nTop := rfl
      rw [h]; rfl

/-- **The ∃p interpolant at this record is `⊤`-built, at every fuel.**  The
row of `X` is `⊤` because the pair is recorded (`BindCell.cellRows`), the row
of `↑p` is `⊤` because its atom IS `p`, and the residual is
`ev_interpR_p`. -/
theorem ev_interpR_done (v : String → Bool) : ∀ (f : Nat),
    evN v (interpR "p" f [] BindCell.done none BindCell.seen) = true
  | 0 => rfl
  | f + 1 => by
      have h : interpR "p" (f + 1) [] BindCell.done none BindCell.seen
          = nAndAll [nAnd nTop
              (interpR "p" f [] [Neg.up (.atom "p")] none BindCell.seen),
            nTop] := by
        show nAndAll (eRowsR id "p" (interpGR id "p" f) BindCell.done
              BindCell.seen) = _
        rw [BindCell.cellRows]
      rw [h]
      have hp := ev_interpR_p v f
      simp [nAndAll, nAnd, nTop, evN, evP, hp]

/-! ## The two branches fail -/

theorem valueFails (f : Nat)
    (d : Inv (interpR "p" f [] BindCell.done none BindCell.seen :: []) []
           (.tru) psi) : False :=
  no_inv_of_model (v := vVal)
    (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact ev_interpR_done vVal f
      · exact absurd hZ List.not_mem_nil)
    (by simp only [psi, BindCell.Qa, BindCell.M0, evN, evP, vVal]; rfl) d

theorem escapeFails (gd : Inv (BindCell.done ++ []) [] .tru (.up BindCell.Qa)) :
    False :=
  no_inv_of_model (v := vEsc)
    (fun Z hZ => by
      simp only [BindCell.done, List.append_nil] at hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · simp only [BindCell.X, BindCell.Qa, evN, evP, vEsc]; rfl
      · rcases List.mem_cons.mp hZ with rfl | hZ
        · simp only [evN, evP, vEsc]; rfl
        · exact absurd hZ List.not_mem_nil)
    (by simp only [BindCell.Qa, evN, evP, vEsc]; rfl) gd

/-! # Part 3 · The refutation -/

/-- **`SatE2RD` is REFUTED.**  At the instance of Part 2 the value branch is
not derivable and the escape branch is empty. -/
theorem satE2RD_refuted (t : SatE2RD "p") : False := by
  have hΔ : PFreeCtx "p" ([] : List Neg) := fun _ h => absurd h List.not_mem_nil
  match t BindCell.done [] psi BindCell.seen refB BindCell.cellSaturated
      BindCell.cellParked hΔ psi_pfree (j := .tru) refD refBook with
  | .inl w => exact valueFails w.1 (w.2 w.1 (Nat.le_refl _))
  | .inr e =>
      cases e with
      | here gd _ => exact escapeFails gd
      | there e' => exact escD_nil_empty e'

end Refute

end LJFO

/-! ## Pins -/

#axioms_within LJFO.evP []
#axioms_within LJFO.evN []
#axioms_within LJFO.omT_nil []
#axioms_within LJFO.omT_singleton [propext]
#axioms_within LJFO.ctxT_cons [propext]
#axioms_within LJFO.sndS [propext, Quot.sound]
#axioms_within LJFO.sndR [propext, Quot.sound]
#axioms_within LJFO.sndL [propext, Quot.sound]
#axioms_within LJFO.sndI [propext, Quot.sound]
#axioms_within LJFO.no_inv_of_model [propext, Quot.sound]
#axioms_within LJFO.Refute.psi_pfree []
#axioms_within LJFO.Refute.refD [propext]
#axioms_within LJFO.Refute.refBook [propext]
#axioms_within LJFO.Refute.ev_interpR_p [propext]
#axioms_within LJFO.Refute.ev_interpR_done [propext]
#axioms_within LJFO.Refute.valueFails [propext, Quot.sound]
#axioms_within LJFO.Refute.escapeFails [propext, Quot.sound]
#axioms_within LJFO.Refute.satE2RD_refuted [propext, Quot.sound]
