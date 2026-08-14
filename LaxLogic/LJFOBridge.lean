/-
LJF◯ → PLL: the ERASURE BRIDGE.

`LaxLogic/LJFOCore.lean` builds the lax-flagged focused calculus LJF◯
and proves a great deal ABOUT it, and `LJFOSearch.lean` relates the
fueled search to the calculus.  What has been missing is the arrow that
makes any of it mean something for PLL: a theorem relating LJF◯
derivability to `PLLND.LaxND`.  Without it, an LJF◯ verdict is a fact
about LJF◯ and nothing more.

This file supplies the bridge, BOTH WAYS:

    LJF◯ ⊢ ⟺ PLL ⊢          (`bridge_iff`)

Soundness (`⟹`) goes by erasing polarity (`erasePos`/`eraseNeg` — `↓`/`↑` vanish, `circ`
becomes `◯`) and reading the judgment flag as the modality:

    Γ ⊢tru P   ↦   ⌊Γ⌋ ⊢ ⌊P⌋
    Γ ⊢lax P   ↦   ⌊Γ⌋ ⊢ ◯⌊P⌋

which is the file's own gloss made into a theorem ("the lax goal is
definable: `Γ ⊢lax P` iff `Γ ⊢tru ↓◯P`-wise").  All four judgments are
handled by one mutual recursion, mirroring `Stab.wk`/`RFocus.wk`/
`LFoc.wk`/`Inv.wk`.

Where the modal content lands:

* `laxOf`  ↦ `laxIntro`  — the truth-to-lax coercion IS `φ ⊢ ◯φ`;
* `circL`  ↦ `laxElim`   — opening a box at a lax goal IS `◯`-elim;
* `circR`  ↦ identity at `tru`, `laxIntro` at `lax` (`◯φ ⊢ ◯◯φ`).

Everything else is structural, and every structural move is
`LaxND.rename`, which subsumes weakening, exchange and contraction —
so no cut and no admissibility lemma is needed anywhere below.

Completeness (`⟸`) is `focalizeSCO`: the port of
`LJFComplete.focalizeSC` to a polarisation that KEEPS the modality.
Every helper it needs is already in `LJFOCore` with the flag threaded,
so the new content is exactly the two modal cases —

* `laxR` ↦ `circR` over `laxOf`: prove the body truly, then coerce;
* `laxL` ↦ `circR` over `lfoc`/`circL`: focus on the box, its body
  entering the inversion queue.

both of which are TRIVIAL in `LJFComplete` only because `negOf` erases
`◯` there.  This closes `docs/ljfo-fidelity.md` §5's open item
("focalization for PLL").  Verdicts now transfer in BOTH directions: an
LJF◯ proof gives a PLL proof, and an LJF◯ failure gives a PLL failure.
-/
import LaxLogic.LJFOCore
import LaxLogic.PLLNDCore
import LaxLogic.PLLSequent

namespace LJFO

open PLLND

/-! ## 1. Erasure -/

mutual

/-- Erase a positive proposition: `↓` vanishes. -/
def erasePos : Pos → PLLFormula
  | .atom a => .prop a
  | .fls => .falsePLL
  | .or P Q => .or (erasePos P) (erasePos Q)
  | .down N => eraseNeg N

/-- Erase a negative proposition: `↑` vanishes, `circ` becomes `◯`. -/
def eraseNeg : Neg → PLLFormula
  | .up P => erasePos P
  | .imp Q N => .ifThen (erasePos Q) (eraseNeg N)
  | .and M N => .and (eraseNeg M) (eraseNeg N)
  | .circ P => .somehow (erasePos P)

end

/-- Erase a context. -/
def eraseCtx (Γ : List Neg) : List PLLFormula := Γ.map eraseNeg

/-- The judgment flag, as a modality on the goal. -/
def goal : JD → PLLFormula → PLLFormula
  | .tru, φ => φ
  | .lax, φ => .somehow φ

/-! ## 2. The two flag lemmas

Everything flag-dependent factors through these, so the main recursion
never case-splits on `JD` except where a rule does. -/

/-- A truth-derivation gives the flagged goal, at either flag: at `lax`
this is exactly `laxIntro`. -/
def goalOf {Γ : List PLLFormula} {φ : PLLFormula} :
    (j : JD) → LaxND Γ φ → LaxND Γ (goal j φ)
  | .tru, p => p
  | .lax, p => .laxIntro p

/-- Substitution for a single hypothesis, WITHOUT cut: `⊃`-intro then
`⊃`-elim.  Uniform in the goal formula, so it serves the focus rules
whatever the flag. -/
def subst1 {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (f : LaxND (φ :: Γ) ψ) (p : LaxND Γ φ) : LaxND Γ ψ :=
  .impElim (.impIntro f) p

/-- The flagged goal is monotone in the formula, uniformly in the flag:
at `lax` this is `laxElim`. -/
def goalMap {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    (j : JD) → LaxND (φ :: Γ) ψ → LaxND Γ (goal j φ) → LaxND Γ (goal j ψ)
  | .tru, f, p => .impElim (.impIntro f) p
  | .lax, f, p => .laxElim p (.laxIntro f)

/-! ## 3. Soundness

One mutual recursion over the four judgments.  Structural throughout;
the three modal rules are the three named above. -/

mutual

/-- **A stable sequent erases to a PLL derivation.** -/
def Stab.sound : {Γ : List Neg} → {j : JD} → {P : Pos} →
    Stab Γ j P → LaxND (eraseCtx Γ) (goal j (erasePos P))
  | _, _, _, .rfoc d => RFocus.sound d
  | _, _, _, .lfoc h d =>
      (LFoc.sound d).rename (by
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact List.mem_map_of_mem h
        · exact hχ)
  | _, _, _, .laxOf d => .laxIntro (Stab.sound d)

/-- **Right focus.** -/
def RFocus.sound : {Γ : List Neg} → {j : JD} → {P : Pos} →
    RFocus Γ j P → LaxND (eraseCtx Γ) (goal j (erasePos P))
  | _, j, _, .init h => goalOf j (.iden (List.mem_map_of_mem h))
  | _, j, _, .or1 d => goalMap j (.orIntro1 (.iden (List.mem_cons_self ..)))
      (RFocus.sound d)
  | _, j, _, .or2 d => goalMap j (.orIntro2 (.iden (List.mem_cons_self ..)))
      (RFocus.sound d)
  | _, _, _, .rel d => Inv.sound d

/-- **Left focus**: the focused hypothesis is put at the head of the
erased context. -/
def LFoc.sound : {Γ : List Neg} → {N : Neg} → {j : JD} → {P : Pos} →
    LFoc Γ N j P → LaxND (eraseNeg N :: eraseCtx Γ) (goal j (erasePos P))
  | _, _, _, _, .rel d => Inv.sound d
  | _, _, _, _, .impL a d =>
      subst1 ((LFoc.sound d).rename (by
          intro χ hχ
          rcases List.mem_cons.mp hχ with rfl | hχ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hχ)))
        (.impElim (.iden (List.mem_cons_self ..))
          ((Stab.sound a).rename (fun _ h => List.mem_cons_of_mem _ h)))
  | _, _, _, _, .and1 d =>
      subst1 ((LFoc.sound d).rename (by
          intro χ hχ
          rcases List.mem_cons.mp hχ with rfl | hχ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hχ)))
        (.andElim1 (.iden (List.mem_cons_self ..)))
  | _, _, _, _, .and2 d =>
      subst1 ((LFoc.sound d).rename (by
          intro χ hχ
          rcases List.mem_cons.mp hχ with rfl | hχ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hχ)))
        (.andElim2 (.iden (List.mem_cons_self ..)))
  | _, _, _, _, .circL d =>
      .laxElim (.iden (List.mem_cons_self ..))
        ((Inv.sound d).rename (by
          intro χ hχ
          rcases List.mem_cons.mp hχ with rfl | hχ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hχ)))

/-- **Inversion**: the `Ω`-zone erases to a prefix of the context. -/
def Inv.sound : {Γ : List Neg} → {Ω : List Pos} → {j : JD} → {N : Neg} →
    Inv Γ Ω j N → LaxND (Ω.map erasePos ++ eraseCtx Γ) (goal j (eraseNeg N))
  | _, _, _, _, .impR d => .impIntro (Inv.sound d)
  | _, _, _, _, .andR d e => .andIntro (Inv.sound d) (Inv.sound e)
  | _, _, j, _, .circR d => goalOf j (Inv.sound d)
  | _, _, _, _, .stable d => Stab.sound d
  | _, _, _, _, .orL d e =>
      .orElim (.iden (List.mem_cons_self ..))
        ((Inv.sound d).rename (by
          intro χ hχ
          rcases List.mem_cons.mp hχ with rfl | hχ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hχ)))
        ((Inv.sound e).rename (by
          intro χ hχ
          rcases List.mem_cons.mp hχ with rfl | hχ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hχ)))
  | _, _, _, _, .flsL => .falsoElim _ (.iden (List.mem_cons_self ..))
  | _, _, _, _, .downL d =>
      (Inv.sound d).rename (by
        intro χ hχ
        rcases List.mem_append.mp hχ with h | h
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ h))
  | _, _, _, _, .atomL d =>
      (Inv.sound d).rename (by
        intro χ hχ
        rcases List.mem_append.mp hχ with h | h
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ h))

end

/-! ## 4. The bridge, in the form a caller wants -/

/-- **LJF◯ SOUNDNESS FOR PLL**: a truth-flagged stable derivation gives
a PLL natural-deduction derivation of the erased sequent. -/
def sound_tru {Γ : List Neg} {P : Pos} (d : Stab Γ .tru P) :
    LaxND (eraseCtx Γ) (erasePos P) := Stab.sound d

/-- **The lax judgment is the modality**: a lax-flagged derivation gives
`◯` of the erased goal. -/
def sound_lax {Γ : List Neg} {P : Pos} (d : Stab Γ .lax P) :
    LaxND (eraseCtx Γ) (.somehow (erasePos P)) := Stab.sound d

/-- Nonempty form: LJF◯ derivability implies PLL derivability. -/
theorem laxND_of_ljfo {Γ : List Neg} {P : Pos} (d : Stab Γ .tru P) :
    Nonempty (LaxND (eraseCtx Γ) (erasePos P)) := ⟨sound_tru d⟩

/-- The contrapositive — the form the DISPROOF thread consumes: a PLL
countermodel refutes the LJF◯ sequent too. -/
theorem not_ljfo_of_not_laxND {Γ : List Neg} {P : Pos}
    (h : ¬ Nonempty (LaxND (eraseCtx Γ) (erasePos P))) :
    IsEmpty (Stab Γ .tru P) :=
  ⟨fun d => h (laxND_of_ljfo d)⟩

/-! ## 4b. The ◯-PRESERVING polarisation, and the converse

`LJFComplete.lean`'s `posOf`/`negOf` DISCARD the modality
(`.somehow φ ↦ posOf φ`), because that development targets IPC through
`PLLND.erase`.  For LJF◯ the polarisation must keep it, so the round
trip is the identity on PLL formulas rather than the ◯-erasure.  With
that, the converse arrow becomes statable, and the bridge becomes a
biconditional the moment it is supplied. -/

mutual

/-- Polarise a PLL formula positively, KEEPING `◯`. -/
def posOfO : PLLFormula → Pos
  | .prop a => .atom a
  | .falsePLL => .fls
  | .or φ ψ => .or (posOfO φ) (posOfO ψ)
  | .and φ ψ => .down (.and (negOfO φ) (negOfO ψ))
  | .ifThen φ ψ => .down (.imp (posOfO φ) (negOfO ψ))
  | .somehow φ => .down (.circ (posOfO φ))

/-- Polarise a PLL formula negatively, KEEPING `◯`. -/
def negOfO : PLLFormula → Neg
  | .prop a => .up (.atom a)
  | .falsePLL => .up .fls
  | .or φ ψ => .up (.or (posOfO φ) (posOfO ψ))
  | .and φ ψ => .and (negOfO φ) (negOfO ψ)
  | .ifThen φ ψ => .imp (posOfO φ) (negOfO ψ)
  | .somehow φ => .circ (posOfO φ)

end

/-- **The round trip is the identity**: polarising and then erasing
gives the formula back, `◯` included. -/
theorem erase_polarise (φ : PLLFormula) :
    erasePos (posOfO φ) = φ ∧ eraseNeg (negOfO φ) = φ := by
  induction φ with
  | prop a => exact ⟨rfl, rfl⟩
  | falsePLL => exact ⟨rfl, rfl⟩
  | and φ ψ ihφ ihψ =>
      refine ⟨?_, ?_⟩ <;>
        simp [posOfO, negOfO, erasePos, eraseNeg, ihφ.2, ihψ.2]
  | or φ ψ ihφ ihψ =>
      refine ⟨?_, ?_⟩ <;>
        simp [posOfO, negOfO, erasePos, eraseNeg, ihφ.1, ihψ.1]
  | ifThen φ ψ ihφ ihψ =>
      refine ⟨?_, ?_⟩ <;>
        simp [posOfO, negOfO, erasePos, eraseNeg, ihφ.1, ihψ.2]
  | somehow φ ih =>
      refine ⟨?_, ?_⟩ <;>
        simp [posOfO, negOfO, erasePos, eraseNeg, ih.1]

theorem eraseCtx_polarise (Γ : List PLLFormula) :
    eraseCtx (Γ.map negOfO) = Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih =>
      simp only [List.map_cons, eraseCtx, List.map_map] at ih ⊢
      exact congrArg₂ _ (erase_polarise φ).2 ih

/-! ### The converse: focalization completeness for PLL

The port of `LJFComplete.focalizeSC` to the ◯-preserving polarisation.
Every helper it needs is already in `LJFOCore` with the flag threaded —
`unStable`, `invertPos`, `invBranches`, `extract`, `simHyp`, `upMerge`,
`stabOr1/2`, `nBotElim` — so only the four bridge-specific helpers and
the two modal cases are new.

The two modal cases are where `negOfO` differs from `LJFComplete`'s
`negOf`, which erases `◯` and makes them trivial:

* `laxR` ↦ `circR` over `laxOf` — prove the body truly, coerce to lax;
* `laxL` ↦ `circR` over `lfoc`/`circL` — focus on the box, its body
  entering the inversion queue via `shiftInO`.
-/

/-- `circR` is the only rule that can conclude `circ` from an EMPTY
inversion queue — the `Ω`-processing rules all need a non-empty queue —
so inverting it is a single pattern match. -/
def circInv {Γ : List Neg} {j : JD} {P : Pos} :
    Inv Γ [] j (.circ P) → Inv Γ [] .lax (.up P)
  | .circR d => d

/-- An inversion at `[]` gives the stable form of the polarised goal. -/
def stabOfInvO : (φ : PLLFormula) → {Δ : List Neg} → {j : JD} →
    Inv Δ [] j (negOfO φ) → Stab Δ j (posOfO φ)
  | .prop _, _, _, d => unStable d
  | .falsePLL, _, _, d => unStable d
  | .or _ _, _, _, d => unStable d
  | .and _ _, _, _, d => .rfoc (.rel d)
  | .ifThen _ _, _, _, d => .rfoc (.rel d)
  | .somehow _, _, _, d => .rfoc (.rel d)

/-- Discharge a left focus on a shifted hypothesis against a branch. -/
def upBranchLFocO {Q : Pos} {Δ : List Neg} {j : JD} {P : Pos}
    {b : List Neg} (hb : b ∈ invertPos Q) (hsub : ∀ X ∈ b, X ∈ Δ) :
    LFoc Δ (.up Q) j P → Stab Δ j P
  | .rel e =>
      unStable ((extract [] e b hb).wk (fun Z hZ => by
        rcases List.mem_append.mp hZ with hZ | hZ
        · exact hsub Z hZ
        · exact hZ))

/-- Discharge a left focus on a hypothesis whose positive is a shift. -/
def downBranchLFocO {M : Neg} {Δ : List Neg} {j : JD} {P : Pos}
    {b : List Neg} (hb : b ∈ invertPos (.down M))
    (hsub : ∀ X ∈ b, X ∈ Δ) (lf : LFoc Δ M j P) : Stab Δ j P := by
  simp only [invertPos, List.mem_singleton] at hb
  subst hb
  exact .lfoc (hsub _ (List.mem_cons_self ..)) lf

/-- Every use of the hypothesis `negOfO φ` is available inside any
branch of the inversion of `posOfO φ`.  Note the `somehow` case is now
a SHIFT case, not a recursive one — that is the whole effect of keeping
the modality in the polarisation. -/
def branchLFocO : (φ : PLLFormula) → {Δ : List Neg} → {j : JD} → {P : Pos} →
    {b : List Neg} → b ∈ invertPos (posOfO φ) → (∀ X ∈ b, X ∈ Δ) →
    LFoc Δ (negOfO φ) j P → Stab Δ j P
  | .prop _, _, _, _, _, hb, hsub, lf => upBranchLFocO hb hsub lf
  | .falsePLL, _, _, _, _, hb, _, _ => by
      simp only [posOfO, invertPos, List.not_mem_nil] at hb
  | .or _ _, _, _, _, _, hb, hsub, lf => upBranchLFocO hb hsub lf
  | .and _ _, _, _, _, _, hb, hsub, lf => downBranchLFocO hb hsub lf
  | .ifThen _ _, _, _, _, _, hb, hsub, lf => downBranchLFocO hb hsub lf
  | .somehow _, _, _, _, _, hb, hsub, lf => downBranchLFocO hb hsub lf

/-- **Branch transfer.** -/
def branchInO (φ : PLLFormula) {Γ : List Neg} {j : JD} {C : Neg}
    {b : List Neg} (hb : b ∈ invertPos (posOfO φ))
    (d : Inv (negOfO φ :: Γ) [] j C) : Inv (b ++ Γ) [] j C :=
  simHyp (H := negOfO φ)
    (fl := fun hs lf =>
      branchLFocO φ hb (fun X hX => hs X (List.mem_append_left _ hX)) lf)
    (fun _ hZ => List.mem_append_right b hZ) d

/-- **Hypothesis to pending positive.** -/
def shiftInO (φ : PLLFormula) {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (negOfO φ :: Γ) [] j C) : Inv Γ [posOfO φ] j C :=
  invBranches (posOfO φ) (fun _ hb => branchInO φ hb d)

/-- **FOCALIZATION FOR PLL, sequent form.**  Every cut-free `SCh`
derivation has a focused LJF◯ counterpart under the ◯-preserving
polarisation. -/
theorem focalizeSCO : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    PLLND.SCh n Γ C → Nonempty (Inv (Γ.map negOfO) [] .tru (negOfO C)) := by
  intro n Γ C d
  induction d with
  | @init n Γ a h => exact ⟨.stable (.rfoc (.init (List.mem_map_of_mem h)))⟩
  | @botL n Γ C h => exact ⟨nBotElim (negOfO C) (List.mem_map_of_mem h)⟩
  | @andR n Γ A B _ _ ih₁ ih₂ =>
      obtain ⟨d₁⟩ := ih₁; obtain ⟨d₂⟩ := ih₂
      exact ⟨.andR d₁ d₂⟩
  | @andL n Γ A B C h _ ih =>
      obtain ⟨d⟩ := ih
      have hAB : Neg.and (negOfO A) (negOfO B) ∈ Γ.map negOfO :=
        List.mem_map_of_mem h
      exact ⟨simHyp (H := negOfO B)
        (fl := fun hs lf => .lfoc (hs _ hAB) (.and2 lf)) (Sub.refl _)
        (simHyp (H := negOfO A)
          (fl := fun hs lf =>
            .lfoc (hs _ (List.mem_cons_of_mem _ hAB)) (.and1 lf))
          (Sub.refl _) d)⟩
  | @orR1 n Γ A B _ ih =>
      obtain ⟨d⟩ := ih
      exact ⟨.stable (stabOr1 (stabOfInvO A d))⟩
  | @orR2 n Γ A B _ ih =>
      obtain ⟨d⟩ := ih
      exact ⟨.stable (stabOr2 (stabOfInvO B d))⟩
  | @orL n Γ A B C h _ _ ih₁ ih₂ =>
      obtain ⟨d₁⟩ := ih₁; obtain ⟨d₂⟩ := ih₂
      have hAB : Neg.up (Pos.or (posOfO A) (posOfO B)) ∈ Γ.map negOfO :=
        List.mem_map_of_mem h
      refine ⟨upMerge (negOfO C) hAB (fun b hb => ?_)⟩
      have hb' : b ∈ invertPos (posOfO A) ++ invertPos (posOfO B) := hb
      exact
        if hA : b ∈ invertPos (posOfO A) then branchInO A hA d₁
        else branchInO B ((List.mem_append.mp hb').resolve_left hA) d₂
  | @impR n Γ A B _ ih =>
      obtain ⟨d⟩ := ih
      exact ⟨.impR (shiftInO A d)⟩
  | @impL n Γ A B C h _ _ ih₁ ih₂ =>
      obtain ⟨d₁⟩ := ih₁; obtain ⟨d₂⟩ := ih₂
      have hAB : Neg.imp (posOfO A) (negOfO B) ∈ Γ.map negOfO :=
        List.mem_map_of_mem h
      exact ⟨simHyp (H := negOfO B)
        (fl := fun {Δ'} {j'} _ hs lf =>
          .lfoc (hs _ hAB) (.impL (stabOfInvO A (d₁.wk hs)) lf))
        (Sub.refl _) d₂⟩
  | @laxR n Γ A _ ih =>
      -- prove the body TRULY, then coerce: `laxOf`, under `circR`
      obtain ⟨d⟩ := ih
      exact ⟨.circR (.stable (.laxOf (stabOfInvO A d)))⟩
  | @laxL n Γ A B h _ ih =>
      -- focus on the box; its body enters the inversion queue
      obtain ⟨d⟩ := ih
      have hA : Neg.circ (posOfO A) ∈ Γ.map negOfO :=
        List.mem_map_of_mem h
      exact ⟨.circR (.stable (.lfoc hA (.circL (shiftInO A (circInv d)))))⟩

/-- **Focalization for PLL**, natural-deduction form, via the repo's cut
elimination `PLLND.ND_to_SC`. -/
theorem focalizeO {Γ : List PLLFormula} {C : PLLFormula} (d : LaxND Γ C) :
    Nonempty (Inv (Γ.map negOfO) [] .tru (negOfO C)) :=
  match PLLND.ND_to_SC d with
  | ⟨_, s⟩ => focalizeSCO s

/-- **The converse arrow** — focalization completeness for PLL.  This
was `docs/ljfo-fidelity.md` §5's open item. -/
theorem FocalizationPLL :
    ∀ (Γ : List PLLFormula) (φ : PLLFormula),
      Nonempty (LaxND Γ φ) → Nonempty (Inv (Γ.map negOfO) [] .tru (negOfO φ)) :=
  fun _ _ h => h.elim focalizeO

/-- **THE BRIDGE: LJF◯ ⊢ ⟺ PLL ⊢.**  `←` is `Inv.sound` composed with
the round trip; `→` is `FocalizationPLL`. -/
theorem bridge_iff (Γ : List PLLFormula) (φ : PLLFormula) :
    Nonempty (LaxND Γ φ) ↔
      Nonempty (Inv (Γ.map negOfO) [] .tru (negOfO φ)) := by
  refine ⟨FocalizationPLL Γ φ, ?_⟩
  rintro ⟨d⟩
  have hd := Inv.sound d
  rw [eraseCtx_polarise, (erase_polarise φ).2] at hd
  exact ⟨hd⟩

/-! ## 5. The bridge in action

Two derivations that exercise the modal cases, so the erasure is
demonstrated and not merely typed. -/

/-- `⊢lax` really is `◯`: a truth-derivation coerced by `laxOf` erases
to `laxIntro`. -/
example : LaxND (eraseCtx [Neg.up (Pos.atom "p")]) (.somehow (.prop "p")) :=
  sound_lax (.laxOf (.rfoc (.init (List.mem_cons_self ..))))

/-- `circL` really is `laxElim`: focusing on a box at a lax goal erases
to `◯p ⊢ ◯p` built by `◯`-elimination. -/
example : LaxND (eraseCtx [Neg.circ (Pos.atom "p")]) (.somehow (.prop "p")) :=
  sound_lax (.lfoc (List.mem_cons_self ..)
    (.circL (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..)))))))

/-! ## 6. Pins

The bridge matches the LJFO development's own axiom profile: no
`Classical.choice`, so nothing here is proved by choice. -/

/--
info: 'LJFO.Stab.sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Stab.sound

/--
info: 'LJFO.Inv.sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Inv.sound

/--
info: 'LJFO.sound_tru' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms sound_tru

/--
info: 'LJFO.sound_lax' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms sound_lax

/--
info: 'LJFO.laxND_of_ljfo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms laxND_of_ljfo

/--
info: 'LJFO.not_ljfo_of_not_laxND' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_ljfo_of_not_laxND

/--
info: 'LJFO.erase_polarise' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms erase_polarise

/--
info: 'LJFO.eraseCtx_polarise' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms eraseCtx_polarise

/--
info: 'LJFO.focalizeSCO' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms focalizeSCO

/--
info: 'LJFO.FocalizationPLL' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FocalizationPLL

/--
info: 'LJFO.bridge_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms bridge_iff

end LJFO
