/-
LJF◯ → PLL: the ERASURE BRIDGE.

`LaxLogic/LJFOCore.lean` builds the lax-flagged focused calculus LJF◯
and proves a great deal ABOUT it, and `LJFOSearch.lean` relates the
fueled search to the calculus.  What has been missing is the arrow that
makes any of it mean something for PLL: a theorem relating LJF◯
derivability to `PLLND.LaxND`.  Without it, an LJF◯ verdict is a fact
about LJF◯ and nothing more.

This file supplies the SOUNDNESS direction:

    LJF◯ ⊢ ⟹ PLL ⊢

by erasing polarity (`erasePos`/`eraseNeg` — `↓`/`↑` vanish, `circ`
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

**Scope, stated.**  This is SOUNDNESS only.  The converse — every
PLL-derivable sequent has a focused LJF◯ derivation, i.e. focalization
completeness for PLL — is NOT proved here and remains OPEN
(`docs/ljfo-fidelity.md` §5).  So an LJF◯ *proof* now transfers to PLL;
an LJF◯ *failure* does not yet transfer.
-/
import LaxLogic.LJFOCore
import LaxLogic.PLLNDCore

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

end LJFO
