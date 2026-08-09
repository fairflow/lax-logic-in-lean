/-!
# LJF◯: the lax-flagged focused calculus, and uniform interpolation for PLL

The ◯-extension of `LaxLogic/LJF.lean` (which stays green beside this file as
the IPC control), per `docs/ljfo-plan.md`.  Zero imports, deliberately: the
auditability property — no other calculus can carry any part of the proof —
is preserved from the IPC campaign.

Design (settled by `PLLFocused.lean` and the blocker exercise, corrected by
the paper pass):

* `Neg` gains `circ : Pos → Neg`; nothing else in the syntax.
* A flag `JD ::= tru | lax` on all four judgments.  Three rules are
  flag-specific: `circL` (left focus on a box, lax only — the modal
  content), `laxOf` (the truth-to-lax coercion at the stable judgment —
  `PLLFocused` lacks it and thereby misses `◯φ` for provable implicational
  `φ`; found by the identity port, recorded as plan §3-results (f)), and
  `circR` *sets* its premise to lax.  `impR`/`andR` are tru-only (at lax
  they would assert the converse of K, refuted in-repo).  `impL` proves its
  argument truly.  Everything else threads the flag.
* Contexts are persistent (`lfoc` selects by membership): the G4iLL
  contraction failure cannot arise, machine-checked at the blocker.
* The lax goal is definable (`Γ ⊢lax P` iff `Γ ⊢tru ↓◯P`-wise), so the
  interpolant recursion of Part 2 carries **no flag** — only the
  derivation traversals do.

Part 1 (this stage): syntax, judgments, weakening, identity, weights.
-/

namespace LJFO

/-! ## Polarised syntax -/

mutual
/-- Positive (synchronous) propositions — unchanged from `LJF`. -/
inductive Pos where
  | atom : String → Pos
  | fls  : Pos
  | or   : Pos → Pos → Pos
  | down : Neg → Pos
  deriving DecidableEq
/-- Negative (asynchronous) propositions; `circ` is the lax modality, with a
positive body (its right rule enters the lax phase, its left rule is the
lax-only focus). -/
inductive Neg where
  | up   : Pos → Neg
  | imp  : Pos → Neg → Neg
  | and  : Neg → Neg → Neg
  | circ : Pos → Neg
  deriving DecidableEq
end

/-- The judgment flag: `tru` for truth, `lax` for the lax judgment. -/
inductive JD where
  | tru : JD
  | lax : JD
  deriving DecidableEq

/-! ## The calculus -/

mutual

/-- A **stable sequent** at judgment `j`: focus right, focus on a
hypothesis, or — the coercion `laxOf` — establish a lax goal by proving it
truly.  `laxOf` is Pfenning–Davies `laxIntro` in focused form, placed at
the stable judgment, where phase transitions belong. -/
inductive Stab : List Neg → JD → Pos → Type
  | rfoc {Γ j P} : RFocus Γ j P → Stab Γ j P
  | lfoc {Γ j P N} (h : N ∈ Γ) : LFoc Γ N j P → Stab Γ j P
  | laxOf {Γ P} : Stab Γ .tru P → Stab Γ .lax P

/-- **Right focus** on a positive goal; every rule threads the flag. -/
inductive RFocus : List Neg → JD → Pos → Type
  | init {Γ j a} (h : Neg.up (Pos.atom a) ∈ Γ) : RFocus Γ j (.atom a)
  | or1 {Γ j P Q} : RFocus Γ j P → RFocus Γ j (.or P Q)
  | or2 {Γ j P Q} : RFocus Γ j Q → RFocus Γ j (.or P Q)
  | rel {Γ j N} : Inv Γ [] j N → RFocus Γ j (.down N)

/-- **Left focus** on a negative hypothesis.  `impL` proves its argument
truly; `circL` — the only rule with modal *content* — opens a box, at a
lax goal only.  This is `SC`'s "succedent must be `◯`-shaped", as a phase
condition. -/
inductive LFoc : List Neg → Neg → JD → Pos → Type
  | rel {Γ j Q P} : Inv Γ [Q] j (.up P) → LFoc Γ (.up Q) j P
  | impL {Γ j Q N P} : Stab Γ .tru Q → LFoc Γ N j P → LFoc Γ (.imp Q N) j P
  | and1 {Γ j M N P} : LFoc Γ M j P → LFoc Γ (.and M N) j P
  | and2 {Γ j M N P} : LFoc Γ N j P → LFoc Γ (.and M N) j P
  | circL {Γ Q P} : Inv Γ [Q] .lax (.up P) → LFoc Γ (.circ Q) .lax P

/-- **Inversion.**  The right rules for `⊃` and `∧` are tru-only (at lax
they would assert the converse of K); `circR` sets its premise to lax from
either flag; the `Ω`-processing rules thread the flag. -/
inductive Inv : List Neg → List Pos → JD → Neg → Type
  | impR {Γ Ω Q N} : Inv Γ (Q :: Ω) .tru N → Inv Γ Ω .tru (.imp Q N)
  | andR {Γ Ω M N} : Inv Γ Ω .tru M → Inv Γ Ω .tru N → Inv Γ Ω .tru (.and M N)
  | circR {Γ Ω j P} : Inv Γ Ω .lax (.up P) → Inv Γ Ω j (.circ P)
  | stable {Γ j P} : Stab Γ j P → Inv Γ [] j (.up P)
  | orL {Γ Ω j P Q N} : Inv Γ (P :: Ω) j N → Inv Γ (Q :: Ω) j N →
      Inv Γ (.or P Q :: Ω) j N
  | flsL {Γ Ω j N} : Inv Γ (.fls :: Ω) j N
  | downL {Γ Ω j M N} : Inv (M :: Γ) Ω j N → Inv Γ (.down M :: Ω) j N
  | atomL {Γ Ω j a N} : Inv (.up (.atom a) :: Γ) Ω j N →
      Inv Γ (.atom a :: Ω) j N

end

/-! ## Contexts: the subset relation -/

/-- `Γ'` contains everything in `Γ`. -/
def Sub (Γ Γ' : List Neg) : Prop := ∀ N, N ∈ Γ → N ∈ Γ'

namespace Sub

theorem refl (Γ : List Neg) : Sub Γ Γ := fun _ h => h

theorem trans {Γ Γ' Γ'' : List Neg} (h₁ : Sub Γ Γ') (h₂ : Sub Γ' Γ'') :
    Sub Γ Γ'' := fun N h => h₂ N (h₁ N h)

/-- Extending both sides by the same hypothesis. -/
theorem cons {Γ Γ' : List Neg} (X : Neg) (h : Sub Γ Γ') :
    Sub (X :: Γ) (X :: Γ') := by
  intro N hN
  rcases List.mem_cons.mp hN with rfl | hN
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (h N hN)

/-- Extending the target. -/
theorem grow {Γ : List Neg} (X : Neg) : Sub Γ (X :: Γ) :=
  fun _ h => List.mem_cons_of_mem _ h

end Sub

/-! ## Weakening -/

mutual

/-- Weakening of a stable sequent. -/
def Stab.wk : {Γ Γ' : List Neg} → {j : JD} → {P : Pos} →
    Sub Γ Γ' → Stab Γ j P → Stab Γ' j P
  | _, _, _, _, H, .rfoc d   => .rfoc (RFocus.wk H d)
  | _, _, _, _, H, .lfoc h d => .lfoc (H _ h) (LFoc.wk H d)
  | _, _, _, _, H, .laxOf d  => .laxOf (Stab.wk H d)

/-- Weakening under right focus. -/
def RFocus.wk : {Γ Γ' : List Neg} → {j : JD} → {P : Pos} →
    Sub Γ Γ' → RFocus Γ j P → RFocus Γ' j P
  | _, _, _, _, H, .init h => .init (H _ h)
  | _, _, _, _, H, .or1 d  => .or1 (RFocus.wk H d)
  | _, _, _, _, H, .or2 d  => .or2 (RFocus.wk H d)
  | _, _, _, _, H, .rel d  => .rel (Inv.wk H d)

/-- Weakening under left focus. -/
def LFoc.wk : {Γ Γ' : List Neg} → {N : Neg} → {j : JD} → {P : Pos} →
    Sub Γ Γ' → LFoc Γ N j P → LFoc Γ' N j P
  | _, _, _, _, _, H, .rel d    => .rel (Inv.wk H d)
  | _, _, _, _, _, H, .impL a d => .impL (Stab.wk H a) (LFoc.wk H d)
  | _, _, _, _, _, H, .and1 d   => .and1 (LFoc.wk H d)
  | _, _, _, _, _, H, .and2 d   => .and2 (LFoc.wk H d)
  | _, _, _, _, _, H, .circL d  => .circL (Inv.wk H d)

/-- Weakening of an inversion sequent. -/
def Inv.wk : {Γ Γ' : List Neg} → {Ω : List Pos} → {j : JD} → {N : Neg} →
    Sub Γ Γ' → Inv Γ Ω j N → Inv Γ' Ω j N
  | _, _, _, _, _, H, .impR d   => .impR (Inv.wk H d)
  | _, _, _, _, _, H, .andR d e => .andR (Inv.wk H d) (Inv.wk H e)
  | _, _, _, _, _, H, .circR d  => .circR (Inv.wk H d)
  | _, _, _, _, _, H, .stable d => .stable (Stab.wk H d)
  | _, _, _, _, _, H, .orL d e  => .orL (Inv.wk H d) (Inv.wk H e)
  | _, _, _, _, _, _, .flsL     => .flsL
  | _, _, _, _, _, H, .downL d  => .downL (Inv.wk (Sub.cons _ H) d)
  | _, _, _, _, _, H, .atomL d  => .atomL (Inv.wk (Sub.cons _ H) d)

end

/-- A tru-stable sequent serves at either judgment (`laxOf` when needed). -/
def Stab.ofTru : {Γ : List Neg} → {P : Pos} → (j : JD) →
    Stab Γ .tru P → Stab Γ j P
  | _, _, .tru, s => s
  | _, _, .lax, s => .laxOf s

/-! ## Size -/

mutual
/-- Size of a positive. -/
def sizePos : Pos → Nat
  | .atom _  => 1
  | .fls     => 1
  | .or P Q  => sizePos P + sizePos Q + 1
  | .down N  => sizeNeg N + 1
/-- Size of a negative.  `circ` costs one, like a shift. -/
def sizeNeg : Neg → Nat
  | .up P    => sizePos P + 1
  | .imp P N => sizePos P + sizeNeg N + 1
  | .and M N => sizeNeg M + sizeNeg N + 1
  | .circ P  => sizePos P + 1
end

theorem sizePos_pos (P : Pos) : 0 < sizePos P := by
  cases P <;> simp [sizePos] <;> omega

theorem sizeNeg_pos (N : Neg) : 0 < sizeNeg N := by
  cases N <;> simp [sizeNeg] <;> omega

/-! ## Identity expansion

As in `LJF`, with one refinement forced by the flags: the right focus a
`posRestore` continuation receives is always **tru** (identity's own right
focus never needs the lax phase), while the judgment of the sequent being
built is free — the leaves coerce with `Stab.ofTru`.  `idNegK`/`idNeg` are
tru-only (`impR` is), which is no loss: lax goals are positive. -/

mutual

/-- **Left inversion of a positive returns it on the right**, at any
judgment, the returned focus at `tru`. -/
def posRestore (Q : Pos) (Γ : List Neg) (Ω : List Pos) {j : JD} (N : Neg)
    (k : ∀ Γ', Sub Γ Γ' → RFocus Γ' .tru Q → Inv Γ' Ω j N) :
    Inv Γ (Q :: Ω) j N :=
  match Q, k with
  | .atom a, k =>
      .atomL (k (.up (.atom a) :: Γ) (Sub.grow _) (.init (List.mem_cons_self ..)))
  | .fls, _ => .flsL
  | .down M, k =>
      .downL (k (M :: Γ) (Sub.grow _)
        (.rel (idNegK M (M :: Γ)
          (fun _ _ _ hs lf => .lfoc (hs _ (List.mem_cons_self ..)) lf))))
  | .or P₁ P₂, k =>
      .orL (posRestore P₁ Γ Ω N (fun Γ' hs r => k Γ' hs (.or1 r)))
           (posRestore P₂ Γ Ω N (fun Γ' hs r => k Γ' hs (.or2 r)))
termination_by sizePos Q
decreasing_by
  all_goals simp_wf
  all_goals simp only [sizePos]
  all_goals omega

/-- **A usable negative is a provable negative** — truly.  The continuation
turns a left focus on `N` *at any judgment* into a stable sequent: the flag
generality is forced by the `circ` case, whose left focus (`circL`) exists
only at lax.  That case is the one genuinely new clause: to prove `◯P`,
enter the lax phase (`circR`), left-focus the usable `◯P` through the
continuation, and restore the returned `P` — coercing the leaf with
`laxOf`. -/
def idNegK (N : Neg) (Γ : List Neg)
    (k : ∀ Γ' (j : JD) P, Sub Γ Γ' → LFoc Γ' N j P → Stab Γ' j P) :
    Inv Γ [] .tru N :=
  match N, k with
  | .up P, k =>
      .stable (k Γ .tru P (Sub.refl Γ)
        (.rel (posRestore P Γ [] (.up P) (fun _ _ r => .stable (.rfoc r)))))
  | .imp Q M, k =>
      .impR (posRestore Q Γ [] M (fun Γ' hs r =>
        idNegK M Γ' (fun Γ'' j P hs' lf =>
          k Γ'' j P (Sub.trans hs hs') (.impL (.rfoc (RFocus.wk hs' r)) lf))))
  | .and M₁ M₂, k =>
      .andR (idNegK M₁ Γ (fun Γ' j P hs lf => k Γ' j P hs (.and1 lf)))
            (idNegK M₂ Γ (fun Γ' j P hs lf => k Γ' j P hs (.and2 lf)))
  | .circ P, k =>
      .circR (.stable (k Γ .lax P (Sub.refl Γ)
        (.circL (posRestore P Γ [] (.up P)
          (fun _ _ r => .stable (.laxOf (.rfoc r)))))))
termination_by sizeNeg N
decreasing_by
  all_goals simp_wf
  all_goals simp only [sizeNeg]
  all_goals omega

end

/-- **Identity, negative form**: every hypothesis proves itself, truly. -/
def idNeg (N : Neg) (Γ : List Neg) (h : N ∈ Γ) : Inv Γ [] .tru N :=
  idNegK N Γ (fun _ _ _ hs lf => .lfoc (hs _ h) lf)

/-- **Identity, positive form**: `P ⇒ P` at any judgment, `P` inverted on
the left and focused (truly) on the right. -/
def idPos (P : Pos) (Γ : List Neg) (j : JD) : Inv Γ [P] j (.up P) :=
  posRestore P Γ [] (.up P) (fun _ _ r => .stable (Stab.ofTru j (.rfoc r)))

/-! ## The weight -/

mutual
/-- Weight of a positive — unchanged from `LJF`. -/
def wPos : Pos → Nat
  | .atom _ => 1
  | .fls    => 1
  | .or P Q => wPos P + wPos Q + 1
  | .down M => wNeg M + 1
/-- Weight of a negative.  `circ` costs `+1`: opening a box moves
`3^{wP+1}` out of the station and `2·3^{wP}` into the pending side, and
`2·3^w < 3^{w+1}` — the same inequality that pays for the atom fire. -/
def wNeg : Neg → Nat
  | .up P    => wPos P
  | .imp Q N => wPos Q + wNeg N + 1
  | .and M N => wNeg M + wNeg N + 3
  | .circ P  => wPos P + 1
end

theorem wPos_pos (P : Pos) : 0 < wPos P := by
  cases P <;> simp [wPos] <;> omega

theorem wNeg_pos (N : Neg) : 0 < wNeg N := by
  cases N with
  | up P => simpa [wNeg] using wPos_pos P
  | imp Q N => simp only [wNeg]; omega
  | and M N => simp only [wNeg]; omega
  | circ P => simpa [wNeg] using wPos_pos P

/-! ## Standing test 1: the G4iLL blocker

`◯((◯p→r)→◯p), ◯p→r ⊢ r` — PLL-provable, G4iLL-unprovable — re-derived
inside LJF◯ itself, so every rebuild re-checks it.  Ported from
`wip/ljf-lax-blocker.lean` (which proved it for `PLLFocused`); the term is
unchanged: `laxOf` is never needed here, and the two left-focusings of
`◯p→r` are free because contexts are persistent. -/

namespace BlockerTest

variable (p r : String)

/-- `◯p`. -/
abbrev oP : Neg := .circ (.atom p)

/-- `◯p → r`. -/
abbrev hyp : Neg := .imp (.down (oP p)) (.up (.atom r))

/-- `(◯p→r) → ◯p`. -/
abbrev chi : Neg := .imp (.down (hyp p r)) (oP p)

/-- `◯((◯p→r)→◯p)`, as `◯(↓χ)`. -/
abbrev bchi : Neg := .circ (.down (chi p r))

/-- Continuation closing goal `r` once `↑r` is released from the focus. -/
def closeR {Γ : List Neg} {j : JD} : LFoc Γ (.up (.atom r)) j (.atom r) :=
  .rel (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..)))))

/-- `Γ ⊢lax p` whenever `◯p ∈ Γ`. -/
def closeOP {Γ : List Neg} (h : oP p ∈ Γ) : Stab Γ .lax (.atom p) :=
  .lfoc h (.circL (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..))))))

/-- `Γ ⊢tru ↓◯p` whenever `◯p ∈ Γ`. -/
def downOP {Γ : List Neg} (h : oP p ∈ Γ) : Stab Γ .tru (.down (oP p)) :=
  .rfoc (.rel (.circR (.stable (closeOP p h))))

/-- The inner sequent — the **second use** of `◯p→r`. -/
def innerR : Stab [oP p, chi p r, bchi p r, hyp p r] .tru (.atom r) :=
  .lfoc
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (.impL (downOP p (List.mem_cons_self ..)) (closeR r))

/-- `χ, ◯χ′, ◯p→r ⊢tru ↓(◯p→r)`. -/
def argHyp : Stab [chi p r, bchi p r, hyp p r] .tru (.down (hyp p r)) :=
  .rfoc (.rel (.impR (.downL (.stable (innerR p r)))))

/-- The lax core `◯χ′, ◯p→r ⊢lax p`. -/
def laxCore : Stab [bchi p r, hyp p r] .lax (.atom p) :=
  .lfoc (List.mem_cons_self ..)
    (.circL (.downL (.stable
      (.lfoc (List.mem_cons_self ..)
        (.impL (argHyp p r)
          (.circL (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..)))))))))))

/-- **The G4iLL blocker is LJF◯-derivable.** -/
def blocker : Stab [bchi p r, hyp p r] .tru (.atom r) :=
  .lfoc (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (.impL (.rfoc (.rel (.circR (.stable (laxCore p r))))) (closeR r))

end BlockerTest

end LJFO

/-! ### Axiom audit -/

/-- info: 'LJFO.BlockerTest.blocker' does not depend on any axioms -/
#guard_msgs in
#print axioms LJFO.BlockerTest.blocker

/-- info: 'LJFO.idNeg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.idNeg
