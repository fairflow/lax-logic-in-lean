/-
`CutInv` — the polarisation cells.

The refutation stage of route (B)'s `CutInv` work package
(`docs/ui-ljfo-clause-table.md` §4.19), answered FROM THE RULES with
designed witness cells.  The step list, the displayed sequents and the hand
analysis are in `docs/cutinv-cases.md`; this file carries the certificates.

Two blocks:

* **S1–S10, the ◯-free steps** (judgment `tru`, no `circ`): every cell is a
  kernel-checked `Inv` term.  Each is the smallest sequent that exercises
  one step of `focalizeSCO` with a shift inserted at the position that step
  is sensitive to — a POSITIVE DELAY `↓↑P` or a NEGATIVE DELAY `↑↓N`, the
  two shapes outside the image of `posOfO`/`negOfO`.

* **S11–S14, the ◯ steps**: `circR`, `circL`, `laxOf`, and the `lax`
  judgment itself.  S11–S13 pass.  **S14 REFUTES `PolInv`** — the statement
  the bridge route through PLL would need — with both parts certified: the
  erasure's `LaxND` term, and the emptiness of the focused sequent by an
  exhaustive `cases`.
-/
import LJF.OBridge
import Meta.Audit

namespace CutInvCells

open LJFO
open PLLND

/-! ## Abbreviations -/

/-- The atom `a`, positively. -/
abbrev pa : Pos := .atom "a"
/-- The atom `b`, positively. -/
abbrev pb : Pos := .atom "b"
/-- The atom `c`, positively. -/
abbrev pc : Pos := .atom "c"
/-- `↑a`. -/
abbrev na : Neg := .up pa
/-- `↑b`. -/
abbrev nb : Neg := .up pb
/-- `↑c`. -/
abbrev nc : Neg := .up pc

/-! # Block I — the ◯-free steps (S1–S10), judgment `tru`

Liang–Miller's "delays are inert" for the ◯-free fragment of LJF◯, one
designed cell at a time. -/

/-! ## S1 — `init` / identity -/

/-- **Cell 1.1** `↑↓↑a ⇒ᵗ ↑a`.  `RFocus.init` cannot fire: it demands
`↑(atom a) ∈ Γ` and the context holds `↑↓↑a`.  Left delay elimination —
`lfoc`, `LFoc.rel` (the only `LFoc` rule for a shifted hypothesis), `downL`
— puts `↑a` in the context, and then `init` fires. -/
def s1_hyp_delay : Inv [Neg.up (Pos.down na)] [] .tru na :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.rel (.downL (.stable (.rfoc (.init (List.mem_cons_self ..)))))))

/-- **Cell 1.2** `↑a ⇒ᵗ ↑↓↑a`.  Right delay introduction:
`Stab Γ j (↓N)` from `Inv Γ [] j N` by `rfoc`/`rel`. -/
def s1_goal_delay : Inv [na] [] .tru (Neg.up (Pos.down na)) :=
  .stable (.rfoc (.rel (.stable (.rfoc (.init (List.mem_cons_self ..))))))

/-- **Cell 1.3** `↓↑a ⊃ ↑b, ↑a ⇒ᵗ ↑b` — route (B)'s `simp` shape
`↓↑P′ ⊃ N` as a hypothesis.  `LFoc.impL`'s left premise `Stab Γ .tru (↓↑a)`
is discharged by `rfoc`/`rel`/`stable` over the ordinary `init`. -/
def s1_under_ant : Inv [Neg.imp (Pos.down na) nb, na] [] .tru nb :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.impL
      (.rfoc (.rel (.stable (.rfoc
        (.init (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
      (.rel (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..))))))))

/-! ## S2 — `botL` -/

/-- **Cell 2.1** `↑↓↑⊥ ⇒ᵗ ↑a`.  `nBotElim` demands `nBot = ↑⊥ ∈ Γ` and does
not apply; the delay is eliminated first, and the empty branch family of
`invertPos .fls` is `flsL`. -/
def s2_bot_delay : Inv [Neg.up (Pos.down nBot)] [] .tru na :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.rel (.downL (.stable (.lfoc (List.mem_cons_self ..) (.rel .flsL))))))

/-- **Cell 2.2** `↑↓↑⊥ ⇒ᵗ (↓↑a ⊃ ↑b)`.  The same elimination commuting past
`impR`/`downL`: the lemma must be stated with a non-empty inversion
queue. -/
def s2_bot_delay_imp :
    Inv [Neg.up (Pos.down nBot)] [] .tru (Neg.imp (Pos.down na) nb) :=
  .impR (.downL (.stable
    (.lfoc (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (.rel (.downL (.stable
        (.lfoc (List.mem_cons_self ..) (.rel .flsL))))))))

/-! ## S3 — `andR` -/

/-- **Cell 3.1** `↑a ⇒ᵗ ↑↓(↑a ∧ ↑a)`.  `andR` is NOT applicable — the goal
is `↑P`, so inversion is already over.  `stable`/`rfoc`/`rel` first, then
`andR`. -/
def s3_and_goal_delay :
    Inv [na] [] .tru (Neg.up (Pos.down (Neg.and na na))) :=
  .stable (.rfoc (.rel (.andR
    (.stable (.rfoc (.init (List.mem_cons_self ..))))
    (.stable (.rfoc (.init (List.mem_cons_self ..)))))))

/-- **Cell 3.2** `↑a ⇒ᵗ (↑↓↑a ∧ ↑a)` — the delay inside a conjunct of the
goal. -/
def s3_and_conj_delay :
    Inv [na] [] .tru (Neg.and (Neg.up (Pos.down na)) na) :=
  .andR s1_goal_delay (.stable (.rfoc (.init (List.mem_cons_self ..))))

/-! ## S4 — `andL` -/

/-- **Cell 4.1** `↑↓(↑a ∧ ↑b) ⇒ᵗ ↑a`.  `and1`/`and2` cannot fire on a
shifted hypothesis — `LFoc` on `↑Q` is `rel` only — so the conjunction is
re-inverted through the queue before it becomes focusable. -/
def s4_andL_delay :
    Inv [Neg.up (Pos.down (Neg.and na nb))] [] .tru na :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.rel (.downL (.stable (.lfoc (List.mem_cons_self ..)
      (.and1 (.rel (.atomL (.stable (.rfoc
        (.init (List.mem_cons_self ..))))))))))))

/-- **Cell 4.2** `(↑a ∧ ↑↓↑b) ⇒ᵗ ↑b` — the delay inside a conjunct of a
hypothesis, eliminated AFTER the projection: the two eliminations
interleave, so the transfer lemma is mutual with the `LFoc` traversal. -/
def s4_andL_inner :
    Inv [Neg.and na (Neg.up (Pos.down nb))] [] .tru nb :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.and2 (.rel (.downL (.stable (.rfoc
      (.init (List.mem_cons_self ..))))))))

/-! ## S5 — `orR` -/

/-- **Cell 5.1** `↑a ⇒ᵗ ↑(↓↑a ∨ b)`.  `stabOfInvO`'s six arms are indexed
by `φ : PLLFormula` and `↓↑a` is the polarisation of no `φ`; the general
replacement is `Stab Γ j P → Stab Γ j (↓↑P)` by `routeStab`. -/
def s5_or_disj_delay :
    Inv [na] [] .tru (Neg.up (Pos.or (Pos.down na) pb)) :=
  .stable (.rfoc (.or1 (.rel (.stable (.rfoc
    (.init (List.mem_cons_self ..)))))))

/-- **Cell 5.2** `↑b ⇒ᵗ ↑(↓↑a ∨ ↓↑b)` — both disjuncts delayed. -/
def s5_or_delay_both :
    Inv [nb] [] .tru (Neg.up (Pos.or (Pos.down na) (Pos.down nb))) :=
  .stable (.rfoc (.or2 (.rel (.stable (.rfoc
    (.init (List.mem_cons_self ..)))))))

/-! ## S6 — `orL`, and S7 — `impR` -/

/-- **Cell 6.1** `⇒ᵗ ↓↑(a ∨ b) ⊃ ↑(b ∨ a)` — the cell that shows what a
positive delay does.  Canonically `impR` would put the disjunction straight
into the inversion queue for `orL`.  With the delay, `impR` queues
`↓↑(a ∨ b)`, `downL` fires and the HYPOTHESIS `↑(a ∨ b)` appears; the case
split is recovered by LEFT FOCUS (`lfoc` + `LFoc.rel` returns the
disjunction to the queue) and only then `orL`.  That recovery is
`stableFire`/`upMerge`: the single branch `invertPos (↓↑P) = [[↑P]]` covers
every branch of `invertPos P`. -/
def s6_delay_hides_split :
    Inv [] [] .tru
      (Neg.imp (Pos.down (Neg.up (Pos.or pa pb))) (Neg.up (Pos.or pb pa))) :=
  .impR (.downL (.stable (.lfoc (List.mem_cons_self ..)
    (.rel (.orL
      (.atomL (.stable (.rfoc (.or2 (.init (List.mem_cons_self ..))))))
      (.atomL (.stable (.rfoc (.or1 (.init (List.mem_cons_self ..)))))))))))

/-- **Cell 6.2** `↓↑(a ∨ b) ⊃ ↑c, ↑a ⇒ᵗ ↑c` — the delay in an antecedent,
discharged by choosing a disjunct. -/
def s6_delay_ant_choice :
    Inv [Neg.imp (Pos.down (Neg.up (Pos.or pa pb))) nc, na] [] .tru nc :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.impL
      (.rfoc (.rel (.stable (.rfoc (.or1
        (.init (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))
      (.rel (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..))))))))

/-- **Cell 6.3** `↓↑(a ∨ b) ⊃ ↑c, ↑(a ∨ b) ⇒ᵗ ↑c` — the same antecedent
discharged by left-focusing a shifted hypothesis instead: the delay does
NOT force an early choice of disjunct. -/
def s6_delay_ant_hyp :
    Inv [Neg.imp (Pos.down (Neg.up (Pos.or pa pb))) nc,
         Neg.up (Pos.or pa pb)] [] .tru nc :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.impL
      (.rfoc (.rel (.stable (.lfoc
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (.rel (.orL
          (.atomL (.stable (.rfoc (.or1 (.init (List.mem_cons_self ..))))))
          (.atomL (.stable (.rfoc (.or2 (.init (List.mem_cons_self ..))))))))))))
      (.rel (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..))))))))

/-! ## S8 — `impL` -/

/-- **Cell 8.1** `↓(↓↑a ⊃ ↑b) ⊃ ↑c, ↑b ⇒ᵗ ↑c` — route (B)'s `dyk` shape
`↓(Q′ ⊃ N′) ⊃ N` with a delayed inner antecedent.  `impL`'s left premise is
a whole inversion phase (`impR`, `downL`) inside a focus. -/
def s8_dyk_delay :
    Inv [Neg.imp (Pos.down (Neg.imp (Pos.down na) nb)) nc, nb] [] .tru nc :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.impL
      (.rfoc (.rel (.impR (.downL (.stable (.rfoc
        (.init (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))
      (.rel (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..))))))))

/-- **Cell 8.2** `↓↑a ⊃ ↑↓↑b, ↑a ⇒ᵗ ↑b` — the negative delay in the
SUCCEDENT of the focused implication, where `LFoc.rel` re-enters inversion
after the focus. -/
def s8_succ_delay :
    Inv [Neg.imp (Pos.down na) (Neg.up (Pos.down nb)), na] [] .tru nb :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.impL
      (.rfoc (.rel (.stable (.rfoc
        (.init (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
      (.rel (.downL (.stable (.rfoc (.init (List.mem_cons_self ..))))))))

/-! ## S9/S10 — the two delays in isolation -/

/-- **Cell 10.2** `↑↓↑↓↑a ⇒ᵗ ↑a` — two stacked negative delays, eliminated
by two `lfoc`/`rel`/`downL` rounds.  The elimination is a recursion on the
formula, not a single unfolding. -/
def s10_double_delay :
    Inv [Neg.up (Pos.down (Neg.up (Pos.down na)))] [] .tru na :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.rel (.downL (.stable (.lfoc (List.mem_cons_self ..)
      (.rel (.downL (.stable (.rfoc
        (.init (List.mem_cons_self ..)))))))))))

/-! # Block II — the ◯ steps (S11–S14) -/

/-! ## S11 — `circR` (`laxR`) -/

/-- **Cell 11.1** `↑a ⇒ᵗ ◯↓↑a` — route (B)'s `◯↓↑P`, at `tru`.  `circR`
opens the lax phase with the delayed goal; `laxOf` closes it. -/
def s11_box_delay_body : Inv [na] [] .tru (Neg.circ (Pos.down na)) :=
  .circR (.stable (.laxOf (.rfoc (.rel (.stable (.rfoc
    (.init (List.mem_cons_self ..))))))))

/-- **Cell 11.2** `◯a ⇒ᵗ ◯↓↑a` — the composite route (B) walks: `circR`,
then `circL` on the box (available only at `lax`), its body into the queue,
`atomL`, and the delayed goal closed by `laxOf` over `init`. -/
def s11_box_from_box :
    Inv [Neg.circ pa] [] .tru (Neg.circ (Pos.down na)) :=
  .circR (.stable (.lfoc (List.mem_cons_self ..)
    (.circL (.atomL (.stable (.laxOf (.rfoc (.rel (.stable (.rfoc
      (.init (List.mem_cons_self ..))))))))))))

/-- **Cell 11.3** `⇒ᵗ ◯↓(↑⊥ ⊃ ↑⊥)` — a NEGATIVE delay at a lax goal.  After
`circR` the goal is `↑↓(⊥ ⊃ ⊥)` at `lax`; `rfoc`/`rel` would need
`Inv [] [] .lax (⊥ ⊃ ⊥)`, which is empty (S14), so the only route is
`laxOf`.  Contrast with cell 14.1: the same erasure `◯(⊥ ⊃ ⊥)`. -/
def s11_lax_neg_delay : Inv [] [] .tru (Neg.circ (Pos.down nTop)) :=
  .circR (.stable (.laxOf (.rfoc (.rel (.impR .flsL)))))

/-! ## S12 — `circL` (`laxL`) -/

/-- **Cell 12.1** `◯↓↑a ⇒ᵗ ◯a` — a delayed box body, opened by `circL`
and un-delayed by `downL` inside the lax phase. -/
def s12_circL_delay_body :
    Inv [Neg.circ (Pos.down na)] [] .tru (Neg.circ pa) :=
  .circR (.stable (.lfoc (List.mem_cons_self ..)
    (.circL (.downL (.stable (.laxOf (.rfoc
      (.init (List.mem_cons_self ..)))))))))

/-- **Cell 12.2** `◯a, ↓↑a ⊃ ↑b ⇒ᵗ ◯b` — `circL` then a delayed
implication antecedent inside the opened box.  This is `laxElim` followed by
`impElim`, focused. -/
def s12_circL_then_imp :
    Inv [Neg.circ pa, Neg.imp (Pos.down na) nb] [] .tru (Neg.circ pb) :=
  .circR (.stable (.lfoc (List.mem_cons_self ..)
    (.circL (.atomL (.stable (.laxOf
      (.lfoc (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_self ..)))
        (.impL
          (.rfoc (.rel (.stable (.rfoc (.init (List.mem_cons_self ..))))))
          (.rel (.atomL (.stable (.rfoc
            (.init (List.mem_cons_self ..))))))))))))))

/-- **Cell 12.3** `↑↓◯a ⇒ᵗ ◯a` — the box behind a NEGATIVE delay.
`LFoc.circL` demands a hypothesis literally `◯Q`, so it cannot fire; the
delay is eliminated first (`lfoc`/`rel`/`downL`) and only then is the box
focusable. -/
def s12_box_behind_delay :
    Inv [Neg.up (Pos.down (Neg.circ pa))] [] .tru (Neg.circ pa) :=
  .circR (.stable (.lfoc (List.mem_cons_self ..)
    (.rel (.downL (.stable (.lfoc (List.mem_cons_self ..)
      (.circL (.atomL (.stable (.laxOf (.rfoc
        (.init (List.mem_cons_self ..)))))))))))))

/-! ## S13 — `laxOf` -/

/-- **Cell 13.1** `↑a ⇒ᵗ ◯a` — `laxOf` bare: the truth-to-lax coercion. -/
def s13_laxOf : Inv [na] [] .tru (Neg.circ pa) :=
  .circR (.stable (.laxOf (.rfoc (.init (List.mem_cons_self ..)))))

/-- **Cell 13.2** `↓◯a ⊃ ↑b, ◯a ⇒ᵗ ↑b` — route (B)'s `cimp` shape
`↓◯Q′ ⊃ N`.  `impL`'s left premise is a complete modal derivation
(`circR`, `circL`, `laxOf`) inside a focus. -/
def s13_cimp :
    Inv [Neg.imp (Pos.down (Neg.circ pa)) nb, Neg.circ pa] [] .tru nb :=
  .stable (.lfoc (List.mem_cons_self ..)
    (.impL
      (.rfoc (.rel (.circR (.stable
        (.lfoc (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          (.circL (.atomL (.stable (.laxOf (.rfoc
            (.init (List.mem_cons_self ..))))))))))))
      (.rel (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..))))))))

/-- **Cell 13.3** `↑a ⇒ˡ ↑a` — the lax judgment reached directly, not
through `circR`.  Erasure `a ⊢ ◯a`. -/
def s13_lax_direct : Inv [na] [] .lax na :=
  .stable (.laxOf (.rfoc (.init (List.mem_cons_self ..))))

/-! ## S14 — the `lax` judgment itself: the REFUTATION

Inspect the constructors of `Inv` at `Ω = []`, `j = .lax` and a goal that is
neither `↑P` nor `◯P`:

* `impR` concludes at `.tru` — the flag is written into the rule;
* `andR` concludes at `.tru`;
* `circR` concludes `.circ _`;
* `stable` concludes `.up _`;
* `orL`, `flsL`, `downL`, `atomL` all require `Ω = _ :: _`.

No constructor applies.  (The development already records the fact:
`upMergeJ`'s docstring, `LJF/OCore.lean`, "at `lax` the goal can only be a
shift or a box — `⊃` and `∧` have no lax right rules".) -/

/-- `Inv Γ [] .lax (Q ⊃ N)` is EMPTY. -/
theorem lax_imp_empty (Γ : List Neg) (Q : Pos) (N : Neg) :
    Inv Γ [] .lax (.imp Q N) → False := fun d => by cases d

/-- `Inv Γ [] .lax (M ∧ N)` is EMPTY. -/
theorem lax_and_empty (Γ : List Neg) (M N : Neg) :
    Inv Γ [] .lax (.and M N) → False := fun d => by cases d

/-- **Cell 14.1, erasure half.**  `⌊nTop⌋ = ⊥ ⊃ ⊥` and
`goal .lax (⊥ ⊃ ⊥) = ◯(⊥ ⊃ ⊥)`, which PLL proves. -/
def s14_refute_nTop_erasure :
    LaxND (eraseCtx []) (goal .lax (eraseNeg nTop)) :=
  .laxIntro (.impIntro (.iden (List.mem_cons_self ..)))

/-- **Cell 14.2, erasure half.**  `a ⊢ ◯(a ∧ a)`. -/
def s14_refute_and_erasure :
    LaxND (eraseCtx [na]) (goal .lax (eraseNeg (Neg.and na na))) :=
  .laxIntro (.andIntro (.iden (List.mem_cons_self ..))
                       (.iden (List.mem_cons_self ..)))

/-- **Cell 14.3, the contrast.**  The SAME erasure `◯(⊥ ⊃ ⊥)`, at the same
flag, IS derivable once the goal carries its shift: `↑↓(↑⊥ ⊃ ↑⊥)`.  So the
failure below is about the JUDGMENT FORM, not about provability. -/
def s14_contrast : Inv [] [] .lax (Neg.up (Pos.down nTop)) :=
  .stable (.laxOf (.rfoc (.rel (.impR .flsL))))

/-- The statement the bridge route through PLL would need. -/
def PolInv : Prop :=
  ∀ (Γ : List Neg) (j : JD) (ψ : Neg),
    Nonempty (LaxND (eraseCtx Γ) (goal j (eraseNeg ψ))) →
    Nonempty (Inv Γ [] j ψ)

/-- **`PolInv` is REFUTED**, by cell 14.1: `Γ = []`, `j = lax`,
`ψ = ↑⊥ ⊃ ↑⊥`.  The erasure `⊢ ◯(⊥ ⊃ ⊥)` is PLL-derivable; the focused
sequent `⇒ˡ (↑⊥ ⊃ ↑⊥)` has no constructor. -/
theorem not_polInv : ¬ PolInv := by
  intro h
  obtain ⟨d⟩ := h [] .lax nTop ⟨s14_refute_nTop_erasure⟩
  cases d

/-- The second refuting cell, 14.2: `↑a ⇒ˡ (↑a ∧ ↑a)`. -/
theorem not_polInv' : ¬ PolInv := by
  intro h
  obtain ⟨d⟩ := h [na] .lax (Neg.and na na) ⟨s14_refute_and_erasure⟩
  cases d

/-! ### What this does to `CutInv`

`CutInv`'s second premise and its conclusion carry the SAME `j` and the SAME
`ψ`.  At `j = .lax` with `ψ` an `imp` or an `and` the premise is itself
empty, so those cases of `CutInv` hold vacuously and need no `PolInv`. -/

/-- `CutInv` at `j = lax`, `ψ = Q ⊃ M`: vacuous. -/
def cutinv_lax_imp (Γ Δ : List Neg) (N : Neg) (Q : Pos) (M : Neg)
    (_ : Inv Γ [] .tru N) (h : Inv (N :: Δ) [] .lax (.imp Q M)) :
    Inv (Γ ++ Δ) [] .lax (.imp Q M) := nomatch h

/-- `CutInv` at `j = lax`, `ψ = M₁ ∧ M₂`: vacuous. -/
def cutinv_lax_and (Γ Δ : List Neg) (N M₁ M₂ : Neg)
    (_ : Inv Γ [] .tru N) (h : Inv (N :: Δ) [] .lax (.and M₁ M₂)) :
    Inv (Γ ++ Δ) [] .lax (.and M₁ M₂) := nomatch h

/-- The restricted statement `CutInv` actually needs, at `tru`. -/
def PolInvT : Prop :=
  ∀ (Γ : List Neg) (ψ : Neg),
    Nonempty (LaxND (eraseCtx Γ) (eraseNeg ψ)) → Nonempty (Inv Γ [] .tru ψ)

/-- The restricted statement `CutInv` actually needs, at `lax`: only shifted
goals, the shape `circR` produces. -/
def PolInvL : Prop :=
  ∀ (Γ : List Neg) (P : Pos),
    Nonempty (LaxND (eraseCtx Γ) (.somehow (erasePos P))) →
    Nonempty (Inv Γ [] .lax (.up P))

/-- The `lax` box goal reduces to `PolInvL` by `circR`. -/
def circ_of_up {Γ : List Neg} {P : Pos} (d : Inv Γ [] .lax (.up P)) :
    Inv Γ [] .lax (.circ P) := .circR d

/-! ## Pins -/

/--
info: 'CutInvCells.s6_delay_hides_split' does not depend on any axioms
-/
#guard_msgs in
#print axioms s6_delay_hides_split

-- Every cell in this file is axiom-free.  The boundary is the bridge they
-- test: `Inv.sound` itself is at `[propext, Quot.sound]`.  Pinning it at
-- `[]` is the watched pin gate (see `docs/cutinv-cases.md` §6).
#axioms_within LJFO.Inv.sound [propext, Quot.sound]

#axioms_within s1_hyp_delay []
#axioms_within s1_goal_delay []
#axioms_within s1_under_ant []
#axioms_within s2_bot_delay []
#axioms_within s2_bot_delay_imp []
#axioms_within s3_and_goal_delay []
#axioms_within s3_and_conj_delay []
#axioms_within s4_andL_delay []
#axioms_within s4_andL_inner []
#axioms_within s5_or_disj_delay []
#axioms_within s5_or_delay_both []
#axioms_within s6_delay_hides_split []
#axioms_within s6_delay_ant_choice []
#axioms_within s6_delay_ant_hyp []
#axioms_within s8_dyk_delay []
#axioms_within s8_succ_delay []
#axioms_within s10_double_delay []

#axioms_within s11_box_delay_body []
#axioms_within s11_box_from_box []
#axioms_within s11_lax_neg_delay []
#axioms_within s12_circL_delay_body []
#axioms_within s12_circL_then_imp []
#axioms_within s12_box_behind_delay []
#axioms_within s13_laxOf []
#axioms_within s13_cimp []
#axioms_within s13_lax_direct []

#axioms_within s14_refute_nTop_erasure []
#axioms_within s14_refute_and_erasure []
#axioms_within s14_contrast []
#axioms_within cutinv_lax_imp []
#axioms_within cutinv_lax_and []

#axioms_within_pin lax_imp_empty
#axioms_within_pin lax_and_empty
#axioms_within_pin not_polInv
#axioms_within_pin not_polInv'

end CutInvCells
