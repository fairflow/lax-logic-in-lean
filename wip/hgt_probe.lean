import LJF.OFuelPFamKit

/-! A cheap bench for the two farms of `LJF/OFuelPFamKit.lean`: one
`example` per edge class of the parking family, stated exactly as the
goal is presented where the farm meets it.  Elaborating this file costs
seconds, where `LJF.OFuelPFam` costs half an hour.

Part 1 is the μ founding the family stands on (`LJF/OFuelPFam.lean`):
each goal as `decreasing_by` presents it after `Prod.Lex.left` (strict) or
inside `lex3_of_le` (non-increasing).

Part 2 is the budget founding of Part 4c of the kit: each goal as the
`autoParam` of a budget bound presents it at a CALL SITE — the callee's
bound, with the caller's in the context and the callee's budget as the
step lemma leaves it (`n - 1` where the edge is strict, `n` where it is
not, and likewise `w`).  The height goals `hgt_dec` sees after
`refine bud_lt hbn ?_` are exactly Part 1's; the station goals `ljf_wt`
sees are exactly those `ljf_dec_e`/`ljf_dec_a` see after `simp_wf`.  The
budget founding is groundwork, not in use — the kit's Part 4c says why. -/

namespace LJFO

variable {p : String}

/-! # Part 1: the μ founding, as `ljf_dec_h` meets it -/

/-! ### Goal inversion — the three sites `UEntryQ` failed on -/

example {Γ Γ₂ : List Neg} {Q : Pos} {N : Neg}
    (d₁ : Inv Γ [Q] .tru N) (b : List Neg) (hb : b ∈ invertPos Q)
    (H : Sub (b ++ Γ) Γ₂) :
    hgtI ((extract [] d₁ b hb).wk H) < hgtI (Inv.impR d₁) := by hgt_dec

example {Γ Γ₂ : List Neg} {Q : Pos} {N : Neg}
    (d₁ : Inv Γ [Q] .tru N) (b : List Neg) (hb : b ∈ invertPos Q)
    (H : Sub (b ++ Γ) Γ₂) :
    hgtI ((extract [] d₁ b hb).wk H) ≤ hgtI (Inv.impR d₁) := by hgt_dec

/-! ### The antecedent dispatch, native (Step C's new sites) -/

example {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos}
    (h : Neg.imp Q N ∈ Γ) (s_d : Stab Γ .tru Q) (lf' : LFoc Γ N j P) :
    hgtI (Inv.stable s_d) < hgtS (Stab.lfoc h (.impL s_d lf')) := by hgt_dec

/-! ### The four `∀p` → `∃p` calls the merge makes recursive -/

example {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos}
    (h : Neg.imp Q N ∈ Γ) (s_c : Stab Γ .tru Q) (lf' : LFoc Γ N j P) :
    hgtS s_c < hgtS (Stab.lfoc h (.impL s_c lf')) := by hgt_dec

example {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos}
    (s : Stab Γ .tru Q) (lf : LFoc Γ N j P) :
    hgtS s < hgtL (LFoc.impL s lf) := by hgt_dec

example {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos}
    {M : Neg} {P₀ : Pos} {j₀ : JD}
    (s : Stab Γ .tru Q) (lf : LFoc Γ N j P) (lfP : LFoc Γ M j₀ P₀) :
    hgtS s < hgtL (LFoc.impL s lf) + hgtL lfP := by hgt_dec

/-! ### Parking, phase change, weakening -/

example {Γ Γ' : List Neg} {Ω : List Pos} {j : JD} {N : Neg}
    (H : Sub Γ Γ') (d : Inv Γ Ω j N) : hgtI (Inv.wk H d) ≤ hgtI d := by hgt_dec

example {Γ : List Neg} {j : JD} {P : Pos} (s : Stab Γ j P) :
    hgtS s ≤ hgtI (Inv.stable s) := by hgt_dec

example {Γ : List Neg} {j : JD} {P : Pos} (r : RFocus Γ j P) :
    hgtR r ≤ hgtS (Stab.rfoc r) := by hgt_dec

example {Γ : List Neg} {N : Neg} {j : JD} {P : Pos}
    (h : N ∈ Γ) (lf : LFoc Γ N j P) : hgtL lf ≤ hgtS (Stab.lfoc h lf) := by
  hgt_dec

/-! ### The non-increasing processing transformers -/

example {P₁ Q₁ : Pos} {Γ Γ'' : List Neg} {j : JD} {C : Neg}
    (d : Inv ((Neg.up (.or P₁ Q₁)) :: Γ) [] j C)
    (b : List Neg) (hb : b ∈ invertPos (Pos.or P₁ Q₁))
    (S : Sub Γ ((Neg.up (.or P₁ Q₁)) :: Γ)) (S' : Sub (b ++ Γ) Γ'') :
    hgtI ((invUp d b hb).wk S') ≤ hgtI d := by hgt_dec

example {M N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.and M N :: Γ) [] j C) {Γ'' : List Neg}
    (S' : Sub (M :: N :: Γ) Γ'') :
    hgtI ((invAndHyp d).wk S') ≤ hgtI d := by hgt_dec

example {N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp .fls N :: Γ) [] j C) : hgtI (invImpFls d) ≤ hgtI d := by
  hgt_dec

example {a : String} {N : Neg} {done rest Δext : List Neg} {j : JD} {C : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done)
    (d : Inv (done ++ Δext) [] j C) : hgtI (invFireHyp h d) ≤ hgtI d := by
  hgt_dec

/-! ### The fire continuation, the box row, the two release sites -/

example {Γ Γ' : List Neg} {j : JD} {Q Q₀ : Pos} {N : Neg} {P : Pos}
    {rest K : List Neg} (h : Neg.imp Q N ∈ Γ)
    (s_d : Stab Γ .tru Q) (lf' : LFoc Γ N j P) (S : Sub Γ (N :: Γ'))
    (h' : N ∈ N :: Γ')
    (hsplit : ∀ Z ∈ Γ', Z = Neg.imp Q₀ N ∨ Z ∈ rest ∨ Z ∈ K) :
    hgtI (fireClean hsplit (.stable (.lfoc h' (lf'.wk S))))
      < hgtS (Stab.lfoc h (.impL s_d lf')) := by hgt_dec

example {Γ Γ' : List Neg} {Q P : Pos} {rest K : List Neg}
    (h : Neg.circ Q ∈ Γ) (d : Inv Γ [Q] .lax (.up P))
    (S : Sub Γ (Neg.up Q :: Γ')) (h' : Neg.up Q ∈ Neg.up Q :: Γ')
    (hsplit : ∀ Z ∈ Γ', Z = Neg.circ Q ∨ Z ∈ rest ∨ Z ∈ K) :
    hgtI (boxClean hsplit (.stable (.lfoc h' (.rel (d.wk S)))))
      ≤ hgtS (Stab.lfoc h (.circL d)) := by hgt_dec

example {Δ : List Neg} {P' : Pos} (s : Stab Δ .tru (.down (.up P'))) :
    hgtI (laxReleaseUp s) < hgtS (Stab.laxOf s) := by hgt_dec

example {Δ : List Neg} {P' : Pos} (s : Stab Δ .tru (.down (.circ P'))) :
    hgtI (laxReleaseCirc s) < hgtS (Stab.laxOf s) := by hgt_dec

/-! ### The `p`-eliminator fire: the extra derivation `lfP` in the
measure, and the atom cast -/

example {Γ Γ' rest K : List Neg} {j : JD} {P₀ : Pos} {M N_b : Neg}
    {c : String} {a b : String}
    (hab : b = a)
    (h : Neg.imp (.atom c) N_b ∈ Γ) (s_b : Stab Γ .tru (.atom c))
    (lf_b : LFoc Γ N_b .tru (.atom b)) (lfP : LFoc Γ M j P₀)
    (h' : Neg.imp (.atom a) M ∈ N_b :: Γ')
    (h'' : N_b ∈ N_b :: Γ')
    (S : Sub Γ (N_b :: Γ'))
    (hsplit : ∀ Z ∈ Γ', Z = Neg.imp (.atom c) N_b ∨ Z ∈ rest ∨ Z ∈ K) :
    hgtI (fireClean hsplit (.stable (.lfoc h'
        (.impL (stabAtomCast hab (Stab.lfoc h'' (lf_b.wk S))) (lfP.wk S)))))
      < hgtS (Stab.lfoc h (.impL s_b lf_b)) + hgtL lfP := by hgt_dec

/-! # Part 2: the budget founding, as the call sites meet it -/

/-! ### The height side, `ljf_bud_h`

`hbn` is the caller's bound; the goal is the callee's, at `n - 1` where
the edge is height-strict and at `n` where it is not. -/

/-! #### Goal inversion — `UEntryQ`'s `.impR` arm into `aMinQ` (strict) -/

example {Γ Γ₂ : List Neg} {Q : Pos} {N : Neg} {n : Nat}
    (d₁ : Inv Γ [Q] .tru N) (b : List Neg) (hb : b ∈ invertPos Q)
    (H : Sub (b ++ Γ) Γ₂) (hbn : hgtI (Inv.impR d₁) < n) :
    hgtI ((extract [] d₁ b hb).wk H) < n - 1 := by ljf_bud_h

/-! #### The antecedent dispatch, native (strict) -/

example {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos} {n : Nat}
    (h : Neg.imp Q N ∈ Γ) (s_d : Stab Γ .tru Q) (lf' : LFoc Γ N j P)
    (hbn : hgtS (Stab.lfoc h (.impL s_d lf')) < n) :
    hgtI (Inv.stable s_d) < n - 1 := by ljf_bud_h

/-! #### The four `∀p` → `∃p` calls the merge makes recursive (strict) -/

example {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos} {n : Nat}
    (h : Neg.imp Q N ∈ Γ) (s_c : Stab Γ .tru Q) (lf' : LFoc Γ N j P)
    (hbn : hgtS (Stab.lfoc h (.impL s_c lf')) < n) :
    hgtS s_c < n - 1 := by ljf_bud_h

example {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos} {n : Nat}
    (s : Stab Γ .tru Q) (lf : LFoc Γ N j P)
    (hbn : hgtL (LFoc.impL s lf) < n) : hgtS s < n - 1 := by ljf_bud_h

example {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos} {n : Nat}
    {M : Neg} {P₀ : Pos} {j₀ : JD}
    (s : Stab Γ .tru Q) (lf : LFoc Γ N j P) (lfP : LFoc Γ M j₀ P₀)
    (hbn : hgtL (LFoc.impL s lf) + hgtL lfP < n) :
    hgtS s < n - 1 := by ljf_bud_h

/-! #### Parking, phase change, weakening — the height does NOT drop, so
the budget is kept and the station or the `sizeOf` pays -/

example {Γ Γ' : List Neg} {Ω : List Pos} {j : JD} {N : Neg} {n : Nat}
    (H : Sub Γ Γ') (d : Inv Γ Ω j N) (hbn : hgtI d < n) :
    hgtI (Inv.wk H d) < n := by ljf_bud_h

example {Γ : List Neg} {j : JD} {P : Pos} {n : Nat} (s : Stab Γ j P)
    (hbn : hgtI (Inv.stable s) < n) : hgtS s < n := by ljf_bud_h

example {Γ : List Neg} {j : JD} {P : Pos} {n : Nat} (r : RFocus Γ j P)
    (hbn : hgtS (Stab.rfoc r) < n) : hgtR r < n := by ljf_bud_h

example {Γ : List Neg} {N : Neg} {j : JD} {P : Pos} {n : Nat}
    (h : N ∈ Γ) (lf : LFoc Γ N j P) (hbn : hgtS (Stab.lfoc h lf) < n) :
    hgtL lf < n := by ljf_bud_h

/-! #### The entry into the `p`-eliminator group: the height is EXACT,
the extra derivation `lfP` in the measure and all -/

example {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos} {n : Nat}
    (h : Neg.imp Q N ∈ Γ) (s_a : Stab Γ .tru Q) (lf' : LFoc Γ N j P)
    (hbn : hgtS (Stab.lfoc h (.impL s_a lf')) < n) :
    hgtS s_a + hgtL lf' < n := by ljf_bud_h

/-! #### The non-increasing processing transformers -/

example {P₁ Q₁ : Pos} {Γ Γ'' : List Neg} {j : JD} {C : Neg} {n : Nat}
    (d : Inv ((Neg.up (.or P₁ Q₁)) :: Γ) [] j C)
    (b : List Neg) (hb : b ∈ invertPos (Pos.or P₁ Q₁))
    (S' : Sub (b ++ Γ) Γ'') (hbn : hgtI d < n) :
    hgtI ((invUp d b hb).wk S') < n := by ljf_bud_h

example {M N : Neg} {Γ : List Neg} {j : JD} {C : Neg} {n : Nat}
    (d : Inv (.and M N :: Γ) [] j C) {Γ'' : List Neg}
    (S' : Sub (M :: N :: Γ) Γ'') (hbn : hgtI d < n) :
    hgtI ((invAndHyp d).wk S') < n := by ljf_bud_h

example {N : Neg} {Γ : List Neg} {j : JD} {C : Neg} {n : Nat}
    (d : Inv (.imp .fls N :: Γ) [] j C) (hbn : hgtI d < n) :
    hgtI (invImpFls d) < n := by ljf_bud_h

example {a : String} {N : Neg} {done rest Δext : List Neg} {j : JD} {C : Neg}
    {n : Nat} (h : (Neg.imp (.atom a) N, rest) ∈ splits done)
    (d : Inv (done ++ Δext) [] j C) (hbn : hgtI d < n) :
    hgtI (invFireHyp h d) < n := by ljf_bud_h

/-! #### The fire continuation, the box row, the two release sites -/

example {Γ Γ' : List Neg} {j : JD} {Q Q₀ : Pos} {N : Neg} {P : Pos}
    {rest K : List Neg} {n : Nat} (h : Neg.imp Q N ∈ Γ)
    (s_d : Stab Γ .tru Q) (lf' : LFoc Γ N j P) (S : Sub Γ (N :: Γ'))
    (h' : N ∈ N :: Γ')
    (hsplit : ∀ Z ∈ Γ', Z = Neg.imp Q₀ N ∨ Z ∈ rest ∨ Z ∈ K)
    (hbn : hgtS (Stab.lfoc h (.impL s_d lf')) < n) :
    hgtI (fireClean hsplit (.stable (.lfoc h' (lf'.wk S)))) < n - 1 := by
  ljf_bud_h

example {Γ Γ' : List Neg} {Q P : Pos} {rest K : List Neg} {n : Nat}
    (h : Neg.circ Q ∈ Γ) (d : Inv Γ [Q] .lax (.up P))
    (S : Sub Γ (Neg.up Q :: Γ')) (h' : Neg.up Q ∈ Neg.up Q :: Γ')
    (hsplit : ∀ Z ∈ Γ', Z = Neg.circ Q ∨ Z ∈ rest ∨ Z ∈ K)
    (hbn : hgtS (Stab.lfoc h (.circL d)) < n) :
    hgtI (boxClean hsplit (.stable (.lfoc h' (.rel (d.wk S))))) < n := by
  ljf_bud_h

example {Δ : List Neg} {P' : Pos} {n : Nat}
    (s : Stab Δ .tru (.down (.up P'))) (hbn : hgtS (Stab.laxOf s) < n) :
    hgtI (laxReleaseUp s) < n - 1 := by ljf_bud_h

example {Δ : List Neg} {P' : Pos} {n : Nat}
    (s : Stab Δ .tru (.down (.circ P'))) (hbn : hgtS (Stab.laxOf s) < n) :
    hgtI (laxReleaseCirc s) < n - 1 := by ljf_bud_h

/-! #### The `p`-eliminator fire: the extra derivation `lfP` in the
measure, and the atom cast -/

example {Γ Γ' rest K : List Neg} {j : JD} {P₀ : Pos} {M N_b : Neg}
    {c : String} {a b : String} {n : Nat}
    (hab : b = a)
    (h : Neg.imp (.atom c) N_b ∈ Γ) (s_b : Stab Γ .tru (.atom c))
    (lf_b : LFoc Γ N_b .tru (.atom b)) (lfP : LFoc Γ M j P₀)
    (h' : Neg.imp (.atom a) M ∈ N_b :: Γ')
    (h'' : N_b ∈ N_b :: Γ')
    (S : Sub Γ (N_b :: Γ'))
    (hsplit : ∀ Z ∈ Γ', Z = Neg.imp (.atom c) N_b ∨ Z ∈ rest ∨ Z ∈ K)
    (hbn : hgtS (Stab.lfoc h (.impL s_b lf_b)) + hgtL lfP < n) :
    hgtI (fireClean hsplit (.stable (.lfoc h'
        (.impL (stabAtomCast hab (Stab.lfoc h'' (lf_b.wk S))) (lfP.wk S)))))
      < n - 1 := by ljf_bud_h

/-! ### The station side, `ljf_bud_w`

`hbw` is the caller's bound.  A height-strict call takes a FRESH station
budget (`bud_fresh`), so only the height-preserving edges appear here. -/

/-! #### Parking, `∃p` (one goal offset) and `∀p` (two) -/

example {todo done : List Neg} {X : Neg} {w : Nat}
    (hbw : 2 * sum3 (X :: todo) + sum3 done + 1 < w) :
    2 * sum3 todo + sum3 (X :: done) + 1 < w - 1 := by ljf_bud_w

example {todo done : List Neg} {X G : Neg} {w : Nat}
    (hbw : 2 * sum3 (X :: todo) + sum3 done + 3 ^ wNeg G + 4 < w) :
    2 * sum3 todo + sum3 (X :: done) + 3 ^ wNeg G + 4 < w - 1 := by ljf_bud_w

/-! #### The processing arms that do not park: drop, `∧`, `↓↑`, `∨` -/

example {todo done : List Neg} {N : Neg} {w : Nat}
    (hbw : 2 * sum3 (Neg.imp .fls N :: todo) + sum3 done + 1 < w) :
    2 * sum3 todo + sum3 done + 1 < w - 1 := by ljf_bud_w

example {todo done : List Neg} {M N : Neg} {w : Nat}
    (hbw : 2 * sum3 (Neg.and M N :: todo) + sum3 done + 1 < w) :
    2 * sum3 (M :: N :: todo) + sum3 done + 1 < w - 1 := by ljf_bud_w

example {todo done : List Neg} {M : Neg} {w : Nat}
    (hbw : 2 * sum3 (Neg.up (.down M) :: todo) + sum3 done + 1 < w) :
    2 * sum3 (M :: todo) + sum3 done + 1 < w - 1 := by ljf_bud_w

example {todo done b : List Neg} {P Q : Pos} {w : Nat}
    (hb : b ∈ invertPos (Pos.or P Q))
    (hbw : 2 * sum3 (Neg.up (.or P Q) :: todo) + sum3 done + 1 < w) :
    2 * sum3 (b ++ todo) + sum3 done + 1 < w - 1 := by ljf_bud_w

/-! #### The two `[]` hand-overs: `eMinQ → TInvQ`, `aMinQ → UEntryQ` -/

example {done : List Neg} {w : Nat}
    (hbw : 2 * sum3 [] + sum3 done + 1 < w) :
    2 * sum3 [] + sum3 done < w - 1 := by ljf_bud_w

example {done : List Neg} {G : Neg} {w : Nat}
    (hbw : 2 * sum3 [] + sum3 done + 3 ^ wNeg G + 4 < w) :
    2 * sum3 [] + sum3 done + 3 ^ wNeg G + 3 < w - 1 := by ljf_bud_w

/-! #### `UEntryQ → UStabQ`: the goal offset drops from `3^wNeg (↑P₀)+3`
to `3^wPos P₀+2` -/

example {done : List Neg} {P₀ : Pos} {w : Nat}
    (hbw : 2 * sum3 [] + sum3 done + 3 ^ wNeg (.up P₀) + 3 < w) :
    2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2 < w - 1 := by ljf_bud_w

/-! #### The phase changes: the station is UNCHANGED and the `sizeOf`
component of the measure pays, so the budget is kept -/

example {done : List Neg} {w : Nat} (hbw : 2 * sum3 [] + sum3 done < w) :
    2 * sum3 [] + sum3 done < w := by ljf_bud_w

example {done : List Neg} {P₀ : Pos} {w : Nat}
    (hbw : 2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2 < w) :
    2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2 < w := by ljf_bud_w

/-! #### The fire into the residual station, `∃p` and `∀p` -/

example {done rest : List Neg} {Q : Pos} {N : Neg} {w : Nat}
    (hXr : (Neg.imp Q N, rest) ∈ splits done)
    (hbw : 2 * sum3 [] + sum3 done < w) :
    2 * sum3 [N] + sum3 rest + 1 < w - 1 := by ljf_bud_w

example {done rest : List Neg} {Q : Pos} {N : Neg} {P₀ : Pos} {w : Nat}
    (hXr : (Neg.imp Q N, rest) ∈ splits done)
    (hbw : 2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2 < w) :
    2 * sum3 [N] + sum3 rest + 3 ^ wNeg (Neg.up P₀) + 4 < w - 1 := by
  ljf_bud_w

/-! #### The box row: the station pays with the slack of `dec_boxF`,
because `boxClean` does not drop the height -/

example {done rest : List Neg} {Q : Pos} {w : Nat}
    (hXr : (Neg.circ Q, rest) ∈ splits done)
    (hbw : 2 * sum3 [] + sum3 done < w) :
    2 * sum3 [Neg.up Q] + sum3 rest + 1 < w - 1 := by ljf_bud_w

example {done rest : List Neg} {Q P₀ : Pos} {w : Nat}
    (hXr : (Neg.circ Q, rest) ∈ splits done)
    (hbw : 2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2 < w) :
    2 * sum3 [Neg.up Q] + sum3 rest + 3 ^ wNeg (Neg.up P₀) + 4 < w - 1 := by
  ljf_bud_w

end LJFO
