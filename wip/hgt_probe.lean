import LJF.OFuelPFamKit

/-! A cheap bench for the height farm of `LJF/OFuelPFamKit.lean`: one
`example` per edge class of the family, stated exactly as the
`decreasing_by` goal presents it after `Prod.Lex.left` (strict) or inside
`lex3_of_le` (non-increasing).  Elaborating this file costs seconds, where
`LJF.OFuelPFam` costs a quarter of an hour. -/

namespace LJFO

variable {p : String}

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

end LJFO
