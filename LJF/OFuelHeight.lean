/-
LJF◯ — height bounds for the derivation transformers (route (B), step 0).

The weight-founded minimality family of `LJF/O.lean` is ordered
lexicographically by (station-and-goal weight, derivation size).  Route
(B)'s retention rows add the edge `E@done → A@done(↑↓◯Q′)`, which raises
the goal weight but drops the derivation; the termination note in
`LJF/OFuelMin.lean` shows that no (station-and-goal weight, derivation
size) order survives that addition, and proposes the opposite founding

    μ := (derivation height, station weight)   lexicographic

with `height` = `szI`/`szS`/`szL`/`szR` of `LJF/OCore.lean`.  For that
order every derivation transformer the family applies before a recursive
call must be height NON-INCREASING.  This module establishes, for each
transformer, whether it is.

Purely additive: nothing in `LJF/OCore.lean`, `LJF/O.lean`,
`LJF/OFuel.lean`, `LJF/OFuelSound.lean` or `LJF/OFuelMin.lean` is touched.
-/
import LJF.O
import Meta.Audit

namespace LJFO

/-! # Part 1: weakening preserves the height exactly

`wk` rebuilds the derivation constructor for constructor, changing only
the membership witnesses, so every height is unchanged. -/

mutual

theorem szS_wk : ∀ {Γ Γ' : List Neg} {j : JD} {P : Pos}
    (H : Sub Γ Γ') (s : Stab Γ j P), szS (Stab.wk H s) = szS s
  | _, _, _, _, H, .rfoc r => by
      simp only [Stab.wk, szS, szR_wk H r]
  | _, _, _, _, H, .lfoc h lf => by
      simp only [Stab.wk, szS, szL_wk H lf]
  | _, _, _, _, H, .laxOf s => by
      simp only [Stab.wk, szS, szS_wk H s]

theorem szR_wk : ∀ {Γ Γ' : List Neg} {j : JD} {P : Pos}
    (H : Sub Γ Γ') (r : RFocus Γ j P), szR (RFocus.wk H r) = szR r
  | _, _, _, _, _, .init _ => by simp only [RFocus.wk, szR]
  | _, _, _, _, H, .or1 r => by simp only [RFocus.wk, szR, szR_wk H r]
  | _, _, _, _, H, .or2 r => by simp only [RFocus.wk, szR, szR_wk H r]
  | _, _, _, _, H, .rel d => by simp only [RFocus.wk, szR, szI_wk H d]

theorem szL_wk : ∀ {Γ Γ' : List Neg} {N : Neg} {j : JD} {P : Pos}
    (H : Sub Γ Γ') (lf : LFoc Γ N j P), szL (LFoc.wk H lf) = szL lf
  | _, _, _, _, _, H, .rel d => by simp only [LFoc.wk, szL, szI_wk H d]
  | _, _, _, _, _, H, .impL s lf => by
      simp only [LFoc.wk, szL, szS_wk H s, szL_wk H lf]
  | _, _, _, _, _, H, .and1 lf => by simp only [LFoc.wk, szL, szL_wk H lf]
  | _, _, _, _, _, H, .and2 lf => by simp only [LFoc.wk, szL, szL_wk H lf]
  | _, _, _, _, _, H, .circL d => by simp only [LFoc.wk, szL, szI_wk H d]

theorem szI_wk : ∀ {Γ Γ' : List Neg} {Ω : List Pos} {j : JD} {N : Neg}
    (H : Sub Γ Γ') (d : Inv Γ Ω j N), szI (Inv.wk H d) = szI d
  | _, _, _, _, _, H, .impR d => by simp only [Inv.wk, szI, szI_wk H d]
  | _, _, _, _, _, H, .andR d e => by
      simp only [Inv.wk, szI, szI_wk H d, szI_wk H e]
  | _, _, _, _, _, H, .circR d => by simp only [Inv.wk, szI, szI_wk H d]
  | _, _, _, _, _, H, .stable s => by simp only [Inv.wk, szI, szS_wk H s]
  | _, _, _, _, _, H, .orL d e => by
      simp only [Inv.wk, szI, szI_wk H d, szI_wk H e]
  | _, _, _, _, _, _, .flsL => by simp only [Inv.wk, szI]
  | _, _, _, _, _, H, .downL d => by
      simp only [Inv.wk, szI, szI_wk (Sub.cons _ H) d]
  | _, _, _, _, _, H, .atomL d => by
      simp only [Inv.wk, szI, szI_wk (Sub.cons _ H) d]

end

/-! # Part 2: the forced-shape extractors

`unStable`, `relOf`, `impROf`, `andROf1/2`, `circROf`, `lfocImp`, `lfocUp`,
`lfocAnd` all project a subderivation, so each strictly drops the height. -/

theorem szS_unStable {Δ : List Neg} {j : JD} {P : Pos} :
    ∀ (d : Inv Δ [] j (.up P)), szS (unStable d) + 1 = szI d
  | .stable _ => rfl

theorem szI_relOf {Δ : List Neg} {j : JD} {M : Neg} :
    ∀ (r : RFocus Δ j (.down M)), szI (relOf r) + 1 = szR r
  | .rel _ => rfl

theorem szI_impROf {Δ : List Neg} {j : JD} {Q : Pos} {N : Neg} :
    ∀ (d : Inv Δ [] j (.imp Q N)), szI (impROf d) + 1 = szI d
  | .impR _ => rfl

theorem szI_andROf1 {Δ : List Neg} {j : JD} {M N : Neg} :
    ∀ (d : Inv Δ [] j (.and M N)), szI (andROf1 d) + 1 ≤ szI d
  | .andR _ _ => by simp only [andROf1, szI]; omega

theorem szI_andROf2 {Δ : List Neg} {j : JD} {M N : Neg} :
    ∀ (d : Inv Δ [] j (.and M N)), szI (andROf2 d) + 1 ≤ szI d
  | .andR _ _ => by simp only [andROf2, szI]; omega

theorem szI_circROf {Δ : List Neg} {j : JD} {P : Pos} :
    ∀ (d : Inv Δ [] j (.circ P)), szI (circROf d) + 1 = szI d
  | .circR _ => rfl

theorem szI_lfocUp {Δ : List Neg} {j : JD} {Q P : Pos} :
    ∀ (lf : LFoc Δ (.up Q) j P), szI (lfocUp lf) + 1 = szL lf
  | .rel _ => rfl

theorem sz_lfocImp {Δ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos} :
    ∀ (lf : LFoc Δ (.imp Q N) j P),
      szS (lfocImp lf).1 + szL (lfocImp lf).2 + 1 = szL lf
  | .impL _ _ => rfl

/-! # Part 3: `extract` and `invBranches`

`extract` replays the derivation along one branch: goal rules commute past
the extraction point and the extraction itself removes a left rule, so the
height never rises.  `invBranches` assembles branch derivations into the
inversion of a positive; it adds one constructor per inversion step, so it
rises by at most the size of that positive. -/

/-- The cast produced by `extract`'s `subst hb` does not change the height. -/
theorem szI_ndrec {Γ : List Neg} {Ω : List Pos} {j : JD} {C : Neg}
    {b b' : List Neg} (d : Inv (b ++ Γ) Ω j C) (h : b = b') :
    szI (@Eq.ndrec (List Neg) b (fun x => Inv (x ++ Γ) Ω j C) d b' h) = szI d := by
  cases h; rfl

/-- **`extract` is height-non-increasing.** -/
theorem szI_extract {Γ : List Neg} (Ω₁ : List Pos) {R : Pos} {Ω₂ : List Pos}
    {C : Neg} {j : JD} (d : Inv Γ (Ω₁ ++ R :: Ω₂) j C)
    (b : List Neg) (hb : b ∈ invertPos R) : szI (extract Ω₁ d b hb) ≤ szI d := by
  fun_induction extract Ω₁ d b hb <;>
    simp_all [szI, szI_wk, szI_ndrec] <;> omega

/-- **`invBranches` rises by at most the size of the positive.** -/
theorem szI_invBranches {j : JD} (n : Nat) (R : Pos) (Γ : List Neg)
    (Ω : List Pos) (N : Neg) (h : ∀ b ∈ invertPos R, Inv (b ++ Γ) Ω j N) :
    (∀ b, ∀ hb : b ∈ invertPos R, szI (h b hb) ≤ n) →
    szI (invBranches R h) ≤ (invertPos R).length * n + sizePos R := by
  fun_induction invBranches R h
  case case1 => intro hn
                simp only [szI, invertPos, sizePos, List.length_cons,
                  List.length_nil, Nat.zero_add, Nat.one_mul]
                exact Nat.add_le_add_right (hn _ _) 1
  case case2 => intro _; simp [szI, invertPos, sizePos]
  case case3 =>
    rename_i P Q h ihP ihQ
    intro hn
    have h1 := ihP (fun b hb => hn b (by
      simp only [invertPos, List.mem_append]; exact .inl hb))
    have h2 := ihQ (fun b hb => hn b (by
      simp only [invertPos, List.mem_append]; exact .inr hb))
    simp only [szI, invertPos, sizePos, List.length_append, Nat.add_mul]
    omega
  case case4 =>
    rename_i M _
    intro hn
    have hM := sizeNeg_pos M
    simp only [szI, invertPos, sizePos, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.one_mul]
    exact Nat.le_trans (Nat.add_le_add_right (hn _ _) 1) (by omega)

/-! # Part 4: the CPS re-targeters

`routeStab`, `routeStabT` and `relStab` walk the spine of a stable proof
unchanged and replace each right-focus leaf by the continuation's value.
Each is height-non-increasing exactly when the continuation spends at most
the constructor it consumes: `szS (k hs r) ≤ szR r + 1` for the two
`route`s, `szS (k hs d) ≤ szI d` for `relStab`.  The bound is tight: the
`orL` clause duplicates the continuation into both branches, so a
continuation with a strictly larger budget multiplies (Part 8). -/

/-- **`routeStab` is height-non-increasing** for a continuation that spends
at most the focus constructor it consumes. -/
theorem sz_routeStab {Δ₀ : List Neg} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg} {j : JD}, Sub Δ₀ Δ' → RFocus Δ' j P → Stab Δ' j P₀)
    (hk : ∀ {Δ' : List Neg} {j : JD} (hs : Sub Δ₀ Δ') (r : RFocus Δ' j P),
      szS (k hs r) ≤ szR r + 1) :
    (∀ (Δ : List Neg) (j : JD) (hs : Sub Δ₀ Δ) (s : Stab Δ j P),
        szS (routeStab k hs s) ≤ szS s)
    ∧ (∀ (Δ : List Neg) (H : Neg) (j : JD) (hs : Sub Δ₀ Δ) (lf : LFoc Δ H j P),
        szL (routeLFoc k hs lf) ≤ szL lf)
    ∧ (∀ (Δ : List Neg) (Ω : List Pos) (j : JD) (hs : Sub Δ₀ Δ)
        (d : Inv Δ Ω j (.up P)), szI (routeInv k hs d) ≤ szI d) := by
  refine routeStab.mutual_induct
    (motive1 := fun Δ j hs s => szS (routeStab k hs s) ≤ szS s)
    (motive2 := fun Δ H j hs lf => szL (routeLFoc k hs lf) ≤ szL lf)
    (motive3 := fun Δ Ω j hs d => szI (routeInv k hs d) ≤ szI d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
    first
      | (rw [routeStab]; exact hk _ _)
      | (rw [routeStab]; simp only [szS]; omega)
      | (rw [routeLFoc]; simp only [szL]; omega)
      | (rw [routeInv]; simp only [szI]; omega)

/-- **`routeStabT` is height-non-increasing** under the same budget. -/
theorem sz_routeStabT {Δ₀ : List Neg} {j₀ : JD} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → RFocus Δ' .tru P → Stab Δ' j₀ P₀)
    (hk : ∀ {Δ' : List Neg} (hs : Sub Δ₀ Δ') (r : RFocus Δ' .tru P),
      szS (k hs r) ≤ szR r + 1) :
    (∀ (Δ : List Neg) (hs : Sub Δ₀ Δ) (s : Stab Δ .tru P),
        szS (routeStabT k hs s) ≤ szS s)
    ∧ (∀ (Δ : List Neg) (H : Neg) (hs : Sub Δ₀ Δ) (lf : LFoc Δ H .tru P),
        szL (routeLFocT k hs lf) ≤ szL lf)
    ∧ (∀ (Δ : List Neg) (Ω : List Pos) (hs : Sub Δ₀ Δ)
        (d : Inv Δ Ω .tru (.up P)), szI (routeInvT k hs d) ≤ szI d) := by
  refine routeStabT.mutual_induct
    (motive1 := fun Δ hs s => szS (routeStabT k hs s) ≤ szS s)
    (motive2 := fun Δ H hs lf => szL (routeLFocT k hs lf) ≤ szL lf)
    (motive3 := fun Δ Ω hs d => szI (routeInvT k hs d) ≤ szI d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
    first
      | (rw [routeStabT]; exact hk _ _)
      | (rw [routeStabT]; simp only [szS]; omega)
      | (rw [routeLFocT]; simp only [szL]; omega)
      | (rw [routeInvT]; simp only [szI]; omega)

/-- **`relStab` is height-non-increasing** for a continuation that spends
at most the released inversion. -/
theorem sz_relStab {Δ₀ : List Neg} {j₀ : JD} {M : Neg} {P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → Inv Δ' [] .tru M → Stab Δ' j₀ P₀)
    (hk : ∀ {Δ' : List Neg} (hs : Sub Δ₀ Δ') (d : Inv Δ' [] .tru M),
      szS (k hs d) ≤ szI d) :
    (∀ (Δ : List Neg) (hs : Sub Δ₀ Δ) (s : Stab Δ .tru (.down M)),
        szS (relStab k hs s) ≤ szS s)
    ∧ (∀ (Δ : List Neg) (H : Neg) (hs : Sub Δ₀ Δ)
        (lf : LFoc Δ H .tru (.down M)), szL (relLF k hs lf) ≤ szL lf)
    ∧ (∀ (Δ : List Neg) (Ω : List Pos) (hs : Sub Δ₀ Δ)
        (d : Inv Δ Ω .tru (.up (.down M))), szI (relInv k hs d) ≤ szI d) := by
  refine relStab.mutual_induct
    (motive1 := fun Δ hs s => szS (relStab k hs s) ≤ szS s)
    (motive2 := fun Δ H hs lf => szL (relLF k hs lf) ≤ szL lf)
    (motive3 := fun Δ Ω hs d => szI (relInv k hs d) ≤ szI d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
    first
      | (rw [relStab]
         refine Nat.le_trans (hk _ _) ?_
         rename_i r
         have := szI_relOf r
         simp only [szS]; omega)
      | (rw [relStab]; simp only [szS]; omega)
      | (rw [relLF]; simp only [szL]; omega)
      | (rw [relInv]; simp only [szI]; omega)


/-! # Part 5: hypothesis simulation

`simInv` and its companions replace every use of one hypothesis `H` by
material the continuation `fl` manufactures.  Two side conditions make the
traversal height-non-increasing, and both are met at every site the
minimality family uses:

* `H` is not an atomic shift — otherwise an `init` use is re-routed through
  `idPos`, which costs the height of the identity expansion;
* `fl` spends at most the focus constructor it consumes,
  `szS (fl hs lf) <= szL lf + 1`.

The right-focus component carries a STRONGER statement — its value is
always a `rfoc`, with a bound on the focus itself — because the `or1`/`or2`
clauses re-route through `stabOr1`/`stabOr2`, which add one constructor per
right-focus LEAF; knowing the value has exactly one leaf is what makes that
addition pay for the `or` constructor it consumes. -/

theorem sz_simInv {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {j : JD} {P : Pos},
      Sub Δ₀ Δ' → LFoc Δ' H j P → Stab Δ' j P)
    (hH : ∀ a : String, Neg.up (.atom a) ≠ H)
    (hfl : ∀ {Δ' : List Neg} {j : JD} {P : Pos} (hs : Sub Δ₀ Δ')
      (lf : LFoc Δ' H j P), szS (fl hs lf) ≤ szL lf + 1) :
    (∀ (Γ Δ : List Neg) (j : JD) (P : Pos)
        (hm : ∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) (hs : Sub Δ₀ Δ) (s : Stab Γ j P),
        szS (simStab fl hm hs s) ≤ szS s)
    ∧ (∀ (Γ Δ : List Neg) (H' : Neg) (j : JD) (P : Pos)
        (hm : ∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) (hs : Sub Δ₀ Δ) (lf : LFoc Γ H' j P),
        szL (simLFoc fl hm hs lf) ≤ szL lf)
    ∧ (∀ (Γ Δ : List Neg) (Ω : List Pos) (j : JD) (C : Neg)
        (hm : ∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) (hs : Sub Δ₀ Δ) (d : Inv Γ Ω j C),
        szI (simInv fl hm hs d) ≤ szI d)
    ∧ (∀ (Γ Δ : List Neg) (j : JD) (P : Pos)
        (hm : ∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) (hs : Sub Δ₀ Δ) (r : RFocus Γ j P),
        ∃ r' : RFocus Δ j P,
          simRFocus fl hm hs r = Stab.rfoc r' ∧ szR r' ≤ szR r) := by
  apply simStab.mutual_induct
    (motive1 := fun Γ Δ j P hm hs s => szS (simStab fl hm hs s) ≤ szS s)
    (motive2 := fun Γ Δ H' j P hm hs lf => szL (simLFoc fl hm hs lf) ≤ szL lf)
    (motive3 := fun Γ Δ Ω j C hm hs d => szI (simInv fl hm hs d) ≤ szI d)
    (motive4 := fun Γ Δ j P hm hs r =>
      ∃ r' : RFocus Δ j P, simRFocus fl hm hs r = Stab.rfoc r' ∧ szR r' ≤ szR r)
  -- simStab
  case case1 => intros; rename_i ih
                obtain ⟨r', he, hle⟩ := ih
                rw [simStab, he]; simp only [szS]; omega
  case case2 => intros; rw [simStab]; simp only [szS]; omega
  case case3 => intros; rename_i hs hm h lf ih
                rw [simStab, dif_pos rfl]
                exact Nat.le_trans (hfl hs _) (by simp only [szS]; omega)
  case case4 => intros; rename_i N hne h hs hm lf ih
                rw [simStab, dif_neg hne]; simp only [szS]; omega
  -- simLFoc
  case case5 => intros; rw [simLFoc]; simp only [szL]; omega
  case case6 => intros; rw [simLFoc]; simp only [szL]; omega
  case case7 => intros; rw [simLFoc]; simp only [szL]; omega
  case case8 => intros; rw [simLFoc]; simp only [szL]; omega
  case case9 => intros; rw [simLFoc]; simp only [szL]; omega
  -- simInv
  case case10 => intros; rw [simInv]; simp only [szI]; omega
  case case11 => intros; rw [simInv]; simp only [szI]; omega
  case case12 => intros; rw [simInv]; simp only [szI]; omega
  case case13 => intros; rw [simInv]; simp only [szI]; omega
  case case14 => intros; rw [simInv]; simp only [szI]; omega
  case case15 => intros; rw [simInv]; simp only [szI]; omega
  case case16 => intros; rw [simInv]; simp only [szI]; omega
  case case17 => intros; rw [simInv]; simp only [szI]; omega
  -- simRFocus
  case case18 => intros; exact absurd (by assumption) (hH _)
  case case19 => intros; rename_i a hne h hs hm
                 refine ⟨.init ((hm _ h).resolve_left hne), ?_, ?_⟩
                 · rw [simRFocus, dif_neg hne]
                 · simp only [szR]; omega
  case case20 => intros; rename_i ih
                 obtain ⟨r', he, hle⟩ := ih
                 exact ⟨.or1 r', by rw [simRFocus, he, stabOr1, routeStab],
                   by simp only [szR]; omega⟩
  case case21 => intros; rename_i ih
                 obtain ⟨r', he, hle⟩ := ih
                 exact ⟨.or2 r', by rw [simRFocus, he, stabOr2, routeStab],
                   by simp only [szR]; omega⟩
  case case22 => intros
                 exact ⟨.rel _, by rw [simRFocus], by simp only [szR]; omega⟩

/-- `simHyp` inherits the bound. -/
theorem szI_simHyp {H : Neg} {Γ Δ₀ : List Neg} {j : JD} {C : Neg}
    (fl : ∀ {Δ' : List Neg} {j' : JD} {P : Pos},
      Sub Δ₀ Δ' → LFoc Δ' H j' P → Stab Δ' j' P)
    (hH : ∀ a : String, Neg.up (.atom a) ≠ H)
    (hfl : ∀ {Δ' : List Neg} {j' : JD} {P : Pos} (hs : Sub Δ₀ Δ')
      (lf : LFoc Δ' H j' P), szS (fl hs lf) ≤ szL lf + 1)
    (hΓ : Sub Γ Δ₀) (d : Inv (H :: Γ) [] j C) :
    szI (simHyp fl hΓ d) ≤ szI d :=
  (sz_simInv fl hH hfl).2.2.1 _ _ _ _ _ _ _ d

end LJFO
