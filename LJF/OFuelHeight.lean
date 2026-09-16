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


/-! # Part 6: the transformers that ARE height-non-increasing

Each is an instance of Part 5 (or of Part 4 through it): the hypothesis
being simulated is never an atomic shift, and each continuation spends at
most the focus constructor it consumes. -/

/-- Uses of `M ∧ N`. -/
theorem szI_invAndHyp {M N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.and M N :: Γ) [] j C) : szI (invAndHyp d) ≤ szI d := by
  rw [invAndHyp]
  refine szI_simHyp _ (fun a => by simp) ?_ _ d
  intro Δ' j' P hs lf
  cases lf with
  | and1 lf' => simp only [lfocAnd, szS, szL]; omega
  | and2 lf' => simp only [lfocAnd, szS, szL]; omega

/-- Uses of `⊥ ⊃ N`. -/
theorem szI_invImpFls {N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp .fls N :: Γ) [] j C) : szI (invImpFls d) ≤ szI d := by
  rw [invImpFls]
  refine szI_simHyp _ (fun a => by simp) ?_ _ d
  intro Δ' j' P hs lf
  have hb := (sz_routeStabT (k := fun {Δ''} (_ : Sub Δ' Δ'')
      (r : RFocus Δ'' .tru .fls) => rfocFls (A := Stab Δ'' j' P) r)
    (fun _ r => nomatch r)).1 Δ' (Sub.refl _) (lfocImp lf).1
  have := sz_lfocImp lf
  omega

theorem szS_unStable_le {Δ : List Neg} {j : JD} {P : Pos}
    (d : Inv Δ [] j (.up P)) : szS (unStable d) ≤ szI d := by
  have := szS_unStable d; omega

/-- Uses of a shifted hypothesis, at a non-atomic positive. -/
theorem szI_invUp {R : Pos} {Γ : List Neg} {j : JD} {C : Neg}
    (hR : ∀ a : String, R ≠ .atom a)
    (d : Inv (.up R :: Γ) [] j C) (b : List Neg) (hb : b ∈ invertPos R) :
    szI (invUp d b hb) ≤ szI d := by
  rw [invUp]
  refine szI_simHyp _ (fun a he => hR a (Neg.up.inj he).symm) ?_ _ d
  intro Δ' j' P hs lf
  refine Nat.le_trans (szS_unStable_le _) ?_
  rw [szI_wk]
  refine Nat.le_trans (szI_extract [] (lfocUp lf) b hb) ?_
  show szI (lfocUp lf) ≤ szL lf + 1
  have := szI_lfocUp lf
  omega

/-- Uses of a fired implication. -/
theorem szI_invFireHyp {a : String} {N : Neg} {done rest Δext : List Neg}
    {j : JD} {C : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done)
    (d : Inv (done ++ Δext) [] j C) : szI (invFireHyp h d) ≤ szI d := by
  rw [invFireHyp]
  refine (sz_simInv _ (fun c => by simp) ?_).2.2.1 _ _ _ _ _ _ _ d
  intro Δ' j' P hs lf
  have := sz_lfocImp lf
  simp only [szS]; omega

/-- Fired-context cleanup. -/
theorem szI_fireClean {Q₀ : Pos} {N : Neg} {Γ' rest K : List Neg} {j : JD}
    {C : Neg} (hsplit : ∀ Z ∈ Γ', Z = Neg.imp Q₀ N ∨ Z ∈ rest ∨ Z ∈ K)
    (d : Inv (N :: Γ') [] j C) : szI (fireClean hsplit d) ≤ szI d := by
  rw [fireClean]
  refine (sz_simInv _ (fun c => by simp) ?_).2.2.1 _ _ _ _ _ _ _ d
  intro Δ' j' P hs lf
  have := sz_lfocImp lf
  simp only [szS]; omega

/-- Opened-box cleanup. -/
theorem szI_boxClean {Q : Pos} {Γ' rest K : List Neg} {j : JD} {C : Neg}
    (hsplit : ∀ Z ∈ Γ', Z = Neg.circ Q ∨ Z ∈ rest ∨ Z ∈ K)
    (d : Inv (Neg.up Q :: Γ') [] j C) : szI (boxClean hsplit d) ≤ szI d := by
  rw [boxClean]
  refine (sz_simInv _ (fun c => by simp) ?_).2.2.1 _ _ _ _ _ _ _ d
  intro Δ' j' P hs lf
  cases lf with
  | circL dQ => simp only [szS, szL]; omega

/-- **`negOfDownStab` at a shifted body** rises by at most one. -/
theorem szI_negOfDownStab_up {P : Pos} {Δ : List Neg}
    (s : Stab Δ .tru (.down (.up P))) :
    szI (negOfDownStab (.up P) s) ≤ szS s + 1 := by
  rw [negOfDownStab]
  have := (sz_relStab (k := fun {Δ'} (_ : Sub Δ Δ') (d : Inv Δ' [] .tru (.up P)) =>
      unStable d) (fun _ d => by have := szS_unStable d; omega)).1 Δ (Sub.refl _) s
  simp only [szI]; omega

/-- **`negOfDownStab` at a boxed body** rises by at most two. -/
theorem szI_negOfDownStab_circ {P : Pos} {Δ : List Neg}
    (s : Stab Δ .tru (.down (.circ P))) :
    szI (negOfDownStab (.circ P) s) ≤ szS s + 2 := by
  rw [negOfDownStab]
  have := (sz_relStab (k := fun {Δ'} (_ : Sub Δ Δ')
      (d : Inv Δ' [] .tru (.circ P)) => unStable (circROf d))
    (fun _ d => by
      have h1 := szS_unStable (circROf d)
      have h2 := szI_circROf d
      omega)).1 Δ (Sub.refl _) s
  simp only [szI]; omega

/-! # Part 7: the transformers that are NOT

Three processing clauses and one dispatch clause fail, and they fail for
one structural reason: their continuation carries the CONTINUATION OF THE
USE (`lf₂`, the left focus below the fired implication) into every
right-focus leaf of the antecedent's proof.  An antecedent proof that
branches — an `orL` under the inversion of a pending positive — therefore
receives one copy of `lf₂` per branch, and the height, which sums over
`orL`, grows.  Part 4's budget `szS (k hs r) ≤ szR r + 1` is exactly what
excludes this, and Part 7.1 shows the budget cannot be relaxed even to
`+ 2`. -/

/-! ## 7.1 The Part 4 budget is tight

`stabOr1 = routeStab (fun _ r => .rfoc (.or1 r))` has continuation budget
`szR r + 2`, one more than Part 4 allows, and it raises the height by the
NUMBER OF RIGHT-FOCUS LEAVES of its argument.  Two leaves, two units. -/

/-- A two-leaf stable proof: the disjunction `u ∨ u` is inverted, and each
branch focuses on the hypothesis `↑a`. -/
def ceU : Pos := .or (.atom "u") (.atom "u")

def ceΔ : List Neg := [Neg.up ceU, Neg.up (Pos.atom "a")]

def ceS : Stab ceΔ .tru (.atom "a") :=
  .lfoc (List.mem_cons_self ..)
    (.rel (.orL (.atomL (.stable (.rfoc (.init (by simp [ceΔ])))))
                (.atomL (.stable (.rfoc (.init (by simp [ceΔ])))))))

/-- Before. -/
theorem szS_ceS : szS ceS = 11 := rfl

/-- After: `stabOr1` has raised the height by two — one per leaf.  So no
bound `szS (routeStab k hs s) ≤ szS s` survives a continuation budget of
`szR r + 2`, and Part 4's hypothesis cannot be weakened. -/
theorem szS_stabOr1_ceS : szS (stabOr1 (B := Pos.atom "b") ceS) = 13 := by
  simp [ceS, stabOr1, routeStab.eq_def, routeLFocT.eq_def, routeLFoc.eq_def,
    routeInv.eq_def, szS, szR, szL, szI]

/-! ## 7.2 `invImpOr`, `invStrip`, `invCurry` raise the height

One cell each, of the same shape: the hypothesis is used ONCE, its
antecedent is proved by a two-branch case analysis on `u ∨ u`, and the
continuation of the use is a left focus of height 5.  The input height is
kernel-checked (`rfl`); the transformed height is the repository
evaluator's, since `simInv` is a well-founded recursion and does not
reduce in the kernel.  `#guard` makes each measurement a build check.

    transformer   szI d   szI (transformer d)
    invImpOr       21          26   (+5)
    invStrip       25          26   (+1)
    invCurry       29          40   (+11)
-/

section Counterexamples

/-- `(q ∨ q) ⊃ ↑z`, used once, antecedent proved by a case split. -/
def ceOrH : Neg := .imp (.or (.atom "q") (.atom "q")) (Neg.up (Pos.atom "z"))
def ceOrΔ : List Neg :=
  [Neg.up ceU, Neg.up (Pos.atom "q"), Neg.up (Pos.atom "z")]
def ceOrΓ : List Neg := ceOrH :: ceOrΔ

def ceOrS1 : Stab ceOrΓ .tru (.or (.atom "q") (.atom "q")) :=
  Stab.lfoc (N := Neg.up ceU) (by simp [ceOrΓ, ceOrΔ, ceU])
    (.rel (.orL
      (.atomL (.stable (.rfoc (.or1 (.init (by simp [ceOrΓ, ceOrΔ]))))))
      (.atomL (.stable (.rfoc (.or1 (.init (by simp [ceOrΓ, ceOrΔ]))))))))

def ceOrLf2 : LFoc ceOrΓ (Neg.up (Pos.atom "z")) .tru (.atom "z") :=
  .rel (.atomL (.stable (.rfoc (.init (by simp [ceOrΓ, ceOrΔ])))))

def ceOrD : Inv ceOrΓ [] .tru (.up (Pos.atom "z")) :=
  .stable (.lfoc (List.mem_cons_self ..) (.impL ceOrS1 ceOrLf2))

theorem szI_ceOrD : szI ceOrD = 21 := rfl

#guard szI (invImpOr (Q₁ := .atom "q") (Q₂ := .atom "q")
  (N := Neg.up (Pos.atom "z")) ceOrD) == 26

/-- `↓↑q ⊃ ↑z`, same shape. -/
def ceStH : Neg := .imp (.down (.up (.atom "q"))) (Neg.up (Pos.atom "z"))
def ceStΔ : List Neg :=
  [Neg.up ceU, Neg.up (Pos.atom "q"), Neg.up (Pos.atom "z")]
def ceStΓ : List Neg := ceStH :: ceStΔ

def ceStS1 : Stab ceStΓ .tru (.down (.up (.atom "q"))) :=
  Stab.lfoc (N := Neg.up ceU) (by simp [ceStΓ, ceStΔ, ceU])
    (.rel (.orL
      (.atomL (.stable (.rfoc (.rel (.stable (.rfoc
        (.init (by simp [ceStΓ, ceStΔ]))))))))
      (.atomL (.stable (.rfoc (.rel (.stable (.rfoc
        (.init (by simp [ceStΓ, ceStΔ]))))))))))

def ceStLf2 : LFoc ceStΓ (Neg.up (Pos.atom "z")) .tru (.atom "z") :=
  .rel (.atomL (.stable (.rfoc (.init (by simp [ceStΓ, ceStΔ])))))

def ceStD : Inv ceStΓ [] .tru (.up (Pos.atom "z")) :=
  .stable (.lfoc (List.mem_cons_self ..) (.impL ceStS1 ceStLf2))

theorem szI_ceStD : szI ceStD = 25 := rfl

#guard szI (invStrip (P' := .atom "q") (N := Neg.up (Pos.atom "z")) ceStD) == 26

/-- `↓(⊤ ∧ ⊤) ⊃ ↑z`, same shape.  Currying splits one implication
elimination into two, which is why this is the worst of the three. -/
def ceCyH : Neg := .imp (.down (.and nTop nTop)) (Neg.up (Pos.atom "z"))
def ceCyΔ : List Neg := [Neg.up ceU, Neg.up (Pos.atom "z")]
def ceCyΓ : List Neg := ceCyH :: ceCyΔ

def ceCyS1 : Stab ceCyΓ .tru (.down (.and nTop nTop)) :=
  Stab.lfoc (N := Neg.up ceU) (by simp [ceCyΓ, ceCyΔ, ceU])
    (.rel (.orL
      (.atomL (.stable (.rfoc (.rel (.andR nTopIntro nTopIntro)))))
      (.atomL (.stable (.rfoc (.rel (.andR nTopIntro nTopIntro)))))))

def ceCyLf2 : LFoc ceCyΓ (Neg.up (Pos.atom "z")) .tru (.atom "z") :=
  .rel (.atomL (.stable (.rfoc (.init (by simp [ceCyΓ, ceCyΔ])))))

def ceCyD : Inv ceCyΓ [] .tru (.up (Pos.atom "z")) :=
  .stable (.lfoc (List.mem_cons_self ..) (.impL ceCyS1 ceCyLf2))

theorem szI_ceCyD : szI ceCyD = 29 := rfl

#guard szI (invCurry (M₁ := nTop) (M₂ := nTop)
  (N := Neg.up (Pos.atom "z")) ceCyD) == 40

end Counterexamples

/-! ## 7.3 `negOfDownStab` at a conjunction, and `dykCommute`

The `and` clause applies the recursion TWICE to the same stable proof and
joins with `andR`, whose height is the SUM.  So the spine of the argument
is duplicated, and no bound `szI (negOfDownStab M s) ≤ szS s + c` with `c`
independent of `M` and `s` can hold.  The equation is the mechanism; the
family below is the measurement. -/

/-- **The duplication, as an equation**: the `and` clause runs the recursion
twice on the same `s`, and `szI` of `andR` is the sum. -/
theorem szI_negOfDownStab_and {M₁ M₂ : Neg} {Δ : List Neg}
    (s : Stab Δ .tru (.down (.and M₁ M₂))) :
    szI (negOfDownStab (.and M₁ M₂) s)
      = szI (negOfDownStab M₁ (relStab
          (fun _ d => .rfoc (.rel (andROf1 d))) (Sub.refl _) s))
      + szI (negOfDownStab M₂ (relStab
          (fun _ d => .rfoc (.rel (andROf2 d))) (Sub.refl _) s))
      + 1 := by
  rw [negOfDownStab]; simp only [szI]

/-- A family whose stable proof has a spine of `n` implication
eliminations with trivial antecedents. -/
def topArrow : Nat → Neg → Neg
  | 0, N => N
  | k+1, N => .imp (.down nTop) (topArrow k N)

def ceMand : Neg := .and (Neg.up (Pos.atom "z")) (Neg.up (Pos.atom "z"))

def ceXn (n : Nat) : Neg := topArrow n (Neg.up (.down ceMand))

def ceΔn (n : Nat) : List Neg := [ceXn n]

def ceChain (Γ : List Neg) :
    ∀ k, LFoc Γ (topArrow k (Neg.up (.down ceMand))) .tru (.down ceMand)
  | 0 => .rel (idPos (.down ceMand) Γ .tru)
  | k+1 => .impL (.rfoc (.rel nTopIntro)) (ceChain Γ k)

def ceSn (n : Nat) : Stab (ceΔn n) .tru (.down ceMand) :=
  Stab.lfoc (N := ceXn n) (List.mem_cons_self ..) (ceChain (ceΔn n) n)

/-! The measurement: `szS (ceSn n) = 5n + 23` while
`szI (negOfDownStab ceMand (ceSn n)) = 10n + 25`.  The difference is
`5n + 2`, unbounded, so no additive constant bounds `negOfDownStab` at a
conjunction — and none bounds `dykCommute` either, since `dykCommute`
calls `negOfDownStab N′` at the Dyckhoff hypothesis's consequent `N′`,
which is an arbitrary negative. -/
#guard ((List.range 6).map
  (fun n => (szS (ceSn n), szI (negOfDownStab ceMand (ceSn n)))))
  == [(23, 25), (28, 35), (33, 45), (38, 55), (43, 65), (48, 75)]

/-! ## 7.4 The max-based height fails too

The natural repair for 7.1-7.2 is a MAX-based height — `impL`, `andR` and
`orL` taking the maximum of their premises instead of the sum — under
which a continuation copied into two branches costs nothing extra.  It is
not enough.  The continuation of a use is re-inserted at the DEPTH of the
antecedent proof's right-focus leaves, so the value's height is
`depth(s₁) + height(lf₂)` where the argument's was
`max (height s₁) (height lf₂) + 1`; a tall continuation under a deep
antecedent still rises.  `htI` below is that measure, and the same three
clauses rise on the cells of 7.2 (`invStrip` only once the continuation is
made tall, cell `dp*`):

    cell                    szI before/after    htI before/after
    invImpOr  (ceOrD)          21 → 26            11 → 13
    invStrip  (ceStD)          25 → 26            13 → 13
    invCurry  (ceCyD)          29 → 40            13 → 14
    invStrip  (dpD, tall)      50 → 76            13 → 18
-/

mutual
/-- Max-based height of a stable derivation. -/
def htS : ∀ {Γ : List Neg} {j : JD} {P : Pos}, Stab Γ j P → Nat
  | _, _, _, .rfoc r => htR r + 1
  | _, _, _, .lfoc _ lf => htL lf + 1
  | _, _, _, .laxOf s => htS s + 1
/-- Max-based height of a right focus. -/
def htR : ∀ {Γ : List Neg} {j : JD} {P : Pos}, RFocus Γ j P → Nat
  | _, _, _, .init _ => 1
  | _, _, _, .or1 r => htR r + 1
  | _, _, _, .or2 r => htR r + 1
  | _, _, _, .rel d => htI d + 1
/-- Max-based height of a left focus. -/
def htL : ∀ {Γ : List Neg} {N : Neg} {j : JD} {P : Pos}, LFoc Γ N j P → Nat
  | _, _, _, _, .rel d => htI d + 1
  | _, _, _, _, .impL s lf => max (htS s) (htL lf) + 1
  | _, _, _, _, .and1 lf => htL lf + 1
  | _, _, _, _, .and2 lf => htL lf + 1
  | _, _, _, _, .circL d => htI d + 1
/-- Max-based height of an inversion. -/
def htI : ∀ {Γ : List Neg} {Ω : List Pos} {j : JD} {N : Neg}, Inv Γ Ω j N → Nat
  | _, _, _, _, .impR d => htI d + 1
  | _, _, _, _, .andR d e => max (htI d) (htI e) + 1
  | _, _, _, _, .circR d => htI d + 1
  | _, _, _, _, .stable s => htS s + 1
  | _, _, _, _, .orL d e => max (htI d) (htI e) + 1
  | _, _, _, _, .flsL => 1
  | _, _, _, _, .downL d => htI d + 1
  | _, _, _, _, .atomL d => htI d + 1
end

#guard htI ceOrD == 11
#guard htI (invImpOr (Q₁ := .atom "q") (Q₂ := .atom "q")
  (N := Neg.up (Pos.atom "z")) ceOrD) == 13
#guard htI ceCyD == 13
#guard htI (invCurry (M₁ := nTop) (M₂ := nTop)
  (N := Neg.up (Pos.atom "z")) ceCyD) == 14

/-- The tall-continuation cell: the consequent of the stripped hypothesis
is a five-fold implication with trivial antecedents, so the continuation
of the use is as tall as the antecedent's proof. -/
def dpN : Neg :=
  .imp (.down nTop) (.imp (.down nTop) (.imp (.down nTop)
    (.imp (.down nTop) (.imp (.down nTop) (Neg.up (Pos.atom "z"))))))

def dpH : Neg := .imp (.down (.up (.atom "q"))) dpN
def dpΔ : List Neg :=
  [Neg.up ceU, Neg.up (Pos.atom "q"), Neg.up (Pos.atom "z")]
def dpΓ : List Neg := dpH :: dpΔ

def dpS1 : Stab dpΓ .tru (.down (.up (.atom "q"))) :=
  Stab.lfoc (N := Neg.up ceU) (by simp [dpΓ, dpΔ, ceU])
    (.rel (.orL
      (.atomL (.stable (.rfoc (.rel (.stable (.rfoc
        (.init (by simp [dpΓ, dpΔ]))))))))
      (.atomL (.stable (.rfoc (.rel (.stable (.rfoc
        (.init (by simp [dpΓ, dpΔ]))))))))))

def dpT : Stab dpΓ .tru (.down nTop) := .rfoc (.rel nTopIntro)

def dpLf2 : LFoc dpΓ dpN .tru (.atom "z") :=
  .impL dpT (.impL dpT (.impL dpT (.impL dpT (.impL dpT
    (.rel (.atomL (.stable (.rfoc (.init (by simp [dpΓ, dpΔ]))))))))))

def dpD : Inv dpΓ [] .tru (.up (Pos.atom "z")) :=
  .stable (.lfoc (List.mem_cons_self ..) (.impL dpS1 dpLf2))

theorem szI_dpD : szI dpD = 50 := rfl
theorem htI_dpD : htI dpD = 13 := rfl

#guard szI (invStrip (P' := .atom "q") (N := dpN) dpD) == 76
#guard htI (invStrip (P' := .atom "q") (N := dpN) dpD) == 18

/-! # Part 8: the verdict for `μ = (derivation height, station weight)`

Collecting Parts 1-7 as the Step-0 table:

    transformer                     height bound
    `wk`                            EQUAL                      (Part 1)
    forced-shape extractors         strictly smaller           (Part 2)
    `extract`                       ≤                          (Part 3)
    `invBranches`                   ≤ max + `sizePos R`        (Part 3)
    `routeStab`,`routeStabT`        ≤, budget `szR r + 1`      (Part 4)
    `relStab`                       ≤, budget `szI d`          (Part 4)
    `simStab`/`simLFoc`/`simInv`    ≤, side conditions         (Part 5)
    `simRFocus`                     ≤, and `rfoc`-headed       (Part 5)
    `simHyp`                        ≤                          (Part 6)
    `invAndHyp`                     ≤                          (Part 6)
    `invImpFls`                     ≤                          (Part 6)
    `invUp` (non-atomic positive)   ≤                          (Part 6)
    `invFireHyp`                    ≤                          (Part 6)
    `fireClean`, `boxClean`         ≤                          (Part 6)
    `negOfDownStab` at `↑P`         ≤ `szS s + 1`              (Part 6)
    `negOfDownStab` at `◯P`         ≤ `szS s + 2`              (Part 6)
    `stabOr1`/`stabOr2`             RISES (per right-focus leaf)  (7.1)
    `invImpOr`                      RISES (21 → 26)               (7.2)
    `invStrip`                      RISES (25 → 26)               (7.2)
    `invCurry`                      RISES (29 → 40)               (7.2)
    `negOfDownStab` at `M₁ ∧ M₂`    RISES, unboundedly            (7.3)
    `dykCommute`                    RISES, unboundedly            (7.3)
    (and all four rise under a max-based height too              (7.4))

The consequence for route (B).  The height-first order needs every
transformer applied before a recursive call to be height-non-increasing,
because the station weight is the SECOND component and processing edges
drop it — a height rise there is fatal.  `invImpOr`, `invStrip` and
`invCurry` are the interpolant's own PROCESSING clauses for the todo-heads
`(Q₁ ∨ Q₂) ⊃ N`, `↓↑P′ ⊃ N` and `↓(M₁ ∧ M₂) ⊃ N`, reached from any station
whose parked bodies have those shapes; all three rise.  So

    μ = (derivation height, station weight)  does NOT found the family,

and the obstruction is NOT confined to the Dyckhoff dispatch: it is in the
processing phase, which the `interpR` fallback of the brief (Dyckhoff rows
guarded at the full station) does not touch.  The one thing the fallback
would buy — removing `dykCommute` and `negOfDownStab` at a conjunction —
is necessary but not sufficient.

The max-based repair does not rescue it either (7.4): it removes the
multiplicative cost of branch duplication but not the cost of INSERTION
DEPTH — the continuation of a use is rebuilt at the depth of the
antecedent proof's right-focus leaves — and the same three clauses rise
under it, `invStrip` as soon as the continuation is as tall as the
antecedent's proof.

So the Step-0 answer is negative on both prescribed branches:

* `interpF` unchanged, height-first: refuted (7.2);
* `interpR` (Dyckhoff rows guarded at the full station), height-first:
  refuted by the SAME cells, since 7.2 lies in the processing phase, which
  the fallback does not touch.

What the two measures have in common is that they are monotone under
adding a constructor along a path, and every residual-firing clause of the
interpolant rebuilds one use as a nest of constructors at the depth of
another derivation.  A founding for route (B) therefore has to come from
somewhere other than the derivation alone — the weight-founded order of
`LJF/O.lean` remains the only one that runs the processing phase, and the
termination note in `LJF/OFuelMin.lean` remains the reason it cannot take
the retention discharge natively.  The obstruction is now exact on both
sides. -/


/-! # Part 9: what the table says the design must be

Two of the four failing transformers leave the family outright, and this
part proves it.

`negOfDownStab` and `dykCommute` are used at exactly three sites: the two
`↓↑P′` / `↓◯P′` release clauses of `UStab` (`LJF/O.lean:1543,1547`) and the
Dyckhoff antecedent dispatch `dykAntC`.  The releases do not need it: the
`laxOf` the goal is about to acquire can be spent INSIDE the release
continuation, and then the height does not rise at all.  The two
replacements below land on the SAME `∀p` row as the originals, because
`jGoal .lax (↑P′) = ◯P′ = jGoal .tru (◯P′)`.  The Dyckhoff dispatch is what
the brief's `interpR` fallback removes.

So a height-first founding is blocked by exactly one thing: the three
PROCESSING clauses of 7.2, which RESHAPE a parked implication's antecedent
(`(Q₁∨Q₂) ⊃ N`, `↓↑P′ ⊃ N`, `↓(M₁∧M₂) ⊃ N`) and simulate its uses.  Every
other processing clause either parks (weakening only, height EXACT by Part
1) or is one of the six Part 6 transformers.  The design that would make
the whole family height-founded therefore has to PARK those three shapes
too — extending `ParkedN` and giving each an aggregate row — rather than
reshape them.  That is a change to `interpF` well beyond the `interpR`
fallback, and it is the finding this module was built to produce. -/

/-- Release a `↓↑P′` proof into the LAX inversion of `↑P′` without raising
the height: the `laxOf` goes INSIDE the release continuation, where it pays
for the `rfoc`/`rel` pair the release consumes. -/
def laxReleaseUp {Δ : List Neg} {P' : Pos} (s : Stab Δ .tru (.down (.up P'))) :
    Inv Δ [] .lax (.up P') :=
  .stable (relStab (j := .lax) (fun _ d => .laxOf (unStable d)) (Sub.refl _) s)

theorem szI_laxReleaseUp {Δ : List Neg} {P' : Pos}
    (s : Stab Δ .tru (.down (.up P'))) :
    szI (laxReleaseUp s) ≤ szS (Stab.laxOf s) := by
  have := (sz_relStab (k := fun {Δ'} (_ : Sub Δ Δ')
      (d : Inv Δ' [] .tru (.up P')) => Stab.laxOf (unStable d))
    (fun _ d => by have := szS_unStable d; simp only [szS]; omega)).1
    Δ (Sub.refl _) s
  simp only [laxReleaseUp, szI, szS]; omega

/-- Likewise for a boxed body: the `circR` the goal would need is consumed
by the `circROf` in the continuation. -/
def laxReleaseCirc {Δ : List Neg} {P' : Pos}
    (s : Stab Δ .tru (.down (.circ P'))) : Inv Δ [] .lax (.up P') :=
  .stable (relStab (j := .lax) (fun _ d => unStable (circROf d)) (Sub.refl _) s)

theorem szI_laxReleaseCirc {Δ : List Neg} {P' : Pos}
    (s : Stab Δ .tru (.down (.circ P'))) :
    szI (laxReleaseCirc s) ≤ szS (Stab.laxOf s) := by
  have := (sz_relStab (k := fun {Δ'} (_ : Sub Δ Δ')
      (d : Inv Δ' [] .tru (.circ P')) => unStable (circROf d))
    (fun _ d => by
      have h1 := szS_unStable (circROf d)
      have h2 := szI_circROf d
      omega)).1 Δ (Sub.refl _) s
  simp only [laxReleaseCirc, szI, szS]; omega

/-- The two replacements land on the SAME `∀p` row as the originals:
`jGoal .lax (.up P′) = .circ P′ = jGoal .tru (.circ P′)`. -/
example (P' : Pos) : jGoal .lax (Neg.up P') = jGoal .tru (Neg.circ P') := rfl


/-! # Part 10: the NORMALISED height, and the edge table of the parking
family (route (B), node N0e)

Parts 1-9 measure each judgment with its own height (`szI`, `szS`, `szL`,
`szR`).  The family of `LJF/O.lean` traverses all four, so ordering it by
"the derivation height" needs ONE number, comparable across a phase
change.  The normalised height is that number: the height of the `Inv`
one gets by re-wrapping the object with the phase constructors,

    hgtI d  = szI d,        hgtS s  = szS s + 1 = szI (.stable s),
    hgtL lf = szL lf + 2,   hgtR r  = szR r + 2.

Under it the phase constructors are height-NEUTRAL (`hgt_stable`,
`hgt_lfoc`, `hgt_rfoc`), which is what makes the FIRST component of

    μ := (normalised height, station weight with the `LJF/O.lean`
          offsets, derivation size)          lexicographic

behave: a phase change keeps the height and the station and is paid for
by the third component, exactly as `sizeOf` pays for it in the
weight-founded family, while a station change is paid for by the second
component as it already is there.

This part collects, as lemmas, the height side of every edge class the
`interpP` family (`LJF/OFuelP.lean`) contains.  The three PROCESSING
edges that refuted the height order for `interpF` (§7.2) are absent —
`interpP` parks those shapes — and the two release sites use Part 9. -/

/-- Normalised height of an inversion. -/
def hgtI {Γ : List Neg} {Ω : List Pos} {j : JD} {N : Neg}
    (d : Inv Γ Ω j N) : Nat := szI d

/-- Normalised height of a stable derivation. -/
def hgtS {Γ : List Neg} {j : JD} {P : Pos} (s : Stab Γ j P) : Nat := szS s + 1

/-- Normalised height of a left focus. -/
def hgtL {Γ : List Neg} {N : Neg} {j : JD} {P : Pos}
    (lf : LFoc Γ N j P) : Nat := szL lf + 2

/-- Normalised height of a right focus. -/
def hgtR {Γ : List Neg} {j : JD} {P : Pos} (r : RFocus Γ j P) : Nat :=
  szR r + 2

/-! ## 10.1 The phase constructors are height-neutral -/

theorem hgt_stable {Γ : List Neg} {j : JD} {P : Pos} (s : Stab Γ j P) :
    hgtI (Inv.stable s) = hgtS s := rfl

theorem hgt_lfoc {Γ : List Neg} {N : Neg} {j : JD} {P : Pos}
    (h : N ∈ Γ) (lf : LFoc Γ N j P) : hgtS (Stab.lfoc h lf) = hgtL lf := rfl

theorem hgt_rfoc {Γ : List Neg} {j : JD} {P : Pos} (r : RFocus Γ j P) :
    hgtS (Stab.rfoc r) = hgtR r := rfl

/-- Weakening is height-EXACT, in normalised form (Part 1). -/
theorem hgt_wk {Γ Γ' : List Neg} {Ω : List Pos} {j : JD} {N : Neg}
    (H : Sub Γ Γ') (d : Inv Γ Ω j N) : hgtI (Inv.wk H d) = hgtI d :=
  szI_wk H d

/-! ## 10.2 Positivity -/

theorem szR_pos {Γ : List Neg} {j : JD} {P : Pos} :
    ∀ (r : RFocus Γ j P), 1 ≤ szR r
  | .init _ | .or1 _ | .or2 _ | .rel _ => by simp only [szR]; omega

theorem szI_pos {Γ : List Neg} {Ω : List Pos} {j : JD} {N : Neg} :
    ∀ (d : Inv Γ Ω j N), 1 ≤ szI d
  | .impR _ | .andR _ _ | .circR _ | .stable _ | .orL _ _ | .flsL
  | .downL _ | .atomL _ => by simp only [szI]; omega

theorem szL_pos {Γ : List Neg} {N : Neg} {j : JD} {P : Pos} :
    ∀ (lf : LFoc Γ N j P), 1 ≤ szL lf
  | .rel _ | .impL _ _ | .and1 _ | .and2 _ | .circL _ => by
      simp only [szL]; omega

theorem szS_pos {Γ : List Neg} {j : JD} {P : Pos} :
    ∀ (s : Stab Γ j P), 1 ≤ szS s
  | .rfoc _ | .lfoc _ _ | .laxOf _ => by simp only [szS]; omega

/-! ## 10.3 The structural edges

Every edge of the family that descends into a premise, in normalised
form.  Each is strict except the three phase changes of 10.1, which are
equalities and are paid for by the third component of `μ`. -/

theorem hgt_impR {Γ : List Neg} {Ω : List Pos} {Q : Pos} {N : Neg}
    (d : Inv Γ (Q :: Ω) .tru N) : hgtI d < hgtI (Inv.impR d) := by
  simp only [hgtI, szI]; omega

theorem hgt_andR1 {Γ : List Neg} {Ω : List Pos} {M N : Neg}
    (d : Inv Γ Ω .tru M) (e : Inv Γ Ω .tru N) :
    hgtI d < hgtI (Inv.andR d e) := by
  have := szI_pos e; simp only [hgtI, szI]; omega

theorem hgt_andR2 {Γ : List Neg} {Ω : List Pos} {M N : Neg}
    (d : Inv Γ Ω .tru M) (e : Inv Γ Ω .tru N) :
    hgtI e < hgtI (Inv.andR d e) := by
  have := szI_pos d; simp only [hgtI, szI]; omega

theorem hgt_circR {Γ : List Neg} {Ω : List Pos} {j : JD} {P : Pos}
    (d : Inv Γ Ω .lax (.up P)) : hgtI d < hgtI (Inv.circR (j := j) d) := by
  simp only [hgtI, szI]; omega

theorem hgt_laxOf {Γ : List Neg} {P : Pos} (s : Stab Γ .tru P) :
    hgtS s < hgtS (Stab.laxOf s) := by simp only [hgtS, szS]; omega

theorem hgt_lfImpL_ant {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos}
    (s : Stab Γ .tru Q) (lf : LFoc Γ N j P) :
    hgtS s < hgtL (LFoc.impL s lf) := by
  have := szL_pos lf; simp only [hgtS, hgtL, szL]; omega

theorem hgt_lfImpL_cont {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos}
    (s : Stab Γ .tru Q) (lf : LFoc Γ N j P) :
    hgtL lf < hgtL (LFoc.impL s lf) := by
  have := szS_pos s; simp only [hgtL, szL]; omega

theorem hgt_lfAnd1 {Γ : List Neg} {j : JD} {M N : Neg} {P : Pos}
    (lf : LFoc Γ M j P) : hgtL lf < hgtL (LFoc.and1 (N := N) lf) := by
  simp only [hgtL, szL]; omega

theorem hgt_lfAnd2 {Γ : List Neg} {j : JD} {M N : Neg} {P : Pos}
    (lf : LFoc Γ N j P) : hgtL lf < hgtL (LFoc.and2 (M := M) lf) := by
  simp only [hgtL, szL]; omega

theorem hgt_lfRel {Γ : List Neg} {j : JD} {Q P : Pos}
    (d : Inv Γ [Q] j (.up P)) : hgtI d < hgtL (LFoc.rel d) := by
  simp only [hgtI, hgtL, szL]; omega

theorem hgt_lfCircL {Γ : List Neg} {Q P : Pos}
    (d : Inv Γ [Q] .lax (.up P)) : hgtI d < hgtL (LFoc.circL d) := by
  simp only [hgtI, hgtL, szL]; omega

theorem hgt_rfRel {Γ : List Neg} {j : JD} {N : Neg} (d : Inv Γ [] j N) :
    hgtI d < hgtR (RFocus.rel d) := by simp only [hgtI, hgtR, szR]; omega

theorem hgt_rfOr1 {Γ : List Neg} {j : JD} {P Q : Pos} (r : RFocus Γ j P) :
    hgtR r < hgtR (RFocus.or1 (Q := Q) r) := by simp only [hgtR, szR]; omega

theorem hgt_rfOr2 {Γ : List Neg} {j : JD} {P Q : Pos} (r : RFocus Γ j Q) :
    hgtR r < hgtR (RFocus.or2 (P := P) r) := by simp only [hgtR, szR]; omega

/-! ## 10.4 The antecedent dispatch — the edge the parking design exists for

At a saturated station the family meets a focus on a parked implication,
`Stab.lfoc h (.impL s_d lf′)`, and `interpP` asks for the `∀p` of the
ANTECEDENT at the FULL station: one native call of the `∀p` entry on
`Inv.stable s_d`, weakened.  The statement is generic in the antecedent
positive `Q`, so it covers the ◯-implication and the Dyckhoff row of
`interpF` and the three shapes `interpP` newly parks.  The edge drops the
normalised height STRICTLY, so the station may stay put — which is
exactly what a station-first order could not allow (the cycle of
`docs/ui-ljfo-clause-table.md` §4.11). -/

theorem hgt_antDispatch {Γ Γ₂ : List Neg} {j : JD} {Q : Pos} {N : Neg}
    {P : Pos} (H : Sub Γ Γ₂) (h : Neg.imp Q N ∈ Γ)
    (s_d : Stab Γ .tru Q) (lf' : LFoc Γ N j P) :
    hgtI ((Inv.stable s_d).wk H) < hgtS (Stab.lfoc h (.impL s_d lf')) := by
  have hp := szL_pos lf'
  have hw := szI_wk H (Inv.stable s_d)
  simp only [hgtI, hgtS, szI, szS, szL] at *
  omega

/-! ## 10.5 The fire continuation and the box row -/

/-- **The fire continuation** — a parked implication's consequent enters
the residual station on a STRICT subderivation. -/
theorem hgt_fireCont {Γ Γ' : List Neg} {j : JD} {Q Q₀ : Pos} {N : Neg}
    {P : Pos} {rest K : List Neg} (h : Neg.imp Q N ∈ Γ)
    (s_d : Stab Γ .tru Q) (lf' : LFoc Γ N j P) (S : Sub Γ (N :: Γ'))
    (h' : N ∈ N :: Γ')
    (hsplit : ∀ Z ∈ Γ', Z = Neg.imp Q₀ N ∨ Z ∈ rest ∨ Z ∈ K) :
    hgtI (fireClean hsplit (.stable (.lfoc h' (lf'.wk S))))
      < hgtS (Stab.lfoc h (.impL s_d lf')) := by
  have hb := szI_fireClean hsplit
    (Inv.stable (Stab.lfoc h' (LFoc.wk S lf')))
  have hw := szL_wk S lf'
  have hs := szS_pos s_d
  have e1 : szI (Inv.stable (Stab.lfoc h' (LFoc.wk S lf')))
      = szL (LFoc.wk S lf') + 2 := rfl
  have e2 : szS (Stab.lfoc h (LFoc.impL s_d lf'))
      = szS s_d + szL lf' + 2 := rfl
  simp only [hgtI, hgtS]
  omega

/-- **The box row** — opening a parked box is height-NEUTRAL, so the
station weight has to pay, and it does (`dec_boxE`:
`2·3^w(↑Q) + Σrest < 3^w(◯Q) + Σrest`). -/
theorem hgt_boxRow {Γ Γ' : List Neg} {Q P : Pos} {rest K : List Neg}
    (h : Neg.circ Q ∈ Γ) (d : Inv Γ [Q] .lax (.up P))
    (S : Sub Γ (Neg.up Q :: Γ')) (h' : Neg.up Q ∈ Neg.up Q :: Γ')
    (hsplit : ∀ Z ∈ Γ', Z = Neg.circ Q ∨ Z ∈ rest ∨ Z ∈ K) :
    hgtI (boxClean hsplit (.stable (.lfoc h' (.rel (d.wk S)))))
      ≤ hgtS (Stab.lfoc h (.circL d)) := by
  have hb := szI_boxClean hsplit
    (Inv.stable (Stab.lfoc h' (LFoc.rel (Inv.wk S d))))
  have hw := szI_wk S d
  have e1 : szI (Inv.stable (Stab.lfoc h' (LFoc.rel (Inv.wk S d))))
      = szI (Inv.wk S d) + 3 := rfl
  have e2 : szS (Stab.lfoc h (LFoc.circL d)) = szI d + 2 := rfl
  simp only [hgtI, hgtS]
  omega

/-! ## 10.6 The two release sites, via Part 9

`negOfDownStab` rises (Part 6: `+1` at `↑P′`, `+2` at `◯P′`; §7.3:
unboundedly at a conjunction).  Part 9's replacements spend the `laxOf`
the goal is about to acquire INSIDE the release continuation, and both
land strictly below the caller's normalised height. -/

theorem hgt_releaseUp {Δ : List Neg} {P' : Pos}
    (s : Stab Δ .tru (.down (.up P'))) :
    hgtI (laxReleaseUp s) < hgtS (Stab.laxOf s) := by
  have := szI_laxReleaseUp s
  simp only [hgtI, hgtS, szS] at *
  omega

theorem hgt_releaseCirc {Δ : List Neg} {P' : Pos}
    (s : Stab Δ .tru (.down (.circ P'))) :
    hgtI (laxReleaseCirc s) < hgtS (Stab.laxOf s) := by
  have := szI_laxReleaseCirc s
  simp only [hgtI, hgtS, szS] at *
  omega

/-! ## 10.7 Goal inversion, and the processing edges

Goal inversion at an implication goal replays the derivation along one
branch of the antecedent's inversion (`extract`), from the PREMISE of the
`impR`; the replay is non-increasing (Part 3) and the premise is a strict
subderivation, so the edge drops the height. -/

theorem hgt_goalInv {Γ Γ₂ : List Neg} {Q : Pos} {N : Neg}
    (d₁ : Inv Γ [Q] .tru N) (b : List Neg) (hb : b ∈ invertPos Q)
    (H : Sub (b ++ Γ) Γ₂) :
    hgtI ((extract [] d₁ b hb).wk H) < hgtI (Inv.impR d₁) := by
  have h1 := szI_extract [] d₁ b hb
  have h2 := szI_wk H (extract [] d₁ b hb)
  have e1 : szI (Inv.impR d₁) = szI d₁ + 1 := rfl
  simp only [List.nil_append] at h1 h2 ⊢
  simp only [hgtI]
  omega

/-! The processing edges of `eMinPP`/`aMinPP` (`LJF/OFuelPMin.lean`).
Each is height NON-INCREASING while the station weight drops:

    parking (all EIGHT shapes)      `wk`                      EXACT (10.1)
    `↑(P∨Q)` split, `↑↓M`           `invUp`                   ≤ (Part 6)
    `M ∧ N`                         `invAndHyp`               ≤ (Part 6)
    `⊥ ⊃ N`                         `invImpFls`               ≤ (Part 6)
    fire scan                       `invFireHyp`              ≤ (Part 6)

and the three that refuted the order for `interpF` — `invImpOr`,
`invStrip`, `invCurry` (§7.2) — are NOT among them, because `interpP`
parks `(Q₁∨Q₂) ⊃ N`, `↓↑P′ ⊃ N` and `↓(M₁∧M₂) ⊃ N` instead of reshaping
them.  Restated in normalised form for completeness: -/

theorem hgt_invUp {R : Pos} {Γ : List Neg} {j : JD} {C : Neg}
    (hR : ∀ a : String, R ≠ .atom a)
    (d : Inv (.up R :: Γ) [] j C) (b : List Neg) (hb : b ∈ invertPos R) :
    hgtI (invUp d b hb) ≤ hgtI d := szI_invUp hR d b hb

theorem hgt_invAndHyp {M N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.and M N :: Γ) [] j C) : hgtI (invAndHyp d) ≤ hgtI d :=
  szI_invAndHyp d

theorem hgt_invImpFls {N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp .fls N :: Γ) [] j C) : hgtI (invImpFls d) ≤ hgtI d :=
  szI_invImpFls d

theorem hgt_invFireHyp {a : String} {N : Neg} {done rest Δext : List Neg}
    {j : JD} {C : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done)
    (d : Inv (done ++ Δext) [] j C) : hgtI (invFireHyp h d) ≤ hgtI d :=
  szI_invFireHyp h d

/-! ## 10.8 What Part 10 does NOT establish

It is the height side of the edge table, not the founding.  Two things
are still needed for `SatE2P`/`SatA2P` (`LJF/OFuelPMin.lean`):

* the STATION side — the second component of `μ` — which is the
  `LJF/O.lean` measure unchanged, discharged by the `ljf_dec_e` /
  `ljf_dec_a` farms; the parking clauses use `dec_park`, where the three
  reshaping clauses used `dec_impor` / `dec_stripshift` / `dec_curry`;
* the family itself in fuel-carrying (`UpFrom`/`UpFrom2`) form.  The
  witness bookkeeping is not a termination question and is not addressed
  here. -/

end LJFO

/-! ### Axiom audit -/

#axioms_within LJFO.szI_wk [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_extract [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_invBranches [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.sz_routeStab [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.sz_routeStabT [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.sz_relStab [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.sz_simInv [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_simHyp [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_invAndHyp [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_invImpFls [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_invUp [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_invFireHyp [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_fireClean [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_boxClean [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_negOfDownStab_up [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_negOfDownStab_circ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szS_ceS [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szS_stabOr1_ceS [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_ceOrD [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_ceStD [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_ceCyD [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_dpD [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.htI_dpD [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_laxReleaseUp [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_laxReleaseCirc [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_negOfDownStab_and [propext, Classical.choice, Quot.sound]

/-! Part 10 -/

#axioms_within LJFO.hgt_stable [propext]
#axioms_within LJFO.hgt_lfoc [propext]
#axioms_within LJFO.hgt_rfoc [propext]
#axioms_within LJFO.hgt_wk [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szI_pos [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szS_pos [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szL_pos [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.szR_pos [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hgt_antDispatch [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hgt_fireCont [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hgt_boxRow [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hgt_releaseUp [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hgt_releaseCirc [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hgt_goalInv [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hgt_impR [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hgt_laxOf [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hgt_lfImpL_ant [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hgt_lfImpL_cont [propext, Classical.choice, Quot.sound]
