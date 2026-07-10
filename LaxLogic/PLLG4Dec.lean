import LaxLogic.PLLG4Set
import LaxLogic.PLLG4Space

/-!
# Termination C: the decider — F&M Theorem 2.8

Backward proof search for the cumulative set calculus `G4s`: the
working context is carried as a **list** (computable iteration), the
loop-check keys sequents by the context's `toFinset`, and a **fuel**
parameter makes the recursion structural.  The gate admits only
sequents inside the finite space of `PLLG4Space.lean`, so fuel
`|seqEnum \ V| + 1` always suffices: every recursive call inserts the
current set-sequent into `V`, and gated sequents live in `seqEnum`.

* `search_sound` — success yields a `G4s` derivation (visited hits
  return `false`, so success never uses them).
* `search_complete` — a *minimal-height* `G4sh` derivation searches
  successfully: strong induction on height, carrying the invariant
  that every visited sequent has minimal height strictly above the
  current subderivation, so a premise can never collide with the
  visited set.

Chained through `G4c.iff_set` and `G4c.equiv_tm`:
`Decidable (G4c Γ C)` and **decidability of PLL provability**.
-/

open PLLFormula

namespace PLLND

/-- The finite ambient space of set-sequents. -/
def seqEnum (as : Finset String) (W : Nat) :
    Finset (Finset PLLFormula × PLLFormula) :=
  (enum as W).powerset ×ˢ enum as W

private theorem card_lem {S : Finset PLLFormula × PLLFormula}
    {V E : Finset (Finset PLLFormula × PLLFormula)}
    (hE : S ∈ E) (hV : S ∉ V) :
    (E \ insert S V).card < (E \ V).card := by
  have h1 : E \ insert S V = (E \ V).erase S := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
    tauto
  rw [h1]
  exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨hE, hV⟩)


private theorem orl {a b : Bool} (h : a = true) : (a || b) = true := by
  simp [h]

private theorem orr {a b : Bool} (h : b = true) : (a || b) = true := by
  simp [h]

private theorem andI {a b : Bool} (h₁ : a = true) (h₂ : b = true) :
    (a && b) = true := by simp [h₁, h₂]

private theorem anyI {α : Type _} {l : List α} {p : α → Bool} {x : α}
    (hx : x ∈ l) (h : p x = true) : l.any p = true := by
  simp only [List.any_eq_true]
  exact ⟨x, hx, h⟩

/-- Backward proof search for `G4s`. -/
def search (W : Nat) (as : Finset String) :
    Nat → Finset (Finset PLLFormula × PLLFormula) →
    List PLLFormula → PLLFormula → Bool
  | 0, _, _, _ => false
  | fuel + 1, V, Γ, C =>
    if (∀ F ∈ Γ, InSpace W as F) ∧ InSpace W as C ∧ (Γ.toFinset, C) ∉ V then
      decide (falsePLL ∈ Γ)
      || (match C with
          | .prop a => decide (PLLFormula.prop a ∈ Γ)
          | .falsePLL => false
          | .and A B =>
              search W as fuel (insert (Γ.toFinset, C) V) Γ A
              && search W as fuel (insert (Γ.toFinset, C) V) Γ B
          | .or A B =>
              search W as fuel (insert (Γ.toFinset, C) V) Γ A
              || search W as fuel (insert (Γ.toFinset, C) V) Γ B
          | .ifThen A B =>
              search W as fuel (insert (Γ.toFinset, C) V) (A :: Γ) B
          | .somehow A =>
              search W as fuel (insert (Γ.toFinset, C) V) Γ A
              || Γ.any fun X => match X with
                  | .somehow x =>
                      search W as fuel (insert (Γ.toFinset, C) V) (x :: Γ) C
                  | _ => false)
      || Γ.any fun F => match F with
          | .and A B =>
              search W as fuel (insert (Γ.toFinset, C) V) (A :: B :: Γ) C
          | .or A B =>
              search W as fuel (insert (Γ.toFinset, C) V) (A :: Γ) C
              && search W as fuel (insert (Γ.toFinset, C) V) (B :: Γ) C
          | .ifThen (.prop a) B =>
              decide (PLLFormula.prop a ∈ Γ)
              && search W as fuel (insert (Γ.toFinset, C) V) (B :: Γ) C
          | .ifThen (.and A B) D =>
              search W as fuel (insert (Γ.toFinset, C) V)
                (A.ifThen (B.ifThen D) :: Γ) C
          | .ifThen (.or A B) D =>
              search W as fuel (insert (Γ.toFinset, C) V)
                (A.ifThen D :: B.ifThen D :: Γ) C
          | .ifThen (.ifThen A B) D =>
              search W as fuel (insert (Γ.toFinset, C) V)
                (B.ifThen D :: Γ) (A.ifThen B)
              && search W as fuel (insert (Γ.toFinset, C) V) (D :: Γ) C
          | .ifThen (.somehow A) B =>
              (search W as fuel (insert (Γ.toFinset, C) V) Γ A
                && search W as fuel (insert (Γ.toFinset, C) V) (B :: Γ) C)
              || Γ.any fun X => match X with
                  | .somehow x =>
                      search W as fuel (insert (Γ.toFinset, C) V)
                        (x :: Γ) A.somehow
                      && search W as fuel (insert (Γ.toFinset, C) V)
                        (B :: Γ) C
                  | _ => false
          | _ => false
    else false

private theorem pair_heights {Γ₁ Γ₂ : Finset PLLFormula} {C₁ C₂ : PLLFormula}
    (d₁ : G4s Γ₁ C₁) (d₂ : G4s Γ₂ C₂) :
    ∃ n, G4sh n Γ₁ C₁ ∧ G4sh n Γ₂ C₂ := by
  obtain ⟨n₁, h₁⟩ := d₁
  obtain ⟨n₂, h₂⟩ := d₂
  exact ⟨max n₁ n₂, h₁.mono (Nat.le_max_left _ _),
    h₂.mono (Nat.le_max_right _ _)⟩

/-- **Soundness of the search.** -/
theorem search_sound (W : Nat) (as : Finset String) :
    ∀ (fuel : Nat) (V : Finset (Finset PLLFormula × PLLFormula))
    (Γ : List PLLFormula) (C : PLLFormula),
    search W as fuel V Γ C = true → G4s Γ.toFinset C := by
  intro fuel
  induction fuel with
  | zero => intro V Γ C h; simp [search] at h
  | succ fuel ih =>
    intro V Γ C h
    simp only [search] at h
    split at h
    case isFalse => simp at h
    case isTrue hg =>
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    rcases h with (hbot | hC) | ⟨F, hFmem, hF⟩
    · exact ⟨0, .botL (List.mem_toFinset.mpr hbot)⟩
    · cases C with
      | prop a =>
          simp only [decide_eq_true_eq] at hC
          exact ⟨0, .init (List.mem_toFinset.mpr hC)⟩
      | falsePLL => simp at hC
      | and A B =>
          simp only [Bool.and_eq_true] at hC
          obtain ⟨n, h₁, h₂⟩ := pair_heights (ih _ _ _ hC.1) (ih _ _ _ hC.2)
          exact ⟨n + 1, .andR h₁ h₂⟩
      | or A B =>
          simp only [Bool.or_eq_true] at hC
          rcases hC with hs | hs
          · obtain ⟨n, d⟩ := ih _ _ _ hs
            exact ⟨n + 1, .orR1 d⟩
          · obtain ⟨n, d⟩ := ih _ _ _ hs
            exact ⟨n + 1, .orR2 d⟩
      | ifThen A B =>
          obtain ⟨n, d⟩ := ih _ _ _ hC
          rw [List.toFinset_cons] at d
          exact ⟨n + 1, .impR d⟩
      | somehow A =>
          simp only [Bool.or_eq_true, List.any_eq_true] at hC
          rcases hC with hs | ⟨X, hXmem, hX⟩
          · obtain ⟨n, d⟩ := ih _ _ _ hs
            exact ⟨n + 1, .laxR d⟩
          · cases X with
            | somehow x =>
                obtain ⟨n, d⟩ := ih _ _ _ hX
                rw [List.toFinset_cons] at d
                exact ⟨n + 1, .laxL (List.mem_toFinset.mpr hXmem) d⟩
            | prop a => simp at hX
            | falsePLL => simp at hX
            | and _ _ => simp at hX
            | or _ _ => simp at hX
            | ifThen _ _ => simp at hX
    · have hFΓ := List.mem_toFinset.mpr hFmem
      cases F with
      | prop a => simp at hF
      | falsePLL => simp at hF
      | and A B =>
          obtain ⟨n, d⟩ := ih _ _ _ hF
          rw [List.toFinset_cons, List.toFinset_cons] at d
          exact ⟨n + 1, .andL hFΓ d⟩
      | or A B =>
          simp only [Bool.and_eq_true] at hF
          obtain ⟨n, h₁, h₂⟩ := pair_heights (ih _ _ _ hF.1) (ih _ _ _ hF.2)
          rw [List.toFinset_cons] at h₁ h₂
          exact ⟨n + 1, .orL hFΓ h₁ h₂⟩
      | somehow A => simp at hF
      | ifThen A' B =>
          cases A' with
          | prop a =>
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hF
              obtain ⟨n, d⟩ := ih _ _ _ hF.2
              rw [List.toFinset_cons] at d
              exact ⟨n + 1, .impLProp hFΓ (List.mem_toFinset.mpr hF.1) d⟩
          | falsePLL => simp at hF
          | and A₁ B₁ =>
              obtain ⟨n, d⟩ := ih _ _ _ hF
              rw [List.toFinset_cons] at d
              exact ⟨n + 1, .impLAnd hFΓ d⟩
          | or A₁ B₁ =>
              obtain ⟨n, d⟩ := ih _ _ _ hF
              rw [List.toFinset_cons, List.toFinset_cons] at d
              exact ⟨n + 1, .impLOr hFΓ d⟩
          | ifThen A₁ B₁ =>
              simp only [Bool.and_eq_true] at hF
              obtain ⟨n, h₁, h₂⟩ := pair_heights (ih _ _ _ hF.1) (ih _ _ _ hF.2)
              rw [List.toFinset_cons] at h₁ h₂
              exact ⟨n + 1, .impLImp hFΓ h₁ h₂⟩
          | somehow A₁ =>
              simp only [Bool.or_eq_true, Bool.and_eq_true,
                List.any_eq_true] at hF
              rcases hF with ⟨hs₁, hs₂⟩ | ⟨X, hXmem, hX⟩
              · obtain ⟨n, h₁, h₂⟩ :=
                  pair_heights (ih _ _ _ hs₁) (ih _ _ _ hs₂)
                rw [List.toFinset_cons] at h₂
                exact ⟨n + 1, .impLLax hFΓ h₁ h₂⟩
              · cases X with
                | somehow x =>
                    simp only [Bool.and_eq_true] at hX
                    obtain ⟨n, h₁, h₂⟩ :=
                      pair_heights (ih _ _ _ hX.1) (ih _ _ _ hX.2)
                    rw [List.toFinset_cons] at h₁ h₂
                    exact ⟨n + 1,
                      .impLLaxLax hFΓ (List.mem_toFinset.mpr hXmem) h₁ h₂⟩
                | prop a => simp at hX
                | falsePLL => simp at hX
                | and _ _ => simp at hX
                | or _ _ => simp at hX
                | ifThen _ _ => simp at hX

/-- **Completeness of the search** for minimal-height derivations,
carrying the visited-set invariant. -/
theorem search_complete (W : Nat) (as : Finset String) :
    ∀ (n : Nat) (Γ : List PLLFormula) (C : PLLFormula) (fuel : Nat)
    (V : Finset (Finset PLLFormula × PLLFormula)),
    G4sh n Γ.toFinset C →
    (∀ m, G4sh m Γ.toFinset C → n ≤ m) →
    (∀ F ∈ Γ, InSpace W as F) → InSpace W as C →
    (∀ T ∈ V, ∀ m, G4sh m T.1 T.2 → n < m) →
    (seqEnum as W \ V).card < fuel →
    search W as fuel V Γ C = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro Γ C fuel V d hmin hctx hgoal hV hfuel
  cases fuel with
  | zero => exact absurd hfuel (Nat.not_lt_zero _)
  | succ fuel =>
  classical
  have hSmem : (Γ.toFinset, C) ∈ seqEnum as W :=
    Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr fun F hF =>
          InSpace.mem_enum W (hctx F (List.mem_toFinset.mp hF)),
       InSpace.mem_enum W hgoal⟩
  have hnotV : (Γ.toFinset, C) ∉ V := fun hin => by
    have := hV _ hin n d
    omega
  have hfuel' : (seqEnum as W \ insert (Γ.toFinset, C) V).card < fuel := by
    have := card_lem hSmem hnotV
    omega
  have mkInv : ∀ {pm : Nat}, pm < n →
      ∀ T ∈ insert (Γ.toFinset, C) V, ∀ m, G4sh m T.1 T.2 → pm < m := by
    intro pm hpm T hT m dm
    rcases Finset.mem_insert.mp hT with heq | hT'
    · subst heq
      exact lt_of_lt_of_le hpm (hmin m dm)
    · exact lt_trans hpm (hV T hT' m dm)
  simp only [search]
  rw [if_pos ⟨hctx, hgoal, hnotV⟩]
  cases d with
  | init h =>
      refine orl (orr ?_)
      exact decide_eq_true (List.mem_toFinset.mp h)
  | botL h =>
      refine orl (orl ?_)
      exact decide_eq_true (List.mem_toFinset.mp h)
  | @andR np _ A B dpa dpb =>
      have hexA : ∃ m, G4sh m Γ.toFinset A := ⟨np, dpa⟩
      have hexB : ∃ m, G4sh m Γ.toFinset B := ⟨np, dpb⟩
      have hsA := IH (Nat.find hexA)
        (by have := Nat.find_min' hexA dpa; omega) Γ A fuel _
        (Nat.find_spec hexA) (fun m dm => Nat.find_min' hexA dm)
        hctx hgoal.and_left
        (mkInv (by have := Nat.find_min' hexA dpa; omega)) hfuel'
      have hsB := IH (Nat.find hexB)
        (by have := Nat.find_min' hexB dpb; omega) Γ B fuel _
        (Nat.find_spec hexB) (fun m dm => Nat.find_min' hexB dm)
        hctx hgoal.and_right
        (mkInv (by have := Nat.find_min' hexB dpb; omega)) hfuel'
      refine orl (orr ?_)
      exact andI hsA hsB
  | @orR1 np _ A B dp =>
      have hex : ∃ m, G4sh m Γ.toFinset A := ⟨np, dp⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp; omega) Γ A fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx hgoal.or_left
        (mkInv (by have := Nat.find_min' hex dp; omega)) hfuel'
      refine orl (orr ?_)
      exact orl hs
  | @orR2 np _ A B dp =>
      have hex : ∃ m, G4sh m Γ.toFinset B := ⟨np, dp⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp; omega) Γ B fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx hgoal.or_right
        (mkInv (by have := Nat.find_min' hex dp; omega)) hfuel'
      refine orl (orr ?_)
      exact orr hs
  | @impR np _ A B dp =>
      have dp' : G4sh np ((A :: Γ).toFinset) B := by
        rw [List.toFinset_cons]; exact dp
      have hex : ∃ m, G4sh m ((A :: Γ).toFinset) B := ⟨np, dp'⟩
      have hctx' : ∀ F ∈ A :: Γ, InSpace W as F := by
        intro F hF
        rcases List.mem_cons.mp hF with rfl | hF'
        · exact hgoal.imp_left
        · exact hctx F hF'
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega) (A :: Γ) B fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx' hgoal.imp_right
        (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orl (orr ?_)
      exact hs
  | @laxR np _ A dp =>
      have hex : ∃ m, G4sh m Γ.toFinset A := ⟨np, dp⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp; omega) Γ A fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx hgoal.box
        (mkInv (by have := Nat.find_min' hex dp; omega)) hfuel'
      refine orl (orr ?_)
      exact orl hs
  | @laxL np _ A B h dp =>
      have dp' : G4sh np ((A :: Γ).toFinset) B.somehow := by
        rw [List.toFinset_cons]; exact dp
      have hex : ∃ m, G4sh m ((A :: Γ).toFinset) B.somehow := ⟨np, dp'⟩
      have hctx' : ∀ F ∈ A :: Γ, InSpace W as F := by
        intro F hF
        rcases List.mem_cons.mp hF with rfl | hF'
        · exact (hctx _ (List.mem_toFinset.mp h)).box
        · exact hctx F hF'
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega) (A :: Γ) B.somehow fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx' hgoal
        (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orl (orr ?_)
      refine orr ?_
      exact anyI (List.mem_toFinset.mp h) hs
  | @andL np _ A B _ h dp =>
      have dp' : G4sh np ((A :: B :: Γ).toFinset) C := by
        rw [List.toFinset_cons, List.toFinset_cons]; exact dp
      have hex : ∃ m, G4sh m ((A :: B :: Γ).toFinset) C := ⟨np, dp'⟩
      have hctx' : ∀ F ∈ A :: B :: Γ, InSpace W as F := by
        intro F hF
        rcases List.mem_cons.mp hF with rfl | hF'
        · exact (hctx _ (List.mem_toFinset.mp h)).and_left
        rcases List.mem_cons.mp hF' with rfl | hF''
        · exact (hctx _ (List.mem_toFinset.mp h)).and_right
        · exact hctx F hF''
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega) (A :: B :: Γ) C fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        hctx' hgoal
        (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orr ?_
      exact anyI (List.mem_toFinset.mp h) hs
  | @orL np _ A B _ h dpa dpb =>
      have dpa' : G4sh np ((A :: Γ).toFinset) C := by
        rw [List.toFinset_cons]; exact dpa
      have dpb' : G4sh np ((B :: Γ).toFinset) C := by
        rw [List.toFinset_cons]; exact dpb
      have hexA : ∃ m, G4sh m ((A :: Γ).toFinset) C := ⟨np, dpa'⟩
      have hexB : ∃ m, G4sh m ((B :: Γ).toFinset) C := ⟨np, dpb'⟩
      have hsA := IH (Nat.find hexA)
        (by have := Nat.find_min' hexA dpa'; omega) (A :: Γ) C fuel _
        (Nat.find_spec hexA) (fun m dm => Nat.find_min' hexA dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (List.mem_toFinset.mp h)).or_left
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hexA dpa'; omega)) hfuel'
      have hsB := IH (Nat.find hexB)
        (by have := Nat.find_min' hexB dpb'; omega) (B :: Γ) C fuel _
        (Nat.find_spec hexB) (fun m dm => Nat.find_min' hexB dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (List.mem_toFinset.mp h)).or_right
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hexB dpb'; omega)) hfuel'
      refine orr ?_
      exact anyI (List.mem_toFinset.mp h) (andI hsA hsB)
  | @impLProp np _ a B _ h ha dp =>
      have dp' : G4sh np ((B :: Γ).toFinset) C := by
        rw [List.toFinset_cons]; exact dp
      have hex : ∃ m, G4sh m ((B :: Γ).toFinset) C := ⟨np, dp'⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega) (B :: Γ) C fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (List.mem_toFinset.mp h)).imp_right
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orr ?_
      refine anyI (List.mem_toFinset.mp h) ?_
      exact andI (decide_eq_true (List.mem_toFinset.mp ha)) hs
  | @impLAnd np _ A B D _ h dp =>
      have dp' : G4sh np ((A.ifThen (B.ifThen D) :: Γ).toFinset) C := by
        rw [List.toFinset_cons]; exact dp
      have hex : ∃ m, G4sh m ((A.ifThen (B.ifThen D) :: Γ).toFinset) C :=
        ⟨np, dp'⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega)
        (A.ifThen (B.ifThen D) :: Γ) C fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (List.mem_toFinset.mp h)).impAnd_piece
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orr ?_
      exact anyI (List.mem_toFinset.mp h) hs
  | @impLOr np _ A B D _ h dp =>
      have dp' : G4sh np ((A.ifThen D :: B.ifThen D :: Γ).toFinset) C := by
        rw [List.toFinset_cons, List.toFinset_cons]; exact dp
      have hex : ∃ m, G4sh m ((A.ifThen D :: B.ifThen D :: Γ).toFinset) C :=
        ⟨np, dp'⟩
      have hs := IH (Nat.find hex)
        (by have := Nat.find_min' hex dp'; omega)
        (A.ifThen D :: B.ifThen D :: Γ) C fuel _
        (Nat.find_spec hex) (fun m dm => Nat.find_min' hex dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (List.mem_toFinset.mp h)).impOr_piece₁
            rcases List.mem_cons.mp hF' with rfl | hF''
            · exact (hctx _ (List.mem_toFinset.mp h)).impOr_piece₂
            · exact hctx F hF'')
        hgoal (mkInv (by have := Nat.find_min' hex dp'; omega)) hfuel'
      refine orr ?_
      exact anyI (List.mem_toFinset.mp h) hs
  | @impLImp np _ A B D _ h dpa dpb =>
      have dpa' : G4sh np ((B.ifThen D :: Γ).toFinset) (A.ifThen B) := by
        rw [List.toFinset_cons]; exact dpa
      have dpb' : G4sh np ((D :: Γ).toFinset) C := by
        rw [List.toFinset_cons]; exact dpb
      have hexA : ∃ m, G4sh m ((B.ifThen D :: Γ).toFinset) (A.ifThen B) :=
        ⟨np, dpa'⟩
      have hexB : ∃ m, G4sh m ((D :: Γ).toFinset) C := ⟨np, dpb'⟩
      have hsA := IH (Nat.find hexA)
        (by have := Nat.find_min' hexA dpa'; omega)
        (B.ifThen D :: Γ) (A.ifThen B) fuel _
        (Nat.find_spec hexA) (fun m dm => Nat.find_min' hexA dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (List.mem_toFinset.mp h)).impImp_piece
            · exact hctx F hF')
        (hctx _ (List.mem_toFinset.mp h)).imp_left
        (mkInv (by have := Nat.find_min' hexA dpa'; omega)) hfuel'
      have hsB := IH (Nat.find hexB)
        (by have := Nat.find_min' hexB dpb'; omega) (D :: Γ) C fuel _
        (Nat.find_spec hexB) (fun m dm => Nat.find_min' hexB dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (List.mem_toFinset.mp h)).imp_right
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hexB dpb'; omega)) hfuel'
      refine orr ?_
      exact anyI (List.mem_toFinset.mp h) (andI hsA hsB)
  | @impLLax np _ A B _ h dpa dpb =>
      have dpb' : G4sh np ((B :: Γ).toFinset) C := by
        rw [List.toFinset_cons]; exact dpb
      have hexA : ∃ m, G4sh m Γ.toFinset A := ⟨np, dpa⟩
      have hexB : ∃ m, G4sh m ((B :: Γ).toFinset) C := ⟨np, dpb'⟩
      have hsA := IH (Nat.find hexA)
        (by have := Nat.find_min' hexA dpa; omega) Γ A fuel _
        (Nat.find_spec hexA) (fun m dm => Nat.find_min' hexA dm)
        hctx ((hctx _ (List.mem_toFinset.mp h)).imp_left).box
        (mkInv (by have := Nat.find_min' hexA dpa; omega)) hfuel'
      have hsB := IH (Nat.find hexB)
        (by have := Nat.find_min' hexB dpb'; omega) (B :: Γ) C fuel _
        (Nat.find_spec hexB) (fun m dm => Nat.find_min' hexB dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (List.mem_toFinset.mp h)).imp_right
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hexB dpb'; omega)) hfuel'
      refine orr ?_
      refine anyI (List.mem_toFinset.mp h) ?_
      exact orl (andI hsA hsB)
  | @impLLaxLax np _ A B X _ h hX dpa dpb =>
      have dpa' : G4sh np ((X :: Γ).toFinset) A.somehow := by
        rw [List.toFinset_cons]; exact dpa
      have dpb' : G4sh np ((B :: Γ).toFinset) C := by
        rw [List.toFinset_cons]; exact dpb
      have hexA : ∃ m, G4sh m ((X :: Γ).toFinset) A.somehow := ⟨np, dpa'⟩
      have hexB : ∃ m, G4sh m ((B :: Γ).toFinset) C := ⟨np, dpb'⟩
      have hsA := IH (Nat.find hexA)
        (by have := Nat.find_min' hexA dpa'; omega) (X :: Γ) A.somehow fuel _
        (Nat.find_spec hexA) (fun m dm => Nat.find_min' hexA dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (List.mem_toFinset.mp hX)).box
            · exact hctx F hF')
        (hctx _ (List.mem_toFinset.mp h)).imp_left
        (mkInv (by have := Nat.find_min' hexA dpa'; omega)) hfuel'
      have hsB := IH (Nat.find hexB)
        (by have := Nat.find_min' hexB dpb'; omega) (B :: Γ) C fuel _
        (Nat.find_spec hexB) (fun m dm => Nat.find_min' hexB dm)
        (by intro F hF
            rcases List.mem_cons.mp hF with rfl | hF'
            · exact (hctx _ (List.mem_toFinset.mp h)).imp_right
            · exact hctx F hF')
        hgoal (mkInv (by have := Nat.find_min' hexB dpb'; omega)) hfuel'
      refine orr ?_
      refine anyI (List.mem_toFinset.mp h) ?_
      refine orr ?_
      exact anyI (List.mem_toFinset.mp hX) (andI hsA hsB)

/-! ### The decision procedure, packaged -/

/-- Weight bound of a list of formulas. -/
def listWeight (l : List PLLFormula) : Nat :=
  l.foldr (fun φ m => max φ.weight m) 0

theorem le_listWeight {φ : PLLFormula} {l : List PLLFormula} (h : φ ∈ l) :
    φ.weight ≤ listWeight l := by
  induction l with
  | nil => cases h
  | cons x l ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_left _ _
      · exact le_trans (ih h') (Nat.le_max_right _ _)

/-- Atom alphabet of a list of formulas. -/
def listAtoms (l : List PLLFormula) : Finset String :=
  l.foldr (fun φ s => φ.atoms ∪ s) ∅

theorem subset_listAtoms {φ : PLLFormula} {l : List PLLFormula} (h : φ ∈ l) :
    φ.atoms ⊆ listAtoms l := by
  induction l with
  | nil => cases h
  | cons x l ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact Finset.subset_union_left
      · exact subset_trans (ih h') Finset.subset_union_right

theorem seqEnum_card (as : Finset String) (W : Nat) :
    (seqEnum as W).card = 2 ^ (enum as W).card * (enum as W).card := by
  rw [seqEnum, Finset.card_product, Finset.card_powerset]

/-- Fuel sufficient for the whole space of the end-sequent, computed
arithmetically (the powerset is never constructed). -/
def decideFuel (Γ : List PLLFormula) (C : PLLFormula) : Nat :=
  2 ^ (enum (listAtoms (C :: Γ)) (listWeight (C :: Γ))).card
    * (enum (listAtoms (C :: Γ)) (listWeight (C :: Γ))).card + 1

/-- **The search decides `G4c`.** -/
theorem G4c_iff_search {Γ : List PLLFormula} {C : PLLFormula} :
    G4c Γ C ↔
    search (listWeight (C :: Γ)) (listAtoms (C :: Γ))
      (decideFuel Γ C) ∅ Γ C = true := by
  constructor
  · intro h
    obtain ⟨n₀, d₀⟩ := G4c.iff_set.mp h
    classical
    have hex : ∃ m, G4sh m Γ.toFinset C := ⟨n₀, d₀⟩
    refine search_complete _ _ (Nat.find hex) Γ C _ ∅ (Nat.find_spec hex)
      (fun m dm => Nat.find_min' hex dm) ?_ ?_
      (fun T hT => absurd hT (Finset.notMem_empty T)) ?_
    · intro F hF
      exact ⟨le_listWeight (List.mem_cons_of_mem _ hF),
        subset_listAtoms (List.mem_cons_of_mem _ hF)⟩
    · exact ⟨le_listWeight (List.mem_cons_self),
        subset_listAtoms (List.mem_cons_self)⟩
    · rw [Finset.sdiff_empty, seqEnum_card]
      exact Nat.lt_succ_self _
  · intro h
    exact G4c.iff_set.mpr (search_sound _ _ _ _ _ _ h)

/-- `G4c` — hence PLL — is decidable. -/
instance decidableG4c (Γ : List PLLFormula) (C : PLLFormula) :
    Decidable (G4c Γ C) :=
  decidable_of_iff _ G4c_iff_search.symm

/-- **F&M Theorem 2.8, decidability**: inhabitation of the PLL term
calculus is decidable — via the terminating, loop-checked backward
search for the complete calculus G4iLL″. -/
instance decidablePLL (Γ : List PLLFormula) (φ : PLLFormula) :
    Decidable (Nonempty (Tm Γ φ)) :=
  decidable_of_iff _ G4c.equiv_tm

-- ◯ admits no escape: the constraint stays.
/-- info: false -/
#guard_msgs in
#eval decide (G4c [(prop "p").somehow] (prop "p"))

-- …but the unit is there.
/-- info: true -/
#guard_msgs in
#eval decide (G4c [prop "p"] (prop "p").somehow)

/-- info: true -/
#guard_msgs in
#eval decide (G4c [] (falsePLL.ifThen falsePLL))

/-- info: false -/
#guard_msgs in
#eval decide (G4c [] (prop "p"))

/--
info: 'PLLND.G4c_iff_search' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G4c_iff_search

end PLLND
