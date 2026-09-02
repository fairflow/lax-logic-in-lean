/-
# `searchW` — the Gbu◯/FRJW dichotomy induction

Templated from `searchO` (`wip/gbu_search_circ.lean`), Type-valued
(delivers derivations), two public modes, no supply hypotheses.
Divergences from the template are documented case by case.
-/
import wip.gbu_frjw_circdb
import wip.gbu_frjw_corner
import wip.gbu_ljfo_transport

namespace FRJ.Gbu.W

open FRJ Form FRJ.Gbu FRJ.Search

/-! ## Type-valued search infrastructure

The searchO helpers eliminate `Or`/`∃` into Prop goals; the Type-valued
motive needs constructive (`⊕`/`Σ'`) forms. -/

private def byDec {p : Prop} (d : Decidable p) {q : Sort _}
    (h1 : p → q) (h2 : ¬ p → q) : q := by
  cases d with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

private def decClo (Ψ : List Form) (A : Form) : Decidable (Clo Ψ A) :=
  match h : cloB Ψ A with
  | true => isTrue (cloB_iff.mp h)
  | false => isFalse (by
      intro hc; rw [cloB_iff.mpr hc] at h; exact Bool.noConfusion h)

/-- Constructive `findNot`: a total scan. -/
private def findNotT {α : Type} {P : α → Prop} (dec : ∀ a, Decidable (P a)) :
    ∀ l : List α, (∀ a ∈ l, P a) ⊕' (Σ' a, a ∈ l ∧ ¬ P a)
  | [] => .inl (fun _ h => absurd h List.not_mem_nil)
  | a :: l =>
      match dec a with
      | isFalse h => .inr ⟨a, List.mem_cons_self, h⟩
      | isTrue ha =>
          match findNotT dec l with
          | .inl hall => .inl (fun x hx =>
              (List.mem_cons.mp hx).elim (fun e => e ▸ ha) (hall x))
          | .inr ⟨x, hx, hnx⟩ => .inr ⟨x, List.mem_cons_of_mem _ hx, hnx⟩

/-- Constructive list split at a member. -/
private def splitOfMem {α : Type} [DecidableEq α] :
    ∀ {l : List α} {a : α}, a ∈ l → Σ' s t, l = s ++ a :: t
  | [], _, h => absurd h List.not_mem_nil
  | b :: l, a, h =>
      if e : a = b then ⟨[], l, by subst e; rfl⟩
      else
        match splitOfMem (l := l) (a := a)
          ((List.mem_cons.mp h).resolve_left e) with
        | ⟨s, t, ht⟩ => ⟨b :: s, t, by rw [ht]; rfl⟩

private def isHat (X : Form) : Bool := X.isPV || X.isImp || X.isCirc

/-- Constructive `splitHat`: all members `Ĝ`-shaped, or a split at a
non-`Ĝ` member. -/
private def splitHatT (Ψ : List Form) :
    (∀ X ∈ Ψ, isHat X = true) ⊕'
      (Σ' (l r : List Form) (X : Form),
        (Ψ = l ++ X :: r) ∧ isHat X = false) :=
  match findNotT (P := fun X => isHat X = true)
      (fun _ => inferInstance) Ψ with
  | .inl hall => .inl hall
  | .inr ⟨X, hX, hnX⟩ =>
      match splitOfMem hX with
      | ⟨l, r, hsplit⟩ =>
          .inr ⟨l, r, X, hsplit, by
            revert hnX; cases isHat X <;> simp⟩

/-! ## `≐`-transport for the queries, and the measure lemmas -/

private theorem ctxEq_cons_self {Γ : List Form} {A : Form} (h : A ∈ Γ) :
    Γ ≐ A :: Γ := by
  intro x
  refine ⟨fun hx => List.mem_cons_of_mem _ hx, fun hx => ?_⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact h
  · exact hx'

private theorem ctxEq_split {l r : List Form} {X : Form} :
    (l ++ X :: r) ≐ X :: (l ++ r) := by
  intro x
  constructor
  · intro hx
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
    · rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ h')
  · intro hx
    rcases List.mem_cons.mp hx with rfl | h'
    · exact List.mem_append_right _ List.mem_cons_self
    · rcases List.mem_append.mp h' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

private theorem ctxEq_symm {l m : List Form} (h : l ≐ m) : m ≐ l :=
  fun x => ⟨(h x).mpr, (h x).mp⟩

private theorem orTrue {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases a
  · exact Or.inr (by simpa using h)
  · exact Or.inl rfl

private theorem mem_gHat_of_isHat {G X : Form} (hsf : X ∈ sfL G)
    (hh : isHat X = true) : X ∈ gHat G := by
  rcases orTrue hh with h | h
  · rcases orTrue h with h' | h'
    · exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_filter.mpr ⟨hsf, h'⟩))
    · exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_filter.mpr ⟨hsf, h'⟩))
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hsf, h⟩)

private theorem wEvalR_ctxEq {D : WSeq → Prop} {Ψ Ψ' : List Form} {C : Form}
    (h : Ψ ≐ Ψ') (he : WEvalR D Ψ C) : WEvalR D Ψ' C :=
  let ⟨t, Γ, hmem, hcl⟩ := he
  ⟨t, Γ, hmem, fun X hX => hcl X ((h X).mpr hX)⟩

private theorem wEvalI_ctxEq {D : WSeq → Prop} {Ω Ω' : List Form} {C : Form}
    (h : Ω ≐ Ω') (he : WEvalI D Ω C) : WEvalI D Ω' C :=
  let ⟨St, Th, hmem, hSt, hΩ⟩ := he
  ⟨St, Th, hmem, fun {x} hx => (h x).mp (hSt hx),
    fun {x} hx => hΩ ((h x).mpr hx)⟩

private theorem seqSize_cons {Ψ : List Form} {X C : Form} :
    seqSize (X :: Ψ) C = X.size + seqSize Ψ C := by
  simp [seqSize]; omega

private theorem seqSize_split {l r : List Form} {X C : Form} :
    seqSize (l ++ X :: r) C = seqSize (l ++ r) C + X.size := by
  simp [seqSize]; omega

private theorem seqSize_goal {Ψ : List Form} {C C' : Form}
    (h : C'.size < C.size) : seqSize Ψ C' < seqSize Ψ C := by
  simp [seqSize]; omega

private theorem wgKeep {G : Form} {r : Bool} {Ψ Ψ' : List Form} {C C' : Form}
    (hcl : ∀ X ∈ Ψ, Clo Ψ' X) (hs : seqSize Ψ' C' < seqSize Ψ C)
    (htp : tpC r C' ≤ tpC r C := by
      first
        | exact Nat.le_refl _
        | exact tpC_false_mono orL'
        | exact tpC_false_mono orR'
        | exact tpC_le_circ _ _) :
    WgLt (wgC G r Ψ' C') (wgC G r Ψ C) :=
  wgCCtx (fun _ hX => clo_trans hcl hX) htp hs

private theorem wgFocus {G : Form} {Ψ Ψ' : List Form} {C C' : Form}
    (hcl : ∀ X ∈ Ψ, Clo Ψ' X) :
    WgLt (wgC G false Ψ' C') (wgC G true Ψ C) :=
  wgCFocus (fun _ hX => clo_trans hcl hX) (tpC_false_lt_true C C')

private theorem wgTpLt {G : Form} {r : Bool} {Ψ Ψ' : List Form} {C C' : Form}
    (hcl : ∀ X ∈ Ψ, Clo Ψ' X) (htp : tpC false C' < tpC r C) :
    WgLt (wgC G false Ψ' C') (wgC G r Ψ C) :=
  wgCFocus (fun _ hX => clo_trans hcl hX) htp

private theorem tpC_free_lt_circ {A Z : Form} (h : A.hasCirc = false) :
    tpC false A < tpC false (Form.circ Z) := by
  show (if A.hasCirc = true then 1 else 0) < 1
  rw [h]
  exact Nat.zero_lt_one

private theorem wgDrop {G : Form} {r r' : Bool} {Ψ Ψ' : List Form} {C C' : Form}
    (h : unclosed G Ψ' < unclosed G Ψ) : WgLt (wgC G r' Ψ' C') (wgC G r Ψ C) :=
  Or.inl h

/-! ## The classical branch: `Ax^I◯` manufacture -/

/-- The `Ax^I◯` row answers any query it classically covers: if some
valuation `ats ⊆ Ĝ_at` refutes `F` while forcing all of `Ω`, the
irregular `◯F`-row with the vacuous zone covers `Ω`. -/
theorem wEvalI_axIC {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    {Ω : List Form} {F : Form} {ats : List Form}
    (hats : ats ⊆ gAt G) (hFf : classForce ats F = false)
    (hgoal : Form.circ F ∈ sfR G)
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G) (hΩf : ∀ X ∈ Ω, classForce ats X = true) :
    WEvalI D Ω (.circ F) := by
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr [] (vacZoneA G ats) (.circ F))
      ⟨.axIC F ats hats hFf hgoal (CtxEq.refl _)⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSt, hTh⟩ =>
      exact ⟨St', Th', hs'mem,
        fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil,
        fun {x} hx => List.mem_append_right _
          (hTh (List.mem_filter.mpr ⟨hΩ x hx, hΩf x hx⟩))⟩

/-- Constructive search for a classical countermodel over the `Ĝ`-atom
valuations (scanned as sublists; `classForce` sees only membership). -/
private def findCMT (G : Form) (Ω : List Form) (F : Form) :
    (Σ' ats : List Form, ats ⊆ gAt G ∧ classForce ats F = false ∧
      ∀ X ∈ Ω, classForce ats X = true) ⊕'
    (∀ ats ∈ (gAt G).sublists,
      ¬ (classForce ats F = false ∧ ∀ X ∈ Ω, classForce ats X = true)) :=
  match findNotT (P := fun ats => ¬ (classForce ats F = false ∧
      ∀ X ∈ Ω, classForce ats X = true))
    (fun _ => inferInstance) (gAt G).sublists with
  | .inl hall => .inr hall
  | .inr ⟨ats, hmem, hnn⟩ =>
      .inl ⟨ats, (List.mem_sublists.mp hmem).subset,
        (Decidable.of_not_not hnn).1, (Decidable.of_not_not hnn).2⟩



/-- **Totality at a critical cell** — the corner's closure.  Every
`Sf^R`-form either carries a `RefAt` certificate over `Z :: R₀` (with
`R₀` absorbing every refuted form) or is `Gbu◯`-DERIVABLE, by
STRUCTURAL induction: `RefAt`'s clauses and the irregular introduction
rules are De Morgan duals (`∧`: one refuted side vs both derivable;
`∨`: both refuted vs one derivable); atoms split by context membership
(`evalI_axI_gHat`: a prime outside the context is always refuted); a
`¬Clo`-antecedent implication is refuted as a form (`.ups`) or hands
`¬WEvalR` to the regular stratum through `gbuInv9`'s contrapositive —
and that recursion drops `unclosed`, so the caller supplies it as a
callback.  Consequence: an antecedent failing the corner's `RefAt`
test is unrefuted, hence DERIVABLE, hence `L⊃ᵢ` steps through it. -/
private def totalityW {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    (decI : ∀ Ω C, Decidable (WEvalI D Ω C))
    {Ψ : List Form} {Z : Form} {R₀ : List Form}
    (hg : ∀ X ∈ Ψ, X ∈ gHat G)
    (hR₀mem : ∀ X, X ∈ sfR G → WEvalI D Ψ X → X ∈ R₀)
    (reccall : ∀ A' B', Form.imp A' B' ∈ sfR G → ¬ Clo Ψ A' →
      ¬ WEvalR D (A' :: Ψ) B' → GbuRC G (A' :: Ψ) B') :
    ∀ X, X ∈ sfR G → RefAt true (Z :: R₀) Ψ X ⊕' GbuIC G Ψ X
  | .bot, _ => .inl .bot
  | .atom a, hX =>
      byDec (decI Ψ (.atom a))
        (fun hI => .inl (.ups (List.mem_cons_of_mem _ (hR₀mem _ hX hI))))
        (fun hnI =>
          byDec (inferInstance : Decidable (Form.atom a ∈ Ψ))
            (fun hmem => .inr (.ax _ (ctxEq_cons_self hmem)))
            (fun hax => absurd (evalI_axI_gHat hsat hg rfl hX hax) hnI))
  | .and C₁ C₂, hX =>
      match totalityW hsat decI hg hR₀mem reccall C₁ (sfR_and hX).1,
            totalityW hsat decI hg hR₀mem reccall C₂ (sfR_and hX).2 with
      | .inr d₁, .inr d₂ => .inr (.randI d₁ d₂)
      | .inl r₁, _ => .inl (.andL r₁)
      | _, .inl r₂ => .inl (.andR r₂)
  | .or C₁ C₂, hX =>
      match totalityW hsat decI hg hR₀mem reccall C₁ (sfR_or hX).1,
            totalityW hsat decI hg hR₀mem reccall C₂ (sfR_or hX).2 with
      | .inr d₁, _ => .inr (.rorI1 d₁)
      | _, .inr d₂ => .inr (.rorI2 d₂)
      | .inl r₁, .inl r₂ => .inl (.or r₁ r₂)
  | .imp A' B', hX =>
      byDec (decI Ψ (.imp A' B'))
        (fun hI => .inl (.ups (List.mem_cons_of_mem _ (hR₀mem _ hX hI))))
        (fun hnI =>
          byDec (decClo Ψ A')
            (fun hcl =>
              match totalityW hsat decI hg hR₀mem reccall B' (sfR_imp hX).2 with
              | .inl r => .inl (.imp hcl r)
              | .inr d => .inr (.rimpII d hcl))
            (fun hncl => .inr (.rimpNII
              (reccall A' B' hX hncl
                (fun h => hnI (gbuInv9 hsat hX hg h))) hncl)))
  | .circ V, hX =>
      match totalityW hsat decI hg hR₀mem reccall V (sfR_circ hX) with
      | .inl r => .inl (.circ rfl r)
      | .inr d => .inr (.rcircI d hX)

/-! ## The induction -/

set_option maxHeartbeats 3200000 in
/-- **`searchW`** — the Gbu◯/FRJW dichotomy at cell level: TYPE-valued,
delivering derivations; no supply hypotheses. -/
def searchW {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    (decI : ∀ Ω C, Decidable (WEvalI D Ω C)) :
    ∀ p : Bool × List Form × Form, WSearchOk G D p := by
  have main : ∀ x : Nat × Nat × Nat, ∀ p : Bool × List Form × Form,
      wgC G p.1 p.2.1 p.2.2 = x → WSearchOk G D p := by
    refine wgLt_wf.fix (fun x ihW => ?_)
    · rintro ⟨reg, Ψ, C⟩ hx
      have IH : ∀ q : Bool × List Form × Form,
          WgLt (wgC G q.1 q.2.1 q.2.2) (wgC G reg Ψ C) →
          WSearchOk G D q :=
        fun q hq => ihW _ (hx ▸ hq) q rfl
      have IHW := IH
      cases reg
      · -- ==================== IRREGULAR ====================
        show (∀ X ∈ Ψ, X ∈ sfL G) → (C.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G) →
          C ∈ sfR G → WUnrefutedBelow G D Ψ C → GbuIC G Ψ C
        intro hΨ hΩc hC hnb
        have hne : ¬ WEvalI D Ψ C := hnb.1
        refine byDec (inferInstance : Decidable (C ∈ Ψ))
          (fun hax => .ax C (ctxEq_cons_self hax)) (fun hax => ?_)
        cases C with
        | atom a => exact absurd (evalI_axI_gHat hsat (hΩc rfl) rfl hC hax) hne
        | bot => exact absurd (evalI_axI_gHat hsat (hΩc rfl) rfl hC hax) hne
        | and C₁ C₂ =>
            obtain ⟨h₁, h₂⟩ := sfR_and hC
            have hg := hΩc rfl
            have d₁ := IH (false, Ψ, C₁)
              (wgKeep (fun _ h => .base h) (seqSize_goal
                (Nat.lt_succ_of_le (Nat.le_add_right _ _))))

              hΨ (fun _ => hg) h₁ (unrefutedBelow_of_gHat hg
                (fun h => hne (gbuInv7 hsat hC (Or.inl h))))
            have d₂ := IH (false, Ψ, C₂)
              (wgKeep (fun _ h => .base h) (seqSize_goal
                (Nat.lt_succ_of_le (Nat.le_add_left _ _))))

              hΨ (fun _ => hg) h₂ (unrefutedBelow_of_gHat hg
                (fun h => hne (gbuInv7 hsat hC (Or.inr h))))
            exact .randI d₁ d₂
        | or C₁ C₂ =>
            obtain ⟨h₁, h₂⟩ := sfR_or hC
            have hg := hΩc rfl
            refine byDec (decI Ψ C₁) (fun he₁ => ?_) (fun he₁ => ?_)
            · refine byDec (decI Ψ C₂) (fun he₂ => ?_) (fun he₂ => ?_)
              · exact absurd (gbuInv10 hsat hC he₁ he₂) hne
              · have d := IH (false, Ψ, C₂)
                  (wgKeep (fun _ h => .base h) (seqSize_goal
                    (Nat.lt_succ_of_le (Nat.le_add_left _ _))))

                  hΨ (fun _ => hg) h₂ (unrefutedBelow_of_gHat hg he₂)
                exact .rorI2 d
            · have d := IH (false, Ψ, C₁)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (Nat.lt_succ_of_le (Nat.le_add_right _ _))))

                hΨ (fun _ => hg) h₁ (unrefutedBelow_of_gHat hg he₁)
              exact .rorI1 d
        | imp A B =>
            obtain ⟨hA, hB⟩ := sfR_imp hC
            have hg := hΩc rfl
            refine byDec (decClo Ψ A) (fun hcl => ?_) (fun hcl => ?_)
            · have d := IH (false, Ψ, B)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (Nat.lt_succ_of_le (Nat.le_add_left _ _))))

                hΨ (fun _ => hg) hB (unrefutedBelow_of_gHat hg
                  (fun h => hne (gbuInv8 hsat hC hcl h)))
              exact .rimpII d hcl
            · have d := IHW (true, A :: Ψ, B)
                (wgDrop (unclosed_lt hA hcl))
                (by
                  intro Y hY
                  rcases List.mem_cons.mp hY with rfl | hY'
                  · exact hA
                  · exact hΨ Y hY')
                hB (fun h => hne (gbuInv9 hsat hC hg h))
              exact .rimpNII d hcl
        | circ Z =>
            have hZsf : Z ∈ sfR G := sfR_circ hC
            rcases findNotT
              (fun X => (inferInstance : Decidable (X ∈ gHat G))) Ψ with
              hg | ⟨X, hXΨ, hXn⟩
            · rcases findNotT
                (fun X => (inferInstance : Decidable (X.isCirc = false))) Ψ with
                hnoc | ⟨Y, hYΨ, hYc⟩
              · -- the CRITICAL modal cell: `Ψ ⊆ Ĝ_at ∪ Ĝ_imp`
                have hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G := by
                  intro W hW
                  rcases gHat_cases (hg W hW) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hc⟩
                  · exact List.mem_append_left _ h
                  · exact List.mem_append_right _ h
                  · exact absurd hc (by simpa using hnoc W hW)
                refine byDec (decI Ψ Z) (fun heZ => ?_) (fun heZ => ?_)
                · -- `Z` refuted at `Ψ`: manufacture the `◯Z`-row
                  rcases findCMT G Ψ Z with ⟨ats, hsub, hFf, hall⟩ | hnocm
                  · exact absurd (wEvalI_axIC hsat hsub hFf hC hg hall) hne
                  set R₀ : List Form := (sfR G).filter
                    (fun A => @decide (WEvalI D Ψ A) (decI Ψ A)) with hR₀def
                  have hR₀ok : ∀ A ∈ R₀, WEvalI D Ψ A := by
                    intro A hA
                    exact of_decide_eq_true (List.mem_filter.mp hA).2
                  rcases findNotT (P := fun Y' => ante Y' ∈ R₀ ∨
                      RefAt true (Z :: R₀) Ψ (ante Y'))
                      (fun Y' => inferInstance) (impPart Ψ) with
                    hallK | ⟨Y₂, hY₂, hnK⟩
                  · refine absurd (gbuInvLift hsat hg
                      (wEvalR_of_refutedCleanly hsat
                        (refutedCleanly_circ_certs hsat hΩai hC heZ
                          hR₀ok ?_))) hne
                    intro A B hAB
                    exact hallK (.imp A B) (List.mem_filter.mpr ⟨hAB, rfl⟩)
                  · -- TOTALITY closes the corner: the failing
                    -- antecedent is unrefuted (else `.ups` would have
                    -- discharged the test), so it is DERIVABLE by the
                    -- structural totality, and `L⊃ᵢ` steps through it
                    have hY₂i : Y₂.isImp = true :=
                      (List.mem_filter.mp hY₂).2
                    have hY₂Ψ : Y₂ ∈ Ψ := (List.mem_filter.mp hY₂).1
                    match Y₂, hY₂i, hY₂Ψ, hnK with
                    | .imp A₂ B₂, _, hY₂Ψ, hnK =>
                        obtain ⟨hA₂sf, hB₂sf⟩ := sfL_imp (hΨ _ hY₂Ψ)
                        rcases totalityW hsat decI hg
                          (fun X hXsf hI => List.mem_filter.mpr
                            ⟨hXsf, @decide_eq_true _ (decI Ψ X) hI⟩)
                          (fun A' B' hXsf hncl hnR =>
                            IHW (true, A' :: Ψ, B')
                              (wgDrop
                                (unclosed_lt (sfR_imp hXsf).1 hncl))
                              (by
                                intro W hW
                                rcases List.mem_cons.mp hW with rfl | hW'
                                · exact (sfR_imp hXsf).1
                                · exact hΨ W hW')
                              (sfR_imp hXsf).2 hnR)
                          A₂ hA₂sf with hRef | hDer
                        · exact absurd hRef (fun h => hnK (Or.inr h))
                        · -- `L⊃ᵢ` through `Y₂`
                          obtain ⟨l₂, r₂, hsplit₂⟩ := splitOfMem hY₂Ψ
                          have hΓ₂ : Ψ ≐ .imp A₂ B₂ :: (l₂ ++ r₂) := by
                            rw [hsplit₂]; exact ctxEq_split
                          have hclB₂ : ∀ W ∈ Ψ,
                              Clo (B₂ :: (l₂ ++ r₂)) W := by
                            intro W hW
                            rcases List.mem_cons.mp ((hΓ₂ W).mp hW) with
                              rfl | hW'
                            · exact .imp (.base List.mem_cons_self)
                            · exact .base (List.mem_cons_of_mem _ hW')
                          have hmemsub₂ : ∀ W ∈ l₂ ++ r₂, W ∈ Ψ :=
                            fun W hW =>
                              (hΓ₂ W).mpr (List.mem_cons_of_mem _ hW)
                          have d₂ := IH (false, B₂ :: (l₂ ++ r₂),
                              Form.circ Z)
                            (by
                              refine wgKeep hclB₂ ?_
                              show seqSize (B₂ :: (l₂ ++ r₂))
                                  (Form.circ Z)
                                < seqSize Ψ (Form.circ Z)
                              rw [hsplit₂, seqSize_split, seqSize_cons]
                              have hb : B₂.size <
                                  (Form.imp A₂ B₂).size :=
                                Nat.lt_succ_of_le (Nat.le_add_left _ _)
                              omega)

                            (by
                              intro W hW
                              rcases List.mem_cons.mp hW with rfl | hW'
                              · exact hB₂sf
                              · exact hΨ W (hmemsub₂ W hW'))
                             (fun h => Bool.noConfusion h) hC
                            (unrefutedBelow_step hsat hclB₂ hnb)
                          exact .limpLI (FRJ.Gbu.LJFT.transportIC hDer hΓ₂) d₂
                            (Or.inr hA₂sf) hC hΓ₂
                · -- `Z` unrefuted: `R◯ᵢ`
                  have d := IH (false, Ψ, Z)
                    (wgKeep (fun _ h => .base h)
                      (seqSize_goal (Nat.lt_succ_self _)))

                    hΨ (fun _ => hg) hZsf (unrefutedBelow_of_gHat hg heZ)
                  exact .rcircI d hC
              · -- a modal member: `L◯ᵢ`
                have hYc' : Y.isCirc = true := by
                  cases hb : Y.isCirc with
                  | true => rfl
                  | false => exact absurd hb hYc
                match Y, hYc' with
                | .circ Y', _ =>
                    obtain ⟨lY, rY, hYsplit⟩ := splitOfMem hYΨ
                    have hΓ : Ψ ≐ .circ Y' :: (lY ++ rY) := by
                      rw [hYsplit]; exact ctxEq_split
                    have hmemsub : ∀ V ∈ lY ++ rY, V ∈ Ψ :=
                      fun V hV => (hΓ V).mpr (List.mem_cons_of_mem _ hV)
                    have hY'sf : Y' ∈ sfL G := sfL_circ (hΨ _ hYΨ)
                    have hcov : ∀ V ∈ Ψ, Clo (Y' :: (lY ++ rY)) V := by
                      intro V hV
                      rcases List.mem_cons.mp ((hΓ V).mp hV) with rfl | hV'
                      · exact .circ (.base List.mem_cons_self)
                      · exact .base (List.mem_cons_of_mem _ hV')
                    have d := IH (false, Y' :: (lY ++ rY), Form.circ Z)
                      (by
                        refine wgKeep hcov ?_
                        show seqSize (Y' :: (lY ++ rY)) (Form.circ Z)
                          < seqSize Ψ (Form.circ Z)
                        rw [hYsplit, seqSize_split, seqSize_cons]
                        have : Y'.size < (Form.circ Y').size := Nat.lt_succ_self _
                        omega)

                      (by
                        intro V hV
                        rcases List.mem_cons.mp hV with rfl | hV'
                        · exact hY'sf
                        · exact hΨ V (hmemsub V hV'))
                       (fun h => Bool.noConfusion h) hC
                      (unrefutedBelow_step hsat hcov hnb)
                    exact .lcircI d (hΨ _ hYΨ) hΓ
            · -- a NON-`Ĝ` member: `⊥`, `∧` or `∨`
              obtain ⟨lX, rX, hXsplit⟩ := splitOfMem hXΨ
              have hΓ : Ψ ≐ X :: (lX ++ rX) := by
                rw [hXsplit]; exact ctxEq_split
              have hmemsub : ∀ V ∈ lX ++ rX, V ∈ Ψ :=
                fun V hV => (hΓ V).mpr (List.mem_cons_of_mem _ hV)
              cases X with
              | atom a =>
                  exact absurd (mem_gHat_of_isHat (hΨ _ hXΨ) rfl) hXn
              | imp A B =>
                  exact absurd (mem_gHat_of_isHat (hΨ _ hXΨ) rfl) hXn
              | circ Y =>
                  exact absurd (mem_gHat_of_isHat (hΨ _ hXΨ) rfl) hXn
              | bot => exact .lbotI hC hΓ
              | and A B =>
                  obtain ⟨hA, hB⟩ := sfL_and (hΨ _ hXΨ)
                  have hcov : ∀ V ∈ Ψ, Clo (A :: B :: (lX ++ rX)) V := by
                    intro V hV
                    rcases List.mem_cons.mp ((hΓ V).mp hV) with rfl | hV'
                    · exact .and (.base List.mem_cons_self)
                        (.base (List.mem_cons_of_mem _ List.mem_cons_self))
                    · exact .base (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hV'))
                  have d := IH (false, A :: B :: (lX ++ rX), Form.circ Z)
                    (by
                      refine wgKeep hcov ?_
                      show seqSize (A :: B :: (lX ++ rX)) (Form.circ Z)
                        < seqSize Ψ (Form.circ Z)
                      rw [hXsplit, seqSize_split, seqSize_cons, seqSize_cons]
                      show A.size + (B.size + seqSize (lX ++ rX) (Form.circ Z))
                        < seqSize (lX ++ rX) (Form.circ Z) + (A.size + B.size + 1)
                      omega)

                    (by
                      intro V hV
                      rcases List.mem_cons.mp hV with rfl | hV'
                      · exact hA
                      · rcases List.mem_cons.mp hV' with rfl | hV''
                        · exact hB
                        · exact hΨ V (hmemsub V hV''))
                     (fun h => Bool.noConfusion h) hC
                    (unrefutedBelow_step hsat hcov hnb)
                  exact .landLI d hC hΓ
              | or A B =>
                  obtain ⟨hA, hB⟩ := sfL_or (hΨ _ hXΨ)
                  have hszo : ∀ Y : Form, Y.size < (Form.or A B).size →
                      seqSize (Y :: (lX ++ rX)) (Form.circ Z)
                        < seqSize Ψ (Form.circ Z) := by
                    intro Y hY
                    rw [hXsplit, seqSize_split, seqSize_cons]
                    omega
                  have hcovL : ∀ V ∈ Ψ, Clo (A :: (lX ++ rX)) V := by
                    intro V hV
                    rcases List.mem_cons.mp ((hΓ V).mp hV) with rfl | hV'
                    · exact .orL (.base List.mem_cons_self)
                    · exact .base (List.mem_cons_of_mem _ hV')
                  have hcovR : ∀ V ∈ Ψ, Clo (B :: (lX ++ rX)) V := by
                    intro V hV
                    rcases List.mem_cons.mp ((hΓ V).mp hV) with rfl | hV'
                    · exact .orR (.base List.mem_cons_self)
                    · exact .base (List.mem_cons_of_mem _ hV')
                  have d₁ := IH (false, A :: (lX ++ rX), Form.circ Z)
                    (wgKeep hcovL (hszo A (Nat.lt_succ_of_le (Nat.le_add_right _ _))))

                    (by
                      intro V hV
                      rcases List.mem_cons.mp hV with rfl | hV'
                      · exact hA
                      · exact hΨ V (hmemsub V hV'))
                     (fun h => Bool.noConfusion h) hC
                    (unrefutedBelow_step hsat hcovL hnb)
                  have d₂ := IH (false, B :: (lX ++ rX), Form.circ Z)
                    (wgKeep hcovR (hszo B (Nat.lt_succ_of_le (Nat.le_add_left _ _))))

                    (by
                      intro V hV
                      rcases List.mem_cons.mp hV with rfl | hV'
                      · exact hB
                      · exact hΨ V (hmemsub V hV'))
                     (fun h => Bool.noConfusion h) hC
                    (unrefutedBelow_step hsat hcovR hnb)
                  exact .lorLI d₁ d₂ hC hΓ
      · -- ==================== REGULAR: `Ψ ⇒g C` ====================
        show (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G → ¬ WEvalR D Ψ C →
          GbuRC G Ψ C
        intro hΨ hC hne
        refine byDec (inferInstance : Decidable (C ∈ Ψ))
          (fun hax => .ax C (ctxEq_cons_self hax)) (fun hax => ?_)
        rcases splitHatT Ψ with hall | ⟨l, r, X, hsplit, hX⟩
        · -- critical: `Ψ ⊆ Ĝ`
          have hΩ : ∀ Y ∈ Ψ, Y ∈ gHat G :=
            fun Y hY => mem_gHat_of_isHat (hΨ Y hY) (hall Y hY)
          have limpStep : ∀ A B : Form, Form.imp A B ∈ Ψ → ¬ WEvalI D Ψ A →
              GbuRC G Ψ C := by
            intro A B hYΨ hnA
            obtain ⟨lY, rY, hYsplit⟩ := splitOfMem hYΨ
            obtain ⟨hAsf, hBsf⟩ := sfL_imp (hΨ _ hYΨ)
            have hΓ : Ψ ≐ .imp A B :: (lY ++ rY) := by
              rw [hYsplit]; exact ctxEq_split
            have hmemsub : ∀ W ∈ lY ++ rY, W ∈ Ψ :=
              fun W hW => (hΓ W).mpr (List.mem_cons_of_mem _ hW)
            have d₁ := IH (false, .imp A B :: (lY ++ rY), A)
              (wgFocus (fun W hW => .base ((hΓ W).mp hW)))

              (by
                intro W hW
                rcases List.mem_cons.mp hW with rfl | hW'
                · exact hΨ _ hYΨ
                · exact hΨ W (hmemsub W hW'))
              (by
                intro _ W hW
                rcases List.mem_cons.mp hW with rfl | hW'
                · exact hΩ _ hYΨ
                · exact hΩ W (hmemsub W hW'))
              hAsf (unrefutedBelow_of_gHat
                (by
                  intro W hW
                  rcases List.mem_cons.mp hW with rfl | hW'
                  · exact hΩ _ hYΨ
                  · exact hΩ W (hmemsub W hW'))
                (fun h => hnA (wEvalI_ctxEq (ctxEq_symm hΓ) h)))
            have d₂ := IH (true, B :: (lY ++ rY), C)
              (by
                refine wgKeep (fun W hW => ?_) ?_
                · rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                  · exact .imp (.base List.mem_cons_self)
                  · exact .base (List.mem_cons_of_mem _ hW')
                · show seqSize (B :: (lY ++ rY)) C < seqSize Ψ C
                  rw [hYsplit, seqSize_split, seqSize_cons]
                  have hb : B.size < (Form.imp A B).size :=
                    Nat.lt_succ_of_le (Nat.le_add_left _ _)
                  omega)

              (by
                intro W hW
                rcases List.mem_cons.mp hW with rfl | hW'
                · exact hBsf
                · exact hΨ W (hmemsub W hW'))
              hC (fun h => hne (wEvalR_ctxEq (ctxEq_symm hΓ) (gbuInv4 h)))
            exact .limpL d₁ d₂ hΓ
          have fromImp : ∀ Y : Form, Y ∈ impPart Ψ →
              ¬ WEvalI D Ψ (ante Y) → GbuRC G Ψ C := by
            intro Y hY hnY
            have hYi : Y.isImp = true := (List.mem_filter.mp hY).2
            have hYΨ : Y ∈ Ψ := (List.mem_filter.mp hY).1
            match Y, hYi, hYΨ, hnY with
            | .imp A B, _, hYΨ, hnY => exact limpStep A B hYΨ hnY
          have upsToImp : (∀ Y ∈ impPart Ψ, WEvalI D Ψ (ante Y)) →
              ∀ A B : Form, Form.imp A B ∈ Ψ → WEvalI D Ψ A := by
            intro hallI A B hAB
            exact hallI (.imp A B) (List.mem_filter.mpr ⟨hAB, rfl⟩)
          cases C with
          | atom a =>
              rcases findNotT (fun Y => decI Ψ (ante Y)) (impPart Ψ) with
                hallI | ⟨Y, hY, hnY⟩
              · exact absurd (gbuSuccAtF hsat hΩ rfl hC hax (upsToImp hallI)) hne
              · exact fromImp Y hY hnY
          | bot =>
              rcases findNotT (fun Y => decI Ψ (ante Y)) (impPart Ψ) with
                hallI | ⟨Y, hY, hnY⟩
              · exact absurd (gbuSuccAtF hsat hΩ rfl hC hax (upsToImp hallI)) hne
              · exact fromImp Y hY hnY
          | and C₁ C₂ =>
              obtain ⟨h₁, h₂⟩ := sfR_and hC
              have d₁ := IH (true, Ψ, C₁)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (Nat.lt_succ_of_le (Nat.le_add_right _ _))))

                hΨ h₁ (fun h => hne (gbuInv2 hsat hC (Or.inl h)))
              have d₂ := IH (true, Ψ, C₂)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (Nat.lt_succ_of_le (Nat.le_add_left _ _))))

                hΨ h₂ (fun h => hne (gbuInv2 hsat hC (Or.inr h)))
              exact .randR d₁ d₂
          | imp A B =>
              obtain ⟨hA, hB⟩ := sfR_imp hC
              refine byDec (decClo Ψ A) (fun hcl => ?_) (fun hcl => ?_)
              · have d := IH (true, Ψ, B)
                  (wgKeep (fun _ h => .base h) (seqSize_goal
                    (Nat.lt_succ_of_le (Nat.le_add_left _ _))))

                  hΨ hB (fun h => hne (gbuInv5 hsat hC hcl h))
                exact .rimpI d hcl
              · have d := IH (true, A :: Ψ, B) (wgDrop (unclosed_lt hA hcl))

                  (by
                    intro Y hY
                    rcases List.mem_cons.mp hY with rfl | hY'
                    · exact hA
                    · exact hΨ Y hY')
                  hB (fun h => hne (gbuInv6 hsat hC h))
                exact .rimpNI d hcl
          | or C₁ C₂ =>
              obtain ⟨h₁, h₂⟩ := sfR_or hC
              refine byDec (decI Ψ C₁) (fun he₁ => ?_) (fun he₁ => ?_)
              · refine byDec (decI Ψ C₂) (fun he₂ => ?_) (fun he₂ => ?_)
                · rcases findNotT (fun Y => decI Ψ (ante Y)) (impPart Ψ) with
                    hallI | ⟨Y, hY, hnY⟩
                  · exact absurd (gbuSuccOrF hsat hΩ hC (upsToImp hallI) he₁ he₂) hne
                  · exact fromImp Y hY hnY
                · have d := IH (false, Ψ, C₂)
                    (wgFocus (fun _ h => .base h))

                    hΨ (fun _ => hΩ) h₂ (unrefutedBelow_of_gHat hΩ he₂)
                  exact .rorR2 d
              · have d := IH (false, Ψ, C₁)
                  (wgFocus (fun _ h => .base h))

                  hΨ (fun _ => hΩ) h₁ (unrefutedBelow_of_gHat hΩ he₁)
                exact .rorR1 d
          | circ Z =>
              rcases findNotT
                (fun X => (inferInstance : Decidable (X.isCirc = false))) Ψ with
                hnoc | ⟨Y, hYΨ, hYc⟩
              · have hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G := by
                  intro W hW
                  rcases gHat_cases (hΩ W hW) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hc⟩
                  · exact List.mem_append_left _ h
                  · exact List.mem_append_right _ h
                  · exact absurd hc (by simpa using hnoc W hW)
                refine byDec (decI Ψ Z) (fun heZ => ?_) (fun heZ => ?_)
                · rcases findNotT (fun Y => decI Ψ (ante Y)) (impPart Ψ) with
                    hallI | ⟨Y, hY, hnY⟩
                  · exact absurd (gbuSuccCirc hsat hΩai hC (upsToImp hallI) heZ) hne
                  · exact fromImp Y hY hnY
                · have d := IH (false, Ψ, Z)
                    (wgFocus (fun _ h => .base h))

                    hΨ (fun _ => hΩ) (sfR_circ hC)
                    (unrefutedBelow_of_gHat hΩ heZ)
                  exact .rcirc d hC
              · have hYc' : Y.isCirc = true := by
                  cases hb : Y.isCirc with
                  | true => rfl
                  | false => exact absurd hb hYc
                match Y, hYc' with
                | .circ Y', _ =>
                    obtain ⟨lY, rY, hYsplit⟩ := splitOfMem hYΨ
                    have hΓ : Ψ ≐ .circ Y' :: (lY ++ rY) := by
                      rw [hYsplit]; exact ctxEq_split
                    have hmemsub : ∀ W ∈ lY ++ rY, W ∈ Ψ :=
                      fun W hW => (hΓ W).mpr (List.mem_cons_of_mem _ hW)
                    have hY'sf : Y' ∈ sfL G := sfL_circ (hΨ _ hYΨ)
                    have d := IH (true, Y' :: (lY ++ rY), Form.circ Z)
                      (by
                        refine wgKeep (fun W hW => ?_) ?_
                        · rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                          · exact .circ (.base List.mem_cons_self)
                          · exact .base (List.mem_cons_of_mem _ hW')
                        · show seqSize (Y' :: (lY ++ rY)) (Form.circ Z) < seqSize Ψ _
                          rw [hYsplit, seqSize_split, seqSize_cons]
                          have : Y'.size < (Form.circ Y').size := Nat.lt_succ_self _
                          omega)

                      (by
                        intro W hW
                        rcases List.mem_cons.mp hW with rfl | hW'
                        · exact hY'sf
                        · exact hΨ W (hmemsub W hW'))
                      hC (fun h => hne (wEvalR_ctxEq (ctxEq_symm hΓ) (gbuInv11 h)))
                    exact .lcirc d (hΨ _ hYΨ) hΓ
        · -- non-critical: an invertible LEFT rule
          subst hsplit
          have hXmem : X ∈ l ++ X :: r := List.mem_append_right _ List.mem_cons_self
          have hΓ : (l ++ X :: r) ≐ X :: (l ++ r) := ctxEq_split
          have hmemsub : ∀ W ∈ l ++ r, W ∈ l ++ X :: r :=
            fun W hW => (hΓ W).mpr (List.mem_cons_of_mem _ hW)
          cases X with
          | atom a => exact Bool.noConfusion hX
          | imp A B => exact Bool.noConfusion hX
          | circ Z => exact Bool.noConfusion hX
          | bot => exact .lbot C (ctxEq_cons_self hXmem)
          | and A B =>
              obtain ⟨hA, hB⟩ := sfL_and (hΨ _ hXmem)
              have d := IH (true, A :: B :: (l ++ r), C)
                (by
                  refine wgKeep (fun W hW => ?_) ?_
                  · rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                    · exact .and (.base List.mem_cons_self)
                        (.base (List.mem_cons_of_mem _ List.mem_cons_self))
                    · exact .base (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hW'))
                  · rw [seqSize_split, seqSize_cons, seqSize_cons]
                    show A.size + (B.size + seqSize (l ++ r) C)
                      < seqSize (l ++ r) C + (A.size + B.size + 1)
                    omega)

                (by
                  intro W hW
                  rcases List.mem_cons.mp hW with rfl | hW'
                  · exact hA
                  · rcases List.mem_cons.mp hW' with rfl | hW''
                    · exact hB
                    · exact hΨ W (hmemsub W hW''))
                hC (fun h => hne (wEvalR_ctxEq (ctxEq_symm hΓ) (gbuInv1 h)))
              exact .landL d hΓ
          | or A B =>
              obtain ⟨hA, hB⟩ := sfL_or (hΨ _ hXmem)
              have hsz : ∀ Y : Form, Y.size < (Form.or A B).size →
                  seqSize (Y :: (l ++ r)) C < seqSize (l ++ Form.or A B :: r) C := by
                intro Y hY
                rw [seqSize_split, seqSize_cons]
                omega
              have d₁ := IH (true, A :: (l ++ r), C)
                (wgKeep (fun W hW => by
                    rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                    · exact .orL (.base List.mem_cons_self)
                    · exact .base (List.mem_cons_of_mem _ hW'))
                  (hsz A (Nat.lt_succ_of_le (Nat.le_add_right _ _))))

                (by
                  intro W hW
                  rcases List.mem_cons.mp hW with rfl | hW'
                  · exact hA
                  · exact hΨ W (hmemsub W hW'))
                hC (fun h => hne (wEvalR_ctxEq (ctxEq_symm hΓ) (gbuInv3L h)))
              have d₂ := IH (true, B :: (l ++ r), C)
                (wgKeep (fun W hW => by
                    rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                    · exact .orR (.base List.mem_cons_self)
                    · exact .base (List.mem_cons_of_mem _ hW'))
                  (hsz B (Nat.lt_succ_of_le (Nat.le_add_left _ _))))

                (by
                  intro W hW
                  rcases List.mem_cons.mp hW with rfl | hW'
                  · exact hB
                  · exact hΨ W (hmemsub W hW'))
                hC (fun h => hne (wEvalR_ctxEq (ctxEq_symm hΓ) (gbuInv3R h)))
              exact .lorL d₁ d₂ hΓ
  exact fun p => main _ p rfl

/-! ## The root dichotomy

`searchW` at the root cell, with the regular root query decided:
either `G` has an FRJW disproof, or `Gbu◯(G)` derives `G` — and the
positive side carries the DERIVATION.  Together with the exclusion
corollary (`wip/gbu_frjw_exclusion.lean`, both directions), this is
the cell-level form of `Γ ⊢_Gbu◯ φ ⇔ Γ ⊬_FRJW φ` over any saturated
database.  What remains for `decideGbuW` proper is the CONCRETE
instantiation: a saturated database for each `G` with its deciders —
the engine-fixpoint obligation, a separate stage. -/
def dichotomyW {G : Form} {D : WSeq → Prop} (hsat : WSaturated G D)
    (decI : ∀ Ω C, Decidable (WEvalI D Ω C))
    (decR : Decidable (WEvalR D [] G)) :
    DisprovableW G ⊕' GbuRC G [] G :=
  byDec decR
    (fun h => .inl (by
      obtain ⟨t, Γ, hmem, -⟩ := h
      obtain ⟨d⟩ := hsat.1 _ hmem
      exact ⟨t, Γ, ⟨d⟩⟩))
    (fun hn =>
      .inr (searchW hsat decI (true, [], G)
        (fun _ h => absurd h List.not_mem_nil) (sfR_self G) hn))

/-! ## Pins -/

/-- info: 'FRJ.Gbu.W.searchW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms searchW

/-- info: 'FRJ.Gbu.W.dichotomyW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dichotomyW

end FRJ.Gbu.W
