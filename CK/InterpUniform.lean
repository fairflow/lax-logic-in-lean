/-
# Theorem 4 (iii): uniformity of `Ep` and `Ap`

Source: I. van der Giessen and I. Shillito, "Uniform interpolation with
constructive diamond", arXiv:2602.16880, §4: Lemma 3 (`Lemma_simple1`),
Lemma 4 (`Lemma_simple2`) and Theorem 4 (`thm:UIP_CK`), the uniformity
property.  Rocq: `theories/Sequent/G4CK/CKPropQuantifiers.v` of
github.com/ianshil/CK, `EA_cong`, `E_left`, `E9_left`, `E12_left`,
`A_right`, `Af_right`, `A16_right`, `A17_right`, `pq_correct`.

    if no member of Γ contains p and Γ, Δ ⇒ ϕ, then
      Γ, Ep(Δ) ⇒ ϕ           provided ϕ does not contain p, and
      Γ, Ep(Δ) ⇒ Ap(Δ ⇒ ϕ).

As in the Rocq proof, the induction is on the measure of the sequent
`Γ, Δ ⇒ ϕ`, by cases on the last rule of its derivation and on the side, `Γ`
or `Δ`, of each principal formula.
-/
import CK.InterpEntail

namespace CK

open Form

/-! ## `Ep` does not depend on the succedent (Rocq `EA_cong`) -/

/-- Rocq `EA_cong`, by induction on the measure. -/
theorem EA_cong_aux (p : Nat) : ∀ (n : Nat) (Δ : List Form), pw Δ ⊥' < n →
    ∀ ϕ ψ : Form, EA p true Δ ϕ = EA p true Δ ψ
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, Δ, hn => by
      intro ϕ ψ
      have IH : ∀ X, pw X ⊥' < pw Δ ⊥' → ∀ ϕ ψ : Form, EA p true X ϕ = EA p true X ψ :=
        fun X h => EA_cong_aux p n X (by omega)
      rw [EA_true, EA_true]
      refine congrArg conj (congr (congrArg HAppend.hAppend (congr (congrArg List.cons ?_) ?_)) ?_)
      · unfold eRow9
        split
        · rfl
        · rename_i h
          exact congrArg Form.box (IH _ (pw_unbox_lt _ h) _ _)
      · refine List.map_congr_left fun θ hθ => ?_
        rcases θ with _|_|_|_|⟨(_|_|_|_|_|_|_),_⟩|_|_ <;> simp only [eRow] <;>
          repeat' first
            | rfl
            | (refine IH _ ?_ _ _; ea_dec)
            | congr 1
      · rw [List.flatMap_def, List.flatMap_def]
        refine congrArg List.flatten (List.map_congr_left fun θ₁ h₁ => ?_)
        refine List.map_congr_left fun θ₂ h₂ => ?_
        rcases θ₁ with _|_|_|_|⟨(_|_|_|_|_|_|_),_⟩|_|_ <;> rcases θ₂ with _|_|_|_|_|_|_ <;>
          simp only [eRow12] <;>
          repeat' first
            | rfl
            | (refine IH _ ?_ _ _; ea_dec)
            | congr 1

/-- `Ep` as a function of a pointed environment that ignores the point. -/
def Ee (p : Nat) (X : List Form) (_ : Form) : Form := Ep p X

/-- Rocq `EA_cong`. -/
theorem EA_true_eq (p : Nat) : EA p true = Ee p :=
  funext fun X => funext fun ϕ => EA_cong_aux p _ X (Nat.lt_succ_self _) ϕ ⊥'

theorem EA_false_eq (p : Nat) : EA p false = Ap p := rfl

/-! ## Lemma 3: a row of `Ep` on the left, a row of `Ap` on the right -/

namespace G4CK

variable {Γ : List Form} {φ ψ : Form}

/-- Rocq `list_conjL`. -/
theorem conjL : ∀ {l : List Form}, φ ∈ l → G4CK (φ :: Γ) ψ → G4CK (conj l :: Γ) ψ
  | a :: l, h, d => by
      refine .andL (List.Perm.refl _) ?_
      by_cases e : φ = a
      · subst e; exact .wk1 d
      · have h' : φ ∈ l := by
          rcases List.mem_cons.1 h with rfl | h'
          · exact absurd rfl e
          · exact h'
        exact .wk (conjL h' d)

/-- Rocq `list_disjR`. -/
theorem disjR : ∀ {l : List Form}, φ ∈ l → G4CK Γ φ → G4CK Γ (disj l)
  | a :: l, h, d => by
      by_cases e : φ = a
      · subst e; exact .orR1 d
      · have h' : φ ∈ l := by
          rcases List.mem_cons.1 h with rfl | h'
          · exact absurd rfl e
          · exact h'
        exact .orR2 (disjR h' d)

end G4CK

section
variable {p : Nat} {Γ Δ : List Form} {χ ϕ θ θ₁ θ₂ : Form}

theorem Ep_unfold (p : Nat) (Δ : List Form) : Ep p Δ =
    conj (eRow9 (Ee p) Δ ⊥'
      :: Δ.map (eRow p (Ee p) (Ap p) Δ ⊥')
      ++ Δ.flatMap (fun θ₁ => Δ.map (eRow12 (Ee p) (Ap p) Δ ⊥' θ₁))) := by
  show EA p true Δ ⊥' = _
  rw [EA_true, EA_true_eq, EA_false_eq]

theorem Ap_unfold (p : Nat) (Δ : List Form) (ϕ : Form) : Ap p Δ ϕ =
    disj (aForm p (Ee p) (Ap p) Δ ϕ
      :: Δ.map (aEnv p (Ee p) (Ap p) Δ ϕ)
      ++ Δ.map (aRow16 (Ee p) (Ap p) Δ ϕ)
      ++ Δ.flatMap (fun θ₁ => Δ.map (aRow17 (Ee p) (Ap p) Δ ϕ θ₁))) := by
  show EA p false Δ ϕ = _
  rw [EA_false, EA_true_eq, EA_false_eq]

/-- **Lemma 3**, left part.  Rocq `E_left`. -/
theorem E_left (hθ : θ ∈ Δ) (d : G4CK (eRow p (Ee p) (Ap p) Δ ⊥' θ :: Γ) χ) :
    G4CK (Ep p Δ :: Γ) χ := by
  rw [Ep_unfold]
  exact G4CK.conjL (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hθ))) d

/-- Rocq `E9_left`. -/
theorem E9_left (d : G4CK (eRow9 (Ee p) Δ ⊥' :: Γ) χ) : G4CK (Ep p Δ :: Γ) χ := by
  rw [Ep_unfold]
  exact G4CK.conjL (List.mem_append_left _ List.mem_cons_self) d

/-- Rocq `E12_left`. -/
theorem E12_left (h₁ : θ₁ ∈ Δ) (h₂ : θ₂ ∈ Δ)
    (d : G4CK (eRow12 (Ee p) (Ap p) Δ ⊥' θ₁ θ₂ :: Γ) χ) : G4CK (Ep p Δ :: Γ) χ := by
  rw [Ep_unfold]
  exact G4CK.conjL (List.mem_append_right _
    (List.mem_flatMap.2 ⟨θ₁, h₁, List.mem_map_of_mem h₂⟩)) d

/-- **Lemma 3**, right part, for the rows that read the succedent.  Rocq
`Af_right`. -/
theorem Af_right (d : G4CK Γ (aForm p (Ee p) (Ap p) Δ ϕ)) : G4CK Γ (Ap p Δ ϕ) := by
  rw [Ap_unfold]
  exact G4CK.disjR (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)) d

/-- **Lemma 3**, right part.  Rocq `A_right`. -/
theorem A_right (hθ : θ ∈ Δ) (d : G4CK Γ (aEnv p (Ee p) (Ap p) Δ ϕ θ)) : G4CK Γ (Ap p Δ ϕ) := by
  rw [Ap_unfold]
  exact G4CK.disjR (List.mem_append_left _ (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_map_of_mem hθ)))) d

/-- Rocq `A16_right`. -/
theorem A16_right (hθ : θ ∈ Δ) (d : G4CK Γ (aRow16 (Ee p) (Ap p) Δ ϕ θ)) :
    G4CK Γ (Ap p Δ ϕ) := by
  rw [Ap_unfold]
  exact G4CK.disjR (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hθ))) d

/-- Rocq `A17_right`. -/
theorem A17_right (h₁ : θ₁ ∈ Δ) (h₂ : θ₂ ∈ Δ)
    (d : G4CK Γ (aRow17 (Ee p) (Ap p) Δ ϕ θ₁ θ₂)) : G4CK Γ (Ap p Δ ϕ) := by
  rw [Ap_unfold]
  exact G4CK.disjR (List.mem_append_right _
    (List.mem_flatMap.2 ⟨θ₁, h₁, List.mem_map_of_mem h₂⟩)) d

/-! ## Lemma 4: `□Ep(□⁻¹Δ)` is available from `Ep(Δ)` -/

/-- The row (E9) may be added next to `Ep(Δ)`. -/
theorem E9_dup (d : G4CK (eRow9 (Ee p) Δ ⊥' :: Ep p Δ :: Γ) χ) : G4CK (Ep p Δ :: Γ) χ :=
  (E9_left d).contract (List.Perm.refl _)

/-- Under `□⁻¹`, the row (E9) next to `Ep(Δ)` yields `Ep(□⁻¹Δ)`.  For
`Δ = ∅` the row is `⊤` and `Ep(∅)` is derivable. -/
theorem e9_unbox (L : List Form) (d : G4CK (Ep p (unbox Δ) :: (L ++ unbox Γ)) χ) :
    G4CK (L ++ unbox (eRow9 (Ee p) Δ ⊥' :: Ep p Δ :: Γ)) χ := by
  unfold eRow9
  split
  · rename_i h
    subst h
    have e : G4CK (L ++ unbox Γ) (Ep p []) := by
      have := (Ep_entail p []).weakenList (L ++ unbox Γ)
      rwa [List.append_nil] at this
    exact G4CK.unboxWk L Form.top (G4CK.unboxWk L (Ep p []) (e.cut d))
  · exact (G4CK.unboxWk (Ep p (unbox Δ) :: L) (Ep p Δ) d).perm List.perm_middle.symm

/-- **Lemma 4** (`Lemma_simple2`) in the form used below:
`□⁻¹Γ, Ep(□⁻¹Δ) ⇒ φ` gives `Γ, Ep(Δ) ⇒ □φ`. -/
theorem Ep_boxR (d : G4CK (Ep p (unbox Δ) :: unbox Γ) χ) : G4CK (Ep p Δ :: Γ) (□χ) :=
  E9_dup (.boxR (e9_unbox [] d))

end

/-! ## Bookkeeping: permutations, the measure, formulas without `p` -/

section
variable {Θ Γ Γ' Δ Δ₀ R U L L' : List Form} {θ a b ϕ ψ' X Y : Form}

theorem perm_ins1 (h : Γ.Perm (θ :: Γ')) : (X :: Γ).Perm (θ :: X :: Γ') :=
  (h.cons X).trans (List.Perm.swap _ _ _)

theorem perm_ins2 (h : Γ.Perm (θ :: Γ')) : (X :: Y :: Γ).Perm (θ :: X :: Y :: Γ') :=
  ((perm_ins1 h).cons X).trans (List.Perm.swap _ _ _)

/-- `Θ ~ θ, Δ₀` and `Θ ~ Γ, Δ` with `Γ ~ θ, Γ'` give `Δ₀ ~ Γ', Δ`. -/
theorem restΓ (h : Θ.Perm (θ :: Δ₀)) (hp : Θ.Perm (Γ ++ Δ)) (hΓ : Γ.Perm (θ :: Γ')) :
    Δ₀.Perm (Γ' ++ Δ) :=
  ((h.symm.trans hp).trans (hΓ.append_right Δ)).cons_inv

/-- `Θ ~ θ, Δ₀` and `Θ ~ Γ, Δ` with `θ ∈ Δ` give `Δ₀ ~ Γ, rm θ Δ`. -/
theorem restΔ (h : Θ.Perm (θ :: Δ₀)) (hp : Θ.Perm (Γ ++ Δ)) (hθ : θ ∈ Δ) :
    Δ₀.Perm (Γ ++ rm θ Δ) :=
  ((h.symm.trans hp).trans (((perm_rm hθ).append_left Γ).trans List.perm_middle)).cons_inv

/-- New formulas `L` join the side `Γ`. -/
theorem splitΓ (L : List Form) (h : Δ₀.Perm (Γ' ++ Δ)) : (L ++ Δ₀).Perm ((L ++ Γ') ++ Δ) := by
  rw [List.append_assoc]; exact h.append_left L

/-- New formulas `L` join the side `Δ`. -/
theorem splitΔ (L : List Form) (h : Δ₀.Perm (Γ ++ R)) : (L ++ Δ₀).Perm (Γ ++ (L ++ R)) :=
  (h.append_left L).trans (perm_shuffle L Γ R)

theorem splitU (h : Δ₀.Perm (Γ ++ R)) : (unbox Δ₀).Perm (unbox Γ ++ unbox R) := by
  rw [← unbox_append]; exact unbox_perm h

theorem pwL (h : Θ.Perm (θ :: Δ₀)) (hU : wt U ≤ wt Δ₀) (hlen : L.length ≤ 4)
    (hL : ∀ x ∈ L.map Form.weight, x + 1 ≤ θ.weight) (hψ : ψ'.weight ≤ ϕ.weight) :
    pw (L ++ U) ψ' < pw Θ ϕ := by
  have hm : θ ∈ Θ := h.mem_iff.2 List.mem_cons_self
  refine pw_envLe hm ?_ hlen hL hψ
  have h₁ := wt_rm hm
  have h₂ : wt Θ = 5 ^ θ.weight + wt Δ₀ := wt_perm h
  omega

theorem pwN (h : Θ.Perm (θ :: Δ₀)) (hU : wt U ≤ wt Δ₀) (hlen : L.length ≤ 2)
    (hL : ∀ x ∈ ψ'.weight :: ψ'.weight :: L.map Form.weight, x + 1 ≤ θ.weight) :
    pw (L ++ U) ψ' < pw Θ ϕ := by
  have hm : θ ∈ Θ := h.mem_iff.2 List.mem_cons_self
  refine pw_envNew hm ?_ hlen hL
  have h₁ := wt_rm hm
  have h₂ : wt Θ = 5 ^ θ.weight + wt Δ₀ := wt_perm h
  omega

theorem pwL0 (h : Θ.Perm (θ :: Δ₀)) (hU : wt U ≤ wt Δ₀) (hψ : ψ'.weight ≤ ϕ.weight) :
    pw U ψ' < pw Θ ϕ := pwL (L := []) h hU (by decide) (fun _ hx => nomatch hx) hψ

theorem pwL1 (h : Θ.Perm (θ :: Δ₀)) (hU : wt U ≤ wt Δ₀)
    (hL : ∀ x ∈ [a].map Form.weight, x + 1 ≤ θ.weight) (hψ : ψ'.weight ≤ ϕ.weight) :
    pw (a :: U) ψ' < pw Θ ϕ := pwL (L := [a]) h hU (by show 1 ≤ 4; decide) hL hψ

theorem pwL2 (h : Θ.Perm (θ :: Δ₀)) (hU : wt U ≤ wt Δ₀)
    (hL : ∀ x ∈ [a, b].map Form.weight, x + 1 ≤ θ.weight) (hψ : ψ'.weight ≤ ϕ.weight) :
    pw (a :: b :: U) ψ' < pw Θ ϕ := pwL (L := [a, b]) h hU (by show 2 ≤ 4; decide) hL hψ

theorem pwN0 (h : Θ.Perm (θ :: Δ₀)) (hU : wt U ≤ wt Δ₀)
    (hL : ∀ x ∈ ψ'.weight :: ψ'.weight :: ([] : List Form).map Form.weight, x + 1 ≤ θ.weight) :
    pw U ψ' < pw Θ ϕ := pwN (L := []) h hU (by decide) hL

theorem pwN1 (h : Θ.Perm (θ :: Δ₀)) (hU : wt U ≤ wt Δ₀)
    (hL : ∀ x ∈ ψ'.weight :: ψ'.weight :: [a].map Form.weight, x + 1 ≤ θ.weight) :
    pw (a :: U) ψ' < pw Θ ϕ := pwN (L := [a]) h hU (by show 1 ≤ 2; decide) hL

theorem pwN2 (h : Θ.Perm (θ :: Δ₀)) (hU : wt U ≤ wt Δ₀)
    (hL : ∀ x ∈ ψ'.weight :: ψ'.weight :: [a, b].map Form.weight, x + 1 ≤ θ.weight) :
    pw (a :: b :: U) ψ' < pw Θ ϕ := pwN (L := [a, b]) h hU (by show 2 ≤ 2; decide) hL

/-- `□⁻¹Δ₀, χ` weighs no more than `Δ₀` when `◇χ ∈ Δ₀`. -/
theorem wt_dia_unbox_le {χ : Form} (h : (◇χ) ∈ Δ₀) : wt (χ :: unbox Δ₀) ≤ wt Δ₀ := by
  have h₁ := wt_rm h
  have h₂ : wt (unbox (rm (◇χ) Δ₀)) ≤ wt (rm (◇χ) Δ₀) := wt_unbox_le _
  rw [unbox_rm (by intro a e; cases e)] at h₂
  have h₃ : 5 ^ χ.weight ≤ 5 ^ (◇χ).weight := Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  show 5 ^ χ.weight + wt (unbox Δ₀) ≤ wt Δ₀
  omega

end

/-- Closes a bound on the measure for a premise of a left rule with
`h : Θ ~ θ, Δ₀`. -/
macro "pq_lt " h:term : tactic =>
  `(tactic| first
      | (refine pwL2 $h ?_ ?_ ?_ <;> first | exact Nat.le_refl _ | exact wt_unbox_le _ | ea_side)
      | (refine pwL1 $h ?_ ?_ ?_ <;> first | exact Nat.le_refl _ | exact wt_unbox_le _ | ea_side)
      | (refine pwN2 $h ?_ ?_ <;> first | exact Nat.le_refl _ | exact wt_unbox_le _ | ea_side)
      | (refine pwN1 $h ?_ ?_ <;> first | exact Nat.le_refl _ | exact wt_unbox_le _ | ea_side)
      | (refine pwL0 $h ?_ ?_ <;>
          first | exact wt_unbox_le _ | exact wt_dia_unbox_le ‹_› | ea_side)
      | (refine pwN0 $h ?_ ?_ <;>
          first | exact wt_unbox_le _ | exact wt_dia_unbox_le ‹_› | ea_side))

section
variable {p : Nat} {Γ : List Form} {a : Form}

theorem free_cons (h₁ : ¬Occurs p a) (h₂ : ∀ x ∈ Γ, ¬Occurs p x) : ∀ x ∈ a :: Γ, ¬Occurs p x := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx'
  · exact h₁
  · exact h₂ x hx'

theorem free_unbox (h : ∀ x ∈ Γ, ¬Occurs p x) : ∀ x ∈ unbox Γ, ¬Occurs p x :=
  fun x hx => h (□x) (box_mem_of_mem_unbox hx)

theorem free_perm {Γ' : List Form} (hp : Γ.Perm Γ') (h : ∀ x ∈ Γ, ¬Occurs p x) :
    ∀ x ∈ Γ', ¬Occurs p x := fun x hx => h x (hp.mem_iff.2 hx)

end

/-- Closes `¬Occurs p a` for a subformula `a` of a formula `θ` with
`hθ : ¬Occurs p θ`. -/
macro "pq_free " hθ:term : tactic =>
  `(tactic| (intro ho; refine $hθ ?_; ea_sub ho))

/-! ## Theorem 4 (iii) -/

/-- The two conclusions of Theorem 4 (iii) for `Γ, Δ ⇒ ϕ`. -/
def PQ (p : Nat) (Γ Δ : List Form) (ϕ : Form) : Prop :=
  (¬Occurs p ϕ → G4CK (Ep p Δ :: Γ) ϕ) ∧ G4CK (Ep p Δ :: Γ) (Ap p Δ ϕ)

section
variable {p : Nat} {Γ Γ₁ Δ X' : List Form} {ϕ θ : Form}

theorem PQ.map (h : PQ p Γ₁ Δ ϕ)
    (f : ∀ X, G4CK (Ep p Δ :: Γ₁) X → G4CK (Ep p Δ :: Γ) X) : PQ p Γ Δ ϕ :=
  ⟨fun hϕ => f _ (h.1 hϕ), f _ h.2⟩

/-- The rows for an invertible principal formula `θ ∈ Δ`: both are the
recursive call at the environment `X'`. -/
theorem PQ.inv (hθ : θ ∈ Δ) (hE : eRow p (Ee p) (Ap p) Δ ⊥' θ = Ep p X')
    (hA : aEnv p (Ee p) (Ap p) Δ ϕ θ = Ap p X' ϕ) (I : PQ p Γ X' ϕ) : PQ p Γ Δ ϕ :=
  ⟨fun hϕ => E_left hθ (hE ▸ I.1 hϕ), A_right hθ (hA ▸ E_left hθ (hE ▸ I.2))⟩

end

/-- One step of the induction: the case analysis on the last rule.  Rocq
`pq_correct`. -/
theorem pq_step {p : Nat} {Θ : List Form} {ϕ : Form}
    (IH : ∀ {Θ' : List Form} {ϕ' : Form}, pw Θ' ϕ' < pw Θ ϕ → ∀ {Γ' Δ' : List Form},
      Θ'.Perm (Γ' ++ Δ') → (∀ x ∈ Γ', ¬Occurs p x) → G4CK Θ' ϕ' → PQ p Γ' Δ' ϕ')
    {Γ Δ : List Form} (hp : Θ.Perm (Γ ++ Δ)) (hΓ : ∀ x ∈ Γ, ¬Occurs p x) (d : G4CK Θ ϕ) :
    PQ p Γ Δ ϕ := by
  cases d with
  | botL h =>
      rcases List.mem_append.1 (hp.mem_iff.1 h) with hθ | hθ
      · exact ⟨fun _ => .botL (List.mem_cons_of_mem _ hθ), .botL (List.mem_cons_of_mem _ hθ)⟩
      · have e : ∀ X, G4CK (Ep p Δ :: Γ) X := fun X =>
          E_left hθ (by simp only [eRow]; exact .botL List.mem_cons_self)
        exact ⟨fun _ => e _, e _⟩
  | @idP _ q h =>
      rcases List.mem_append.1 (hp.mem_iff.1 h) with hθ | hθ
      · have hq : ¬q = p := hΓ _ hθ
        refine ⟨fun _ => .idP (List.mem_cons_of_mem _ hθ), Af_right ?_⟩
        simp only [aForm]
        rw [if_neg (fun e => hq e.symm)]
        exact .idP (List.mem_cons_of_mem _ hθ)
      · refine ⟨fun hϕ => E_left hθ ?_, ?_⟩
        · simp only [eRow]
          rw [if_neg (fun e => hϕ e.symm)]
          exact .idP List.mem_cons_self
        · by_cases e : p = q
          · refine A_right hθ ?_
            simp only [aEnv]
            rw [if_pos e, if_pos (congrArg Form.var e)]
            exact .top
          · refine E_left hθ ?_
            simp only [eRow]
            rw [if_neg e]
            refine Af_right ?_
            simp only [aForm]
            rw [if_neg e]
            exact .idP List.mem_cons_self
  | @andR _ φ ψ d₁ d₂ =>
      have I₁ := IH (by ea_dec) hp hΓ d₁
      have I₂ := IH (by ea_dec) hp hΓ d₂
      exact ⟨fun hϕ => .andR (I₁.1 fun h => hϕ (Or.inl h)) (I₂.1 fun h => hϕ (Or.inr h)),
        Af_right (by simp only [aForm]; exact .andR I₁.2 I₂.2)⟩
  | @andL _ Δ₀ φ ψ _ h d' =>
      rcases List.mem_append.1 (hp.mem_iff.1 (h.mem_iff.2 List.mem_cons_self)) with hθ | hθ
      · obtain ⟨Γ', hΓ'⟩ := exists_perm_cons_of_mem hθ
        have hr := restΓ h hp hΓ'
        have hθf := hΓ _ hθ
        have hf' : ∀ x ∈ Γ', ¬Occurs p x := fun x hx =>
          hΓ x (hΓ'.mem_iff.2 (List.mem_cons_of_mem _ hx))
        have I : PQ p (φ :: ψ :: Γ') Δ _ := IH (by pq_lt h) (splitΓ [φ, ψ] hr)
          (free_cons (by pq_free hθf) (free_cons (by pq_free hθf) hf')) d'
        exact I.map fun X e => .andL (perm_ins1 hΓ') (.front2 e)
      · have hr := restΔ h hp hθ
        have I : PQ p Γ (ψ :: φ :: rm (φ ⋏ ψ) Δ) _ := IH (by pq_lt h)
          ((splitΔ [φ, ψ] hr).trans ((List.Perm.swap ψ φ _).append_left Γ)) hΓ d'
        exact I.inv hθ rfl rfl
  | @orR1 _ φ ψ d' =>
      have I := IH (by ea_dec) hp hΓ d'
      exact ⟨fun hϕ => .orR1 (I.1 fun h => hϕ (Or.inl h)),
        Af_right (by simp only [aForm]; exact .orR1 I.2)⟩
  | @orR2 _ φ ψ d' =>
      have I := IH (by ea_dec) hp hΓ d'
      exact ⟨fun hϕ => .orR2 (I.1 fun h => hϕ (Or.inr h)),
        Af_right (by simp only [aForm]; exact .orR2 I.2)⟩
  | @orL _ Δ₀ φ ψ _ h d₁ d₂ =>
      rcases List.mem_append.1 (hp.mem_iff.1 (h.mem_iff.2 List.mem_cons_self)) with hθ | hθ
      · obtain ⟨Γ', hΓ'⟩ := exists_perm_cons_of_mem hθ
        have hr := restΓ h hp hΓ'
        have hθf := hΓ _ hθ
        have hf' : ∀ x ∈ Γ', ¬Occurs p x := fun x hx =>
          hΓ x (hΓ'.mem_iff.2 (List.mem_cons_of_mem _ hx))
        have I₁ : PQ p (φ :: Γ') Δ _ := IH (by pq_lt h) (splitΓ [φ] hr)
          (free_cons (by pq_free hθf) hf') d₁
        have I₂ : PQ p (ψ :: Γ') Δ _ := IH (by pq_lt h) (splitΓ [ψ] hr)
          (free_cons (by pq_free hθf) hf') d₂
        exact ⟨fun hϕ => .orL (perm_ins1 hΓ') (.front1 (I₁.1 hϕ)) (.front1 (I₂.1 hϕ)),
          .orL (perm_ins1 hΓ') (.front1 I₁.2) (.front1 I₂.2)⟩
      · have hr := restΔ h hp hθ
        have I₁ : PQ p Γ (φ :: rm (φ ⋎ ψ) Δ) _ := IH (by pq_lt h) (splitΔ [φ] hr) hΓ d₁
        have I₂ : PQ p Γ (ψ :: rm (φ ⋎ ψ) Δ) _ := IH (by pq_lt h) (splitΔ [ψ] hr) hΓ d₂
        exact ⟨fun hϕ => E_left hθ (by
            simp only [eRow, Ee]; exact .orL (List.Perm.refl _) (I₁.1 hϕ) (I₂.1 hϕ)),
          A_right hθ (by
            simp only [aEnv, Ee]; exact .andR (.impR (.wk1 I₁.2)) (.impR (.wk1 I₂.2)))⟩
  | @impR _ φ ψ d' =>
      refine ⟨fun hϕ => .impR (.front1 ((IH (by ea_dec) (hp.cons φ)
        (free_cons (fun h => hϕ (Or.inl h)) hΓ) d').1 fun h => hϕ (Or.inr h))), ?_⟩
      have I : PQ p Γ (φ :: Δ) ψ :=
        IH (by ea_dec) ((hp.cons φ).trans List.perm_middle.symm) hΓ d'
      exact Af_right (by simp only [aForm, Ee]; exact .impR (.wk1 I.2))
  | @impAndL _ Δ₀ φ ψ χ _ h d' =>
      rcases List.mem_append.1 (hp.mem_iff.1 (h.mem_iff.2 List.mem_cons_self)) with hθ | hθ
      · obtain ⟨Γ', hΓ'⟩ := exists_perm_cons_of_mem hθ
        have hr := restΓ h hp hΓ'
        have hθf := hΓ _ hθ
        have hf' : ∀ x ∈ Γ', ¬Occurs p x := fun x hx =>
          hΓ x (hΓ'.mem_iff.2 (List.mem_cons_of_mem _ hx))
        have I : PQ p ((φ ⟶ (ψ ⟶ χ)) :: Γ') Δ _ := IH (by pq_lt h) (splitΓ [_] hr)
          (free_cons (by pq_free hθf) hf') d'
        exact I.map fun X e => .impAndL (perm_ins1 hΓ') (.front1 e)
      · have hr := restΔ h hp hθ
        have I : PQ p Γ ((φ ⟶ (ψ ⟶ χ)) :: rm ((φ ⋏ ψ) ⟶ χ) Δ) _ :=
          IH (by pq_lt h) (splitΔ [_] hr) hΓ d'
        exact I.inv hθ rfl rfl
  | @impOrL _ Δ₀ φ ψ χ _ h d' =>
      rcases List.mem_append.1 (hp.mem_iff.1 (h.mem_iff.2 List.mem_cons_self)) with hθ | hθ
      · obtain ⟨Γ', hΓ'⟩ := exists_perm_cons_of_mem hθ
        have hr := restΓ h hp hΓ'
        have hθf := hΓ _ hθ
        have hf' : ∀ x ∈ Γ', ¬Occurs p x := fun x hx =>
          hΓ x (hΓ'.mem_iff.2 (List.mem_cons_of_mem _ hx))
        have I : PQ p ((φ ⟶ χ) :: (ψ ⟶ χ) :: Γ') Δ _ := IH (by pq_lt h) (splitΓ [_, _] hr)
          (free_cons (by pq_free hθf) (free_cons (by pq_free hθf) hf')) d'
        exact I.map fun X e => .impOrL (perm_ins1 hΓ') (.front2 e)
      · have hr := restΔ h hp hθ
        have I : PQ p Γ ((ψ ⟶ χ) :: (φ ⟶ χ) :: rm ((φ ⋎ ψ) ⟶ χ) Δ) _ := IH (by pq_lt h)
          ((splitΔ [_, _] hr).trans ((List.Perm.swap _ _ _).append_left Γ)) hΓ d'
        exact I.inv hθ rfl rfl
  | @impVarL _ Δ₀ q φ _ h hq d' =>
      rcases List.mem_append.1 (hp.mem_iff.1 (h.mem_iff.2 List.mem_cons_self)) with hθ | hθ
      · obtain ⟨Γ', hΓ'⟩ := exists_perm_cons_of_mem hθ
        have hr := restΓ h hp hΓ'
        have hθf := hΓ _ hθ
        have hf' : ∀ x ∈ Γ', ¬Occurs p x := fun x hx =>
          hΓ x (hΓ'.mem_iff.2 (List.mem_cons_of_mem _ hx))
        have I : PQ p (φ :: Γ') Δ _ := IH (by pq_lt h) (splitΓ [φ] hr)
          (free_cons (by pq_free hθf) hf') d'
        by_cases hqΓ : Form.var q ∈ Γ'
        · exact I.map fun X e =>
            .impVarL (perm_ins1 hΓ') (List.mem_cons_of_mem _ hqΓ) (.front1 e)
        · have hqΔ : Form.var q ∈ Δ := (List.mem_append.1 (hr.mem_iff.1 hq)).resolve_left hqΓ
          have hpq : ¬p = q := fun e => hθf (Or.inl e.symm)
          refine I.map fun X e => ?_
          refine G4CK.contract (A := Ep p Δ) ?_ (List.Perm.refl _)
          refine E_left hqΔ ?_
          simp only [eRow]
          rw [if_neg hpq]
          exact .impVarL (perm_ins2 hΓ') List.mem_cons_self (.wk1 (.front1 e))
      · have hr := restΔ h hp hθ
        have I : PQ p Γ (φ :: rm (Form.var q ⟶ φ) Δ) _ :=
          IH (by pq_lt h) (splitΔ [φ] hr) hΓ d'
        by_cases hqΔ : Form.var q ∈ Δ
        · exact I.inv hθ (by simp only [eRow, Ee]; rw [if_pos hqΔ])
            (by simp only [aEnv]; rw [if_pos hqΔ])
        · have hqΓ : Form.var q ∈ Γ := (List.mem_append.1 (hr.mem_iff.1 hq)).resolve_right
            fun h => hqΔ (mem_of_mem_rm h)
          have hpq : ¬p = q := fun e => hΓ _ hqΓ e.symm
          have eL : ∀ X, G4CK (Ep p (φ :: rm (Form.var q ⟶ φ) Δ) :: Γ) X →
              G4CK (Ep p Δ :: Γ) X := fun X e => E_left hθ (by
            simp only [eRow, Ee]; rw [if_neg hqΔ, if_neg hpq]
            exact .impVarL (List.Perm.refl _) hqΓ e)
          exact ⟨fun hϕ => eL _ (I.1 hϕ), A_right hθ (by
            simp only [aEnv]; rw [if_neg hqΔ, if_neg hpq]
            exact .andR (.idP (List.mem_cons_of_mem _ hqΓ)) (eL _ I.2))⟩
  | @impImpL _ Δ₀ φ ψ χ _ h d₁ d₂ =>
      rcases List.mem_append.1 (hp.mem_iff.1 (h.mem_iff.2 List.mem_cons_self)) with hθ | hθ
      · obtain ⟨Γ', hΓ'⟩ := exists_perm_cons_of_mem hθ
        have hr := restΓ h hp hΓ'
        have hθf := hΓ _ hθ
        have hf' : ∀ x ∈ Γ', ¬Occurs p x := fun x hx =>
          hΓ x (hΓ'.mem_iff.2 (List.mem_cons_of_mem _ hx))
        have I₁ : PQ p ((ψ ⟶ χ) :: Γ') Δ (φ ⟶ ψ) := IH (by pq_lt h) (splitΓ [_] hr)
          (free_cons (by pq_free hθf) hf') d₁
        have I₂ : PQ p (χ :: Γ') Δ _ := IH (by pq_lt h) (splitΓ [χ] hr)
          (free_cons (by pq_free hθf) hf') d₂
        exact I₂.map fun X e =>
          .impImpL (perm_ins1 hΓ') (.front1 (I₁.1 (by pq_free hθf))) (.front1 e)
      · have hr := restΔ h hp hθ
        have I₁ : PQ p Γ (φ :: (ψ ⟶ χ) :: rm ((φ ⟶ ψ) ⟶ χ) Δ) ψ :=
          IH (by pq_lt h) (splitΔ [_, _] hr) hΓ d₁.impR_inv
        have I₂ : PQ p Γ (χ :: rm ((φ ⟶ ψ) ⟶ χ) Δ) _ := IH (by pq_lt h) (splitΔ [χ] hr) hΓ d₂
        have eL : ∀ X, G4CK (Ep p (χ :: rm ((φ ⟶ ψ) ⟶ χ) Δ) :: Γ) X → G4CK (Ep p Δ :: Γ) X :=
          fun X e => E_left hθ (by
            simp only [eRow, Ee]
            exact .impImpL (List.Perm.refl _) (.wk (.impR I₁.2)) e)
        exact ⟨fun hϕ => eL _ (I₂.1 hϕ), A_right hθ (by
          simp only [aEnv, Ee]; exact .andR (.wk (.impR I₁.2)) (eL _ I₂.2))⟩
  | @boxR _ φ d' =>
      have I : PQ p (unbox Γ) (unbox Δ) φ := IH (by ea_dec) (splitU hp) (free_unbox hΓ) d'
      exact ⟨fun hϕ => Ep_boxR (I.1 hϕ), Af_right (by
        simp only [aForm, Ee]; exact .boxR (G4CK.unboxWk [] (Ep p Δ) (.impR I.2)))⟩
  | @impBoxL _ Δ₀ φ₁ φ₂ _ h d₁ d₂ =>
      rcases List.mem_append.1 (hp.mem_iff.1 (h.mem_iff.2 List.mem_cons_self)) with hθ | hθ
      · obtain ⟨Γ', hΓ'⟩ := exists_perm_cons_of_mem hθ
        have hr := restΓ h hp hΓ'
        have hθf := hΓ _ hθ
        have hf' : ∀ x ∈ Γ', ¬Occurs p x := fun x hx =>
          hΓ x (hΓ'.mem_iff.2 (List.mem_cons_of_mem _ hx))
        have I₁ : PQ p (unbox Γ') (unbox Δ) φ₁ :=
          IH (by pq_lt h) (splitU hr) (free_unbox hf') d₁
        have I₂ : PQ p (φ₂ :: Γ') Δ _ := IH (by pq_lt h) (splitΓ [φ₂] hr)
          (free_cons (by pq_free hθf) hf') d₂
        have b : G4CK (Ep p Δ :: Γ') (□φ₁) := Ep_boxR (I₁.1 (by pq_free hθf))
        exact I₂.map fun X e => (b.weakImp (.front1 e)).perm (perm_ins1 hΓ').symm
      · have hr := restΔ h hp hθ
        have I₁ : PQ p (unbox Γ) (unbox (rm ((□φ₁) ⟶ φ₂) Δ)) φ₁ :=
          IH (by pq_lt h) (splitU hr) (free_unbox hΓ) d₁
        have I₂ : PQ p Γ (φ₂ :: rm ((□φ₁) ⟶ φ₂) Δ) _ :=
          IH (by pq_lt h) (splitΔ [φ₂] hr) hΓ d₂
        have b := G4CK.boxR (Γ := Γ) (.impR I₁.2)
        have eL : ∀ X, G4CK (Ep p (φ₂ :: rm ((□φ₁) ⟶ φ₂) Δ) :: Γ) X → G4CK (Ep p Δ :: Γ) X :=
          fun X e => E_left hθ (by simp only [eRow, Ee]; exact b.weakImp e)
        exact ⟨fun hϕ => eL _ (I₂.1 hϕ), A_right hθ (by
          simp only [aEnv, Ee]; exact .andR b.wk (eL _ I₂.2))⟩
  | @impDiaL _ Δ₀ γ φ₁ φ₂ _ h hγ d₁ d₂ =>
      rcases List.mem_append.1 (hp.mem_iff.1 (h.mem_iff.2 List.mem_cons_self)) with hθ | hθ
      · obtain ⟨Γ', hΓ'⟩ := exists_perm_cons_of_mem hθ
        have hr := restΓ h hp hΓ'
        have hθf := hΓ _ hθ
        have hf' : ∀ x ∈ Γ', ¬Occurs p x := fun x hx =>
          hΓ x (hΓ'.mem_iff.2 (List.mem_cons_of_mem _ hx))
        have I₂ : PQ p (φ₂ :: Γ') Δ _ := IH (by pq_lt h) (splitΓ [φ₂] hr)
          (free_cons (by pq_free hθf) hf') d₂
        by_cases hγΓ : (◇γ) ∈ Γ'
        · -- both principal formulas in `Γ`
          have I₁ : PQ p (γ :: unbox Γ') (unbox Δ) φ₁ := IH (by pq_lt h) ((splitU hr).cons γ)
            (free_cons (hf' (◇γ) hγΓ) (free_unbox hf')) d₁
          refine I₂.map fun X e => E9_dup ?_
          exact .impDiaL (perm_ins2 hΓ') (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hγΓ))
            (e9_unbox [γ] (I₁.1 (by pq_free hθf))) (.wk1 (.front1 e))
        · -- `◇φ₁ → φ₂ ∈ Γ`, `◇γ ∈ Δ`
          have hγΔ : (◇γ) ∈ Δ := (List.mem_append.1 (hr.mem_iff.1 hγ)).resolve_left hγΓ
          have I₁ : PQ p (unbox Γ') (γ :: unbox (rm (◇γ) Δ)) φ₁ := IH (by pq_lt h)
            (by rw [unbox_rm (by intro a e; cases e)]
                exact ((splitU hr).cons γ).trans List.perm_middle.symm)
            (free_unbox hf') d₁
          refine I₂.map fun X e => ?_
          refine G4CK.contract (A := Ep p Δ) ?_ (List.Perm.refl _)
          refine E_left hγΔ ?_
          simp only [eRow, Ee]
          exact .impDiaL (perm_ins2 hΓ') List.mem_cons_self
            (G4CK.unboxWk [_] (Ep p Δ) (I₁.1 (by pq_free hθf))) (.wk1 (.front1 e))
      · have hr := restΔ h hp hθ
        have I₂ : PQ p Γ (φ₂ :: rm ((◇φ₁) ⟶ φ₂) Δ) _ :=
          IH (by pq_lt h) (splitΔ [φ₂] hr) hΓ d₂
        by_cases hγΓ : (◇γ) ∈ Γ
        · -- `◇φ₁ → φ₂ ∈ Δ`, `◇γ ∈ Γ`
          have I₁ : PQ p (γ :: unbox Γ) (unbox (rm ((◇φ₁) ⟶ φ₂) Δ)) φ₁ :=
            IH (by pq_lt h) ((splitU hr).cons γ) (free_cons (hΓ (◇γ) hγΓ) (free_unbox hΓ)) d₁
          have g := G4CK.impR I₁.2
          have eL : ∀ X, G4CK (Ep p (φ₂ :: rm ((◇φ₁) ⟶ φ₂) Δ) :: Γ) X → G4CK (Ep p Δ :: Γ) X :=
            fun X e => E_left hθ (by
              simp only [eRow, Ee]; exact .impDiaL (List.Perm.refl _) hγΓ g e)
          obtain ⟨Γ₂, hΓ₂⟩ := exists_perm_cons_of_mem hγΓ
          have g' : G4CK ([γ] ++ unbox Γ₂) _ := g.perm ((unbox_perm hΓ₂).cons γ)
          exact ⟨fun hϕ => eL _ (I₂.1 hϕ), A_right hθ (by
            simp only [aEnv, Ee]
            exact .andR (.diaL (perm_ins1 hΓ₂) (G4CK.unboxWk [γ] (Ep p Δ) g')) (eL _ I₂.2))⟩
        · -- both principal formulas in `Δ`
          have hγR : (◇γ) ∈ rm ((◇φ₁) ⟶ φ₂) Δ :=
            (List.mem_append.1 (hr.mem_iff.1 hγ)).resolve_left hγΓ
          have hγΔ : (◇γ) ∈ Δ := mem_of_mem_rm hγR
          have I₁ : PQ p (unbox Γ) (γ :: unbox (rm (◇γ) (rm ((◇φ₁) ⟶ φ₂) Δ))) φ₁ :=
            IH (by pq_lt h)
              (by rw [unbox_rm (by intro a e; cases e)]
                  exact ((splitU hr).cons γ).trans List.perm_middle.symm)
              (free_unbox hΓ) d₁
          have b := G4CK.boxR (Γ := Γ) (.impR I₁.2)
          have eL : ∀ X, G4CK (Ep p (φ₂ :: rm ((◇φ₁) ⟶ φ₂) Δ) :: Γ) X → G4CK (Ep p Δ :: Γ) X :=
            fun X e => E12_left hθ hγΔ (by simp only [eRow12, Ee]; exact b.weakImp e)
          exact ⟨fun hϕ => eL _ (I₂.1 hϕ), A17_right hθ hγΔ (by
            simp only [aRow17, Ee]; exact .andR b.wk (eL _ I₂.2))⟩
  | @diaL _ Δ₀ φ ψ h d' =>
      rcases List.mem_append.1 (hp.mem_iff.1 (h.mem_iff.2 List.mem_cons_self)) with hθ | hθ
      · obtain ⟨Γ', hΓ'⟩ := exists_perm_cons_of_mem hθ
        have hr := restΓ h hp hΓ'
        have hθf := hΓ _ hθ
        have hf' : ∀ x ∈ Γ', ¬Occurs p x := fun x hx =>
          hΓ x (hΓ'.mem_iff.2 (List.mem_cons_of_mem _ hx))
        have I : PQ p (φ :: unbox Γ') (unbox Δ) ψ := IH (by pq_lt h) ((splitU hr).cons φ)
          (free_cons hθf (free_unbox hf')) d'
        exact ⟨fun hϕ => E9_dup (.diaL (perm_ins2 hΓ') (e9_unbox [φ] (I.1 hϕ))),
          Af_right (by
            simp only [aForm, Ee]
            exact .diaL (perm_ins1 hΓ') (G4CK.unboxWk [φ] (Ep p Δ) (.impR I.2)))⟩
      · have hr := restΔ h hp hθ
        have I : PQ p (unbox Γ) (φ :: unbox (rm (◇φ) Δ)) ψ := IH (by pq_lt h)
          (((splitU hr).cons φ).trans List.perm_middle.symm) (free_unbox hΓ) d'
        exact ⟨fun hϕ => E_left hθ (by
            simp only [eRow, Ee]; exact .diaL (List.Perm.refl _) (I.1 hϕ)),
          A16_right hθ (by
            simp only [aRow16, Ee]
            exact .boxR (G4CK.unboxWk [] (Ep p Δ) (.impR I.2)))⟩

/-- Rocq `pq_correct`, by induction on the measure. -/
theorem pq_aux (p : Nat) : ∀ (n : Nat) {Θ : List Form} {ϕ : Form}, pw Θ ϕ < n →
    ∀ {Γ Δ : List Form}, Θ.Perm (Γ ++ Δ) → (∀ x ∈ Γ, ¬Occurs p x) → G4CK Θ ϕ → PQ p Γ Δ ϕ
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, _, _, hn => fun hp hΓ d =>
      pq_step (fun h => pq_aux p n (by omega)) hp hΓ d

/-- **Theorem 4 (iii)** (`thm:UIP_CK`, uniformity).  Rocq `pq_correct`.

If no member of `Γ` contains `p` and `Γ, Δ ⇒ ϕ`, then `Γ, Ep(Δ) ⇒ ϕ` when `ϕ`
does not contain `p`, and `Γ, Ep(Δ) ⇒ Ap(Δ ⇒ ϕ)`. -/
theorem pq_correct {p : Nat} {Γ Δ : List Form} {ϕ : Form} (hΓ : ∀ x ∈ Γ, ¬Occurs p x)
    (d : G4CK (Γ ++ Δ) ϕ) :
    (¬Occurs p ϕ → G4CK (Ep p Δ :: Γ) ϕ) ∧ G4CK (Ep p Δ :: Γ) (Ap p Δ ϕ) :=
  pq_aux p _ (Nat.lt_succ_self _) (List.Perm.refl _) hΓ d

#print axioms pq_correct

end CK
