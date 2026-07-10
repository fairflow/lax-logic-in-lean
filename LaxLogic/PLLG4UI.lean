import LaxLogic.PLLG4Dec

/-!
# Uniform interpolation, phase 2: the Pitts quantifiers

`interE p fuel Γ` — the ∃-quantifier for contexts (strongest p-free
consequence of `Γ`, to fuel depth), conjunction-shaped; and
`interA p fuel Γ C` — the ∀-quantifier for sequents (weakest p-free
antecedent `X` with `X, Γ ⊢ C`), disjunction-shaped.  Both by **plain
fuel recursion** — no termination order on sequents, the ingredient
Iemhoff's method lacks for retention calculi: adequacy will instead
ride `height_bound`, the pigeonhole bound extracted from the decider.

The clause sets follow the rules of the cumulative calculus `G4s`,
including the three *lax* clauses this development contributes:

* `◯ E_p(χ :: Γ)` for each box `◯χ ∈ Γ` (opening);
* `A_p(Γ ⇒ A) → E_p(B :: Γ)` for each `◯A→B ∈ Γ` (`R◯→″`-firing);
* `A_p(X :: Γ ⇒ ◯A) → E_p(B :: Γ)` for each such pair with a witness
  box `◯X ∈ Γ` (`L◯→″`-firing);

and their `interA`-side analogues.
-/

open PLLFormula

namespace PLLND

/-- Big conjunction; `[]` is `⊤ = ⊥→⊥`. -/
def andAll : List PLLFormula → PLLFormula
  | [] => truePLL
  | φ :: l => φ.and (andAll l)

/-- Big disjunction; `[]` is `⊥`. -/
def orAll : List PLLFormula → PLLFormula
  | [] => falsePLL
  | φ :: l => φ.or (orAll l)

namespace G4c

theorem truePLL_intro (Γ : List PLLFormula) : G4c Γ truePLL :=
  impR (botL (List.Mem.head _))

theorem andAll_intro : ∀ {l : List PLLFormula} {Γ : List PLLFormula},
    (∀ φ ∈ l, G4c Γ φ) → G4c Γ (andAll l) := by
  intro l
  induction l with
  | nil => intro Γ _; exact truePLL_intro Γ
  | cons φ l ih =>
      intro Γ h
      exact andR (h φ (.head _)) (ih fun ψ hψ => h ψ (.tail _ hψ))

theorem andAll_elim : ∀ {l : List PLLFormula} {φ : PLLFormula}, φ ∈ l →
    ∀ {Δ : List PLLFormula} {D : PLLFormula},
    G4c (φ :: Δ) D → G4c (andAll l :: Δ) D := by
  intro l
  induction l with
  | nil => intro φ h; cases h
  | cons x l ih =>
      intro φ hmem Δ D h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · -- φ is the head: expose it with andL
        exact andL (List.Perm.refl _)
          ((h.weaken (andAll l)).perm
            ((List.Perm.swap _ _ _).trans (List.Perm.refl _)))
      · -- φ is in the tail
        refine andL (List.Perm.refl _) ?_
        have := ih hmem' (Δ := x :: Δ) (D := D)
          ((h.weaken x).perm (List.Perm.swap _ _ _))
        exact (this.perm (List.Perm.swap _ _ _))

theorem orAll_intro : ∀ {l : List PLLFormula} {φ : PLLFormula}, φ ∈ l →
    ∀ {Γ : List PLLFormula}, G4c Γ φ → G4c Γ (orAll l) := by
  intro l
  induction l with
  | nil => intro φ h; cases h
  | cons x l ih =>
      intro φ hmem Γ h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact orR1 h
      · exact orR2 (ih hmem' h)

theorem orAll_elim : ∀ {l : List PLLFormula} {Δ : List PLLFormula}
    {D : PLLFormula}, (∀ φ ∈ l, G4c (φ :: Δ) D) →
    G4c (orAll l :: Δ) D := by
  intro l
  induction l with
  | nil => intro Δ D _; exact botL (.head _)
  | cons x l ih =>
      intro Δ D h
      exact orL (List.Perm.refl _) (h x (.head _))
        (ih fun ψ hψ => h ψ (.tail _ hψ))

end G4c

/-! ### `G4s`-level toolkit

The soundness and adequacy properties of the quantifiers live at the
cumulative set calculus `G4s`, whose rules match the clause contexts
verbatim (`(A :: Γ).toFinset = insert A Γ.toFinset`); everything is
packaged back to `G4c` at the end via `G4c.iff_set`.  First the
height-erased rule lifters (two-premise rules take a `max`), then the
big-operator introduction/elimination lemmas.
-/

namespace G4s

theorem weaken_subset {Γ Γ' : Finset PLLFormula} {C : PLLFormula}
    (d : G4s Γ C) (h : Γ ⊆ Γ') : G4s Γ' C := by
  obtain ⟨n, d⟩ := d
  exact ⟨n, d.weaken_subset h⟩

theorem init {Γ : Finset PLLFormula} {a : String} (h : prop a ∈ Γ) :
    G4s Γ (prop a) := ⟨0, .init h⟩

theorem botL {Γ : Finset PLLFormula} {C : PLLFormula}
    (h : falsePLL ∈ Γ) : G4s Γ C := ⟨0, .botL h⟩

theorem andR {Γ : Finset PLLFormula} {A B : PLLFormula}
    (d₁ : G4s Γ A) (d₂ : G4s Γ B) : G4s Γ (A.and B) := by
  obtain ⟨n, d₁⟩ := d₁
  obtain ⟨m, d₂⟩ := d₂
  exact ⟨max n m + 1, .andR (d₁.mono (Nat.le_max_left n m))
    (d₂.mono (Nat.le_max_right n m))⟩

theorem orR1 {Γ : Finset PLLFormula} {A B : PLLFormula}
    (d : G4s Γ A) : G4s Γ (A.or B) := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .orR1 d⟩

theorem orR2 {Γ : Finset PLLFormula} {A B : PLLFormula}
    (d : G4s Γ B) : G4s Γ (A.or B) := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .orR2 d⟩

theorem impR {Γ : Finset PLLFormula} {A B : PLLFormula}
    (d : G4s (insert A Γ) B) : G4s Γ (A.ifThen B) := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .impR d⟩

theorem laxR {Γ : Finset PLLFormula} {A : PLLFormula}
    (d : G4s Γ A) : G4s Γ A.somehow := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .laxR d⟩

theorem laxL {Γ : Finset PLLFormula} {A B : PLLFormula}
    (h : A.somehow ∈ Γ) (d : G4s (insert A Γ) B.somehow) :
    G4s Γ B.somehow := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .laxL h d⟩

theorem andL {Γ : Finset PLLFormula} {A B C : PLLFormula}
    (h : A.and B ∈ Γ) (d : G4s (insert A (insert B Γ)) C) :
    G4s Γ C := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .andL h d⟩

theorem orL {Γ : Finset PLLFormula} {A B C : PLLFormula}
    (h : A.or B ∈ Γ) (d₁ : G4s (insert A Γ) C)
    (d₂ : G4s (insert B Γ) C) : G4s Γ C := by
  obtain ⟨n, d₁⟩ := d₁
  obtain ⟨m, d₂⟩ := d₂
  exact ⟨max n m + 1, .orL h (d₁.mono (Nat.le_max_left n m))
    (d₂.mono (Nat.le_max_right n m))⟩

theorem impLProp {Γ : Finset PLLFormula} {a : String} {B C : PLLFormula}
    (h : (prop a).ifThen B ∈ Γ) (ha : prop a ∈ Γ)
    (d : G4s (insert B Γ) C) : G4s Γ C := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .impLProp h ha d⟩

theorem impLAnd {Γ : Finset PLLFormula} {A B D C : PLLFormula}
    (h : (A.and B).ifThen D ∈ Γ)
    (d : G4s (insert (A.ifThen (B.ifThen D)) Γ) C) : G4s Γ C := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .impLAnd h d⟩

theorem impLOr {Γ : Finset PLLFormula} {A B D C : PLLFormula}
    (h : (A.or B).ifThen D ∈ Γ)
    (d : G4s (insert (A.ifThen D) (insert (B.ifThen D) Γ)) C) :
    G4s Γ C := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .impLOr h d⟩

theorem impLImp {Γ : Finset PLLFormula} {A B D C : PLLFormula}
    (h : (A.ifThen B).ifThen D ∈ Γ)
    (d₁ : G4s (insert (B.ifThen D) Γ) (A.ifThen B))
    (d₂ : G4s (insert D Γ) C) : G4s Γ C := by
  obtain ⟨n, d₁⟩ := d₁
  obtain ⟨m, d₂⟩ := d₂
  exact ⟨max n m + 1, .impLImp h (d₁.mono (Nat.le_max_left n m))
    (d₂.mono (Nat.le_max_right n m))⟩

theorem impLLax {Γ : Finset PLLFormula} {A B C : PLLFormula}
    (h : A.somehow.ifThen B ∈ Γ) (d₁ : G4s Γ A)
    (d₂ : G4s (insert B Γ) C) : G4s Γ C := by
  obtain ⟨n, d₁⟩ := d₁
  obtain ⟨m, d₂⟩ := d₂
  exact ⟨max n m + 1, .impLLax h (d₁.mono (Nat.le_max_left n m))
    (d₂.mono (Nat.le_max_right n m))⟩

theorem impLLaxLax {Γ : Finset PLLFormula} {A B X C : PLLFormula}
    (h : A.somehow.ifThen B ∈ Γ) (hX : X.somehow ∈ Γ)
    (d₁ : G4s (insert X Γ) A.somehow)
    (d₂ : G4s (insert B Γ) C) : G4s Γ C := by
  obtain ⟨n, d₁⟩ := d₁
  obtain ⟨m, d₂⟩ := d₂
  exact ⟨max n m + 1, .impLLaxLax h hX (d₁.mono (Nat.le_max_left n m))
    (d₂.mono (Nat.le_max_right n m))⟩

theorem truePLL_intro (Γ : Finset PLLFormula) : G4s Γ truePLL :=
  impR (botL (Finset.mem_insert_self _ _))

theorem andAll_intro : ∀ {l : List PLLFormula} {Γ : Finset PLLFormula},
    (∀ φ ∈ l, G4s Γ φ) → G4s Γ (andAll l) := by
  intro l
  induction l with
  | nil => intro Γ _; exact truePLL_intro Γ
  | cons φ l ih =>
      intro Γ h
      exact andR (h φ (.head _)) (ih fun ψ hψ => h ψ (.tail _ hψ))

theorem orAll_intro : ∀ {l : List PLLFormula} {φ : PLLFormula}, φ ∈ l →
    ∀ {Γ : Finset PLLFormula}, G4s Γ φ → G4s Γ (orAll l) := by
  intro l
  induction l with
  | nil => intro φ h; cases h
  | cons x l ih =>
      intro φ hmem Γ h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact orR1 h
      · exact orR2 (ih hmem' h)

/-- Split a conjunction at the head of the context (cumulatively). -/
theorem andL_ins {X₁ X₂ : PLLFormula} {Δ : Finset PLLFormula}
    {C : PLLFormula} (d : G4s (insert X₁ (insert X₂ Δ)) C) :
    G4s (insert (X₁.and X₂) Δ) C :=
  andL (Finset.mem_insert_self _ _)
    (d.weaken_subset (Finset.insert_subset_insert _
      (Finset.insert_subset_insert _ (Finset.subset_insert _ _))))

theorem andAll_elim : ∀ {l : List PLLFormula} {φ : PLLFormula}, φ ∈ l →
    ∀ {Δ : Finset PLLFormula} {D : PLLFormula},
    G4s (insert φ Δ) D → G4s (insert (andAll l) Δ) D := by
  intro l
  induction l with
  | nil => intro φ h; cases h
  | cons x l ih =>
      intro φ hmem Δ D h
      simp only [andAll]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact andL_ins (h.weaken_subset
          (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      · refine andL_ins ?_
        have h' : G4s (insert φ (insert x Δ)) D :=
          h.weaken_subset (by
            intro y hy
            simp only [Finset.mem_insert] at hy ⊢
            tauto)
        exact (ih hmem' h').weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)

theorem orAll_elim : ∀ {l : List PLLFormula} {Δ : Finset PLLFormula}
    {C : PLLFormula}, (∀ φ ∈ l, G4s (insert φ Δ) C) →
    G4s (insert (orAll l) Δ) C := by
  intro l
  induction l with
  | nil => intro Δ C _; exact botL (Finset.mem_insert_self _ _)
  | cons x l ih =>
      intro Δ C h
      simp only [orAll]
      refine orL (Finset.mem_insert_self _ _) ?_ ?_
      · exact (h x (.head _)).weaken_subset
          (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      · exact (ih fun ψ hψ => h ψ (.tail _ hψ)).weaken_subset
          (Finset.insert_subset_insert _ (Finset.subset_insert _ _))

end G4s

namespace G4sh

/-- **Height-preserving `impR`-inversion** for the cumulative calculus:
an implication goal can always be unfolded first.  (The other right
rules are not invertible: `◯A` via `laxR` does not imply `A`, and a
disjunction goal proved by `orL` splits.) -/
theorem impR_inv : ∀ {n : Nat} {Γ : Finset PLLFormula} {C : PLLFormula},
    G4sh n Γ C → ∀ {A B : PLLFormula}, C = A.ifThen B →
    G4sh n (insert A Γ) B := by
  intro n Γ C d
  induction d with
  | init h => intro A B hC; cases hC
  | botL h => intro A B hC; exact .botL (Finset.mem_insert_of_mem h)
  | andR _ _ _ _ => intro A B hC; cases hC
  | orR1 _ _ => intro A B hC; cases hC
  | orR2 _ _ => intro A B hC; cases hC
  | laxR _ _ => intro A B hC; cases hC
  | laxL _ _ _ => intro A B hC; cases hC
  | @impR _ _ A₀ B₀ d _ =>
      intro A B hC
      injection hC with h₁ h₂
      subst h₁; subst h₂
      exact d.succ_mono
  | @andL _ Γ₀ A₀ B₀ C₀ h _ ih =>
      intro A B hC
      subst hC
      refine .andL (Finset.mem_insert_of_mem h) ?_
      exact (ih rfl).weaken_subset (by
        intro y hy
        simp only [Finset.mem_insert] at hy ⊢
        tauto)
  | @orL _ Γ₀ A₀ B₀ C₀ h _ _ ih₁ ih₂ =>
      intro A B hC
      subst hC
      refine .orL (Finset.mem_insert_of_mem h) ?_ ?_
      · exact (ih₁ rfl).weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
      · exact (ih₂ rfl).weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
  | @impLProp _ Γ₀ a B₀ C₀ h ha _ ih =>
      intro A B hC
      subst hC
      refine .impLProp (Finset.mem_insert_of_mem h)
        (Finset.mem_insert_of_mem ha) ?_
      exact (ih rfl).weaken_subset (by
        intro y hy
        simp only [Finset.mem_insert] at hy ⊢
        tauto)
  | @impLAnd _ Γ₀ A₀ B₀ D₀ C₀ h _ ih =>
      intro A B hC
      subst hC
      refine .impLAnd (Finset.mem_insert_of_mem h) ?_
      exact (ih rfl).weaken_subset (by
        intro y hy
        simp only [Finset.mem_insert] at hy ⊢
        tauto)
  | @impLOr _ Γ₀ A₀ B₀ D₀ C₀ h _ ih =>
      intro A B hC
      subst hC
      refine .impLOr (Finset.mem_insert_of_mem h) ?_
      exact (ih rfl).weaken_subset (by
        intro y hy
        simp only [Finset.mem_insert] at hy ⊢
        tauto)
  | @impLImp _ Γ₀ A₀ B₀ D₀ C₀ h d₁ _ _ ih₂ =>
      intro A B hC
      subst hC
      refine .impLImp (Finset.mem_insert_of_mem h) ?_ ?_
      · exact d₁.weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
      · exact (ih₂ rfl).weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
  | @impLLax _ Γ₀ A₀ B₀ C₀ h d₁ _ _ ih₂ =>
      intro A B hC
      subst hC
      refine .impLLax (Finset.mem_insert_of_mem h)
        (d₁.weaken_subset (Finset.subset_insert _ _)) ?_
      exact (ih₂ rfl).weaken_subset (by
        intro y hy
        simp only [Finset.mem_insert] at hy ⊢
        tauto)
  | @impLLaxLax _ Γ₀ A₀ B₀ X₀ C₀ h hX d₁ _ _ ih₂ =>
      intro A B hC
      subst hC
      refine .impLLaxLax (Finset.mem_insert_of_mem h)
        (Finset.mem_insert_of_mem hX) ?_ ?_
      · exact d₁.weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
      · exact (ih₂ rfl).weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)

end G4sh

/-! ### The Pitts quantifiers -/

mutual

/-- ∃-quantifier for contexts: strongest p-free consequence, to fuel
depth. -/
def interE (p : String) : Nat → List PLLFormula → PLLFormula
  | 0, _ => truePLL
  | fuel + 1, Γ =>
      andAll (
        (if falsePLL ∈ Γ then [falsePLL] else [])
        ++ Γ.filterMap (fun F => match F with
            | .prop q => if q = p then none else some (prop q)
            | _ => none)
        ++ Γ.flatMap (fun F => match F with
            | .and A B => [interE p fuel (A :: B :: Γ)]
            | .or A B =>
                [(interE p fuel (A :: Γ)).or (interE p fuel (B :: Γ))]
            | .ifThen (.prop q) B =>
                if q = p then
                  (if PLLFormula.prop p ∈ Γ then [interE p fuel (B :: Γ)]
                   else [])
                else [(prop q).ifThen (interE p fuel (B :: Γ))]
            | .ifThen (.and A B) D =>
                [interE p fuel (A.ifThen (B.ifThen D) :: Γ)]
            | .ifThen (.or A B) D =>
                [interE p fuel (A.ifThen D :: B.ifThen D :: Γ)]
            | .ifThen (.ifThen A B) D =>
                [(interA p fuel (B.ifThen D :: Γ) (A.ifThen B)).ifThen
                  (interE p fuel (D :: Γ))]
            | .ifThen (.somehow A) B =>
                ((interA p fuel Γ A).ifThen (interE p fuel (B :: Γ)))
                :: Γ.filterMap (fun X => match X with
                    | .somehow x =>
                        some ((interA p fuel (x :: Γ) A.somehow).ifThen
                          (interE p fuel (B :: Γ)))
                    | _ => none)
            | .somehow χ => [(interE p fuel (χ :: Γ)).somehow]
            | _ => []))

/-- ∀-quantifier for sequents: weakest p-free antecedent, to fuel
depth. -/
def interA (p : String) : Nat → List PLLFormula → PLLFormula → PLLFormula
  | 0, _, _ => falsePLL
  | fuel + 1, Γ, C =>
      orAll (
        (if falsePLL ∈ Γ then [truePLL] else [])
        ++ (match C with
            | .prop q =>
                (if PLLFormula.prop q ∈ Γ then [truePLL] else [])
                ++ (if q = p then [] else [prop q])
            | .falsePLL => []
            | .and C₁ C₂ =>
                [(interA p fuel Γ C₁).and (interA p fuel Γ C₂)]
            | .or C₁ C₂ => [interA p fuel Γ C₁, interA p fuel Γ C₂]
            | .ifThen C₁ C₂ => [interA p fuel (C₁ :: Γ) C₂]
            | .somehow C' =>
                interA p fuel Γ C'
                :: Γ.filterMap (fun X => match X with
                    | .somehow x => some (interA p fuel (x :: Γ) (C'.somehow))
                    | _ => none))
        ++ Γ.flatMap (fun F => match F with
            | .and A B => [interA p fuel (A :: B :: Γ) C]
            | .or A B =>
                [(interA p fuel (A :: Γ) C).and (interA p fuel (B :: Γ) C)]
            | .ifThen (.prop q) B =>
                (if PLLFormula.prop q ∈ Γ then [interA p fuel (B :: Γ) C]
                 else [])
                ++ (if q = p then []
                    else [(prop q).and (interA p fuel (B :: Γ) C)])
            | .ifThen (.and A B) D =>
                [interA p fuel (A.ifThen (B.ifThen D) :: Γ) C]
            | .ifThen (.or A B) D =>
                [interA p fuel (A.ifThen D :: B.ifThen D :: Γ) C]
            | .ifThen (.ifThen A B) D =>
                [(interA p fuel (B.ifThen D :: Γ) (A.ifThen B)).and
                  (interA p fuel (D :: Γ) C)]
            | .ifThen (.somehow A) B =>
                ((interA p fuel Γ A).and (interA p fuel (B :: Γ) C))
                :: Γ.filterMap (fun X => match X with
                    | .somehow x =>
                        some ((interA p fuel (x :: Γ) A.somehow).and
                          (interA p fuel (B :: Γ) C))
                    | _ => none)
            | _ => []))

end

/-! ### p-freeness -/

private theorem mem_atoms_andAll {x : String} :
    ∀ {l : List PLLFormula}, x ∈ (andAll l).atoms → ∃ φ ∈ l, x ∈ φ.atoms := by
  intro l
  induction l with
  | nil => intro h; simp [andAll, truePLL] at h
  | cons φ l ih =>
      intro h
      simp only [andAll, atoms_and, Finset.mem_union] at h
      rcases h with h | h
      · exact ⟨φ, .head _, h⟩
      · obtain ⟨ψ, hmem, hx⟩ := ih h
        exact ⟨ψ, .tail _ hmem, hx⟩

private theorem mem_atoms_orAll {x : String} :
    ∀ {l : List PLLFormula}, x ∈ (orAll l).atoms → ∃ φ ∈ l, x ∈ φ.atoms := by
  intro l
  induction l with
  | nil => intro h; simp [orAll] at h
  | cons φ l ih =>
      intro h
      simp only [orAll, atoms_or, Finset.mem_union] at h
      rcases h with h | h
      · exact ⟨φ, .head _, h⟩
      · obtain ⟨ψ, hmem, hx⟩ := ih h
        exact ⟨ψ, .tail _ hmem, hx⟩

/-- **The quantifiers are p-free.** -/
theorem inter_pfree (p : String) : ∀ (fuel : Nat),
    (∀ Γ, p ∉ (interE p fuel Γ).atoms) ∧
    (∀ Γ C, p ∉ (interA p fuel Γ C).atoms) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro Γ h; simp [interE, truePLL] at h
      · intro Γ C h; simp [interA] at h
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · intro Γ hmem
        simp only [interE] at hmem
        obtain ⟨φ, hφ, hx⟩ := mem_atoms_andAll hmem
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥ clause
            split at hφ
            · rcases List.mem_singleton.mp hφ with rfl
              simp at hx
            · cases hφ
          · -- the atom clauses
            obtain ⟨F, _, heq⟩ := List.mem_filterMap.mp hφ
            cases F with
            | prop q =>
                simp only at heq
                split at heq
                · cases heq
                · injection heq with heq'
                  subst heq'
                  rw [atoms_prop, Finset.mem_singleton] at hx
                  subst hx
                  simp_all
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- the rule clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | and A B =>
              rcases List.mem_singleton.mp hin with rfl
              exact ihE _ hx
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              rw [atoms_or, Finset.mem_union] at hx
              rcases hx with hx | hx
              · exact ihE _ hx
              · exact ihE _ hx
          | somehow χ =>
              rcases List.mem_singleton.mp hin with rfl
              rw [atoms_somehow] at hx
              exact ihE _ hx
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  · split at hin
                    · rcases List.mem_singleton.mp hin with rfl
                      exact ihE _ hx
                    · cases hin
                  · rcases List.mem_singleton.mp hin with rfl
                    rw [atoms_ifThen, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · rw [atoms_prop, Finset.mem_singleton] at hx
                      subst hx
                      simp_all
                    · exact ihE _ hx
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  exact ihE _ hx
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  exact ihE _ hx
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  rw [atoms_ifThen, Finset.mem_union] at hx
                  rcases hx with hx | hx
                  · exact ihA _ _ hx
                  · exact ihE _ hx
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · rw [atoms_ifThen, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · exact ihA _ _ hx
                    · exact ihE _ hx
                  · obtain ⟨X, _, heq⟩ := List.mem_filterMap.mp hin'
                    cases X with
                    | somehow x =>
                        injection heq with heq'
                        subst heq'
                        rw [atoms_ifThen, Finset.mem_union] at hx
                        rcases hx with hx | hx
                        · exact ihA _ _ hx
                        · exact ihE _ hx
                    | prop _ => cases heq
                    | falsePLL => cases heq
                    | and _ _ => cases heq
                    | or _ _ => cases heq
                    | ifThen _ _ => cases heq
      · intro Γ C hmem
        simp only [interA] at hmem
        obtain ⟨φ, hφ, hx⟩ := mem_atoms_orAll hmem
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥-in-Γ clause
            split at hφ
            · rcases List.mem_singleton.mp hφ with rfl
              simp [truePLL] at hx
            · cases hφ
          · -- the goal clauses
            cases C with
            | prop q =>
                rcases List.mem_append.mp hφ with hφ | hφ
                · split at hφ
                  · rcases List.mem_singleton.mp hφ with rfl
                    simp [truePLL] at hx
                  · cases hφ
                · split at hφ
                  · cases hφ
                  · rcases List.mem_singleton.mp hφ with rfl
                    rw [atoms_prop, Finset.mem_singleton] at hx
                    subst hx
                    simp_all
            | falsePLL => cases hφ
            | and C₁ C₂ =>
                rcases List.mem_singleton.mp hφ with rfl
                rw [atoms_and, Finset.mem_union] at hx
                rcases hx with hx | hx
                · exact ihA _ _ hx
                · exact ihA _ _ hx
            | or C₁ C₂ =>
                rcases List.mem_cons.mp hφ with rfl | hφ'
                · exact ihA _ _ hx
                · rcases List.mem_singleton.mp hφ' with rfl
                  exact ihA _ _ hx
            | ifThen C₁ C₂ =>
                rcases List.mem_singleton.mp hφ with rfl
                exact ihA _ _ hx
            | somehow C' =>
                rcases List.mem_cons.mp hφ with rfl | hφ'
                · exact ihA _ _ hx
                · obtain ⟨X, _, heq⟩ := List.mem_filterMap.mp hφ'
                  cases X with
                  | somehow x =>
                      injection heq with heq'
                      subst heq'
                      exact ihA _ _ hx
                  | prop _ => cases heq
                  | falsePLL => cases heq
                  | and _ _ => cases heq
                  | or _ _ => cases heq
                  | ifThen _ _ => cases heq
        · obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | somehow _ => cases hin
          | and A B =>
              rcases List.mem_singleton.mp hin with rfl
              exact ihA _ _ hx
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              rw [atoms_and, Finset.mem_union] at hx
              rcases hx with hx | hx
              · exact ihA _ _ hx
              · exact ihA _ _ hx
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  rcases List.mem_append.mp hin with hin | hin
                  · split at hin
                    · rcases List.mem_singleton.mp hin with rfl
                      exact ihA _ _ hx
                    · cases hin
                  · split at hin
                    · cases hin
                    · rcases List.mem_singleton.mp hin with rfl
                      rw [atoms_and, Finset.mem_union] at hx
                      rcases hx with hx | hx
                      · rw [atoms_prop, Finset.mem_singleton] at hx
                        subst hx
                        simp_all
                      · exact ihA _ _ hx
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  exact ihA _ _ hx
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  exact ihA _ _ hx
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  rw [atoms_and, Finset.mem_union] at hx
                  rcases hx with hx | hx
                  · exact ihA _ _ hx
                  · exact ihA _ _ hx
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · rw [atoms_and, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · exact ihA _ _ hx
                    · exact ihA _ _ hx
                  · obtain ⟨X, _, heq⟩ := List.mem_filterMap.mp hin'
                    cases X with
                    | somehow x =>
                        injection heq with heq'
                        subst heq'
                        rw [atoms_and, Finset.mem_union] at hx
                        rcases hx with hx | hx
                        · exact ihA _ _ hx
                        · exact ihA _ _ hx
                    | prop _ => cases heq
                    | falsePLL => cases heq
                    | and _ _ => cases heq
                    | or _ _ => cases heq
                    | ifThen _ _ => cases heq

theorem interE_pfree (p : String) (fuel : Nat) (Γ : List PLLFormula) :
    p ∉ (interE p fuel Γ).atoms := (inter_pfree p fuel).1 Γ

theorem interA_pfree (p : String) (fuel : Nat) (Γ : List PLLFormula)
    (C : PLLFormula) : p ∉ (interA p fuel Γ C).atoms :=
  (inter_pfree p fuel).2 Γ C

/-! ### Soundness of the quantifiers (Pitts E1/A1)

`interE p fuel Γ` is a consequence of `Γ`, and `interA p fuel Γ C`
suffices for `C` alongside `Γ` — at every fuel.  Both by one mutual
fuel induction at the `G4s` level, where each clause is discharged by
firing the cumulative rule it mirrors; the `impLImp` / `impLLax` /
`impLLaxLax` clauses consume the `interA` induction hypothesis as
their side premise (the sequent-shaped ingredient of the recursion).
-/

private theorem memF {F : PLLFormula} {Γ : List PLLFormula} (h : F ∈ Γ) :
    F ∈ Γ.toFinset := List.mem_toFinset.mpr h

theorem inter_sound (p : String) : ∀ (fuel : Nat),
    (∀ Γ, G4s Γ.toFinset (interE p fuel Γ)) ∧
    (∀ Γ C, G4s (insert (interA p fuel Γ C) Γ.toFinset) C) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro Γ
        simp only [interE]
        exact G4s.truePLL_intro _
      · intro Γ C
        simp only [interA]
        exact G4s.botL (Finset.mem_insert_self _ _)
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · -- E1: Γ ⊢ interE p (fuel+1) Γ
        intro Γ
        simp only [interE]
        refine G4s.andAll_intro ?_
        intro φ hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥ clause
            split at hφ
            next hbot =>
              rcases List.mem_singleton.mp hφ with rfl
              exact G4s.botL (memF hbot)
            next => cases hφ
          · -- the atom clauses
            obtain ⟨F, hFΓ, heq⟩ := List.mem_filterMap.mp hφ
            cases F with
            | prop q =>
                simp only at heq
                split at heq
                · cases heq
                · injection heq with heq'
                  subst heq'
                  exact G4s.init (memF hFΓ)
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- the rule clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | and A B =>
              rcases List.mem_singleton.mp hin with rfl
              have ih' := ihE (A :: B :: Γ)
              rw [List.toFinset_cons, List.toFinset_cons] at ih'
              exact G4s.andL (memF hFΓ) ih'
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              have ih₁ := ihE (A :: Γ)
              rw [List.toFinset_cons] at ih₁
              have ih₂ := ihE (B :: Γ)
              rw [List.toFinset_cons] at ih₂
              exact G4s.orL (memF hFΓ) (G4s.orR1 ih₁) (G4s.orR2 ih₂)
          | somehow χ =>
              rcases List.mem_singleton.mp hin with rfl
              have ih' := ihE (χ :: Γ)
              rw [List.toFinset_cons] at ih'
              exact G4s.laxL (memF hFΓ) (G4s.laxR ih')
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next hq =>
                    split at hin
                    next hp =>
                      rcases List.mem_singleton.mp hin with rfl
                      subst hq
                      have ih' := ihE (B :: Γ)
                      rw [List.toFinset_cons] at ih'
                      exact G4s.impLProp (memF hFΓ) (memF hp) ih'
                    next => cases hin
                  next hq =>
                    rcases List.mem_singleton.mp hin with rfl
                    refine G4s.impR ?_
                    have ih' := ihE (B :: Γ)
                    rw [List.toFinset_cons] at ih'
                    refine G4s.impLProp
                      (Finset.mem_insert_of_mem (memF hFΓ))
                      (Finset.mem_insert_self _ _) ?_
                    exact ih'.weaken_subset
                      (Finset.insert_subset_insert _
                        (Finset.subset_insert _ _))
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  have ih' := ihE (A₁.ifThen (B₁.ifThen B) :: Γ)
                  rw [List.toFinset_cons] at ih'
                  exact G4s.impLAnd (memF hFΓ) ih'
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  have ih' := ihE (A₁.ifThen B :: B₁.ifThen B :: Γ)
                  rw [List.toFinset_cons, List.toFinset_cons] at ih'
                  exact G4s.impLOr (memF hFΓ) ih'
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4s.impR ?_
                  have ihb := ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁)
                  rw [List.toFinset_cons] at ihb
                  have ihd := ihE (B :: Γ)
                  rw [List.toFinset_cons] at ihd
                  refine G4s.impLImp
                    (Finset.mem_insert_of_mem (memF hFΓ)) ?_ ?_
                  · exact ihb.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                  · exact ihd.weaken_subset
                      (Finset.insert_subset_insert _
                        (Finset.subset_insert _ _))
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · refine G4s.impR ?_
                    have ihe := ihE (B :: Γ)
                    rw [List.toFinset_cons] at ihe
                    refine G4s.impLLax
                      (Finset.mem_insert_of_mem (memF hFΓ)) (ihA Γ A₁) ?_
                    exact ihe.weaken_subset
                      (Finset.insert_subset_insert _
                        (Finset.subset_insert _ _))
                  · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin'
                    cases X with
                    | somehow x =>
                        injection heq with heq'
                        subst heq'
                        refine G4s.impR ?_
                        have iha := ihA (x :: Γ) A₁.somehow
                        rw [List.toFinset_cons] at iha
                        have ihe := ihE (B :: Γ)
                        rw [List.toFinset_cons] at ihe
                        refine G4s.impLLaxLax
                          (Finset.mem_insert_of_mem (memF hFΓ))
                          (Finset.mem_insert_of_mem (memF hXΓ)) ?_ ?_
                        · exact iha.weaken_subset (by
                            intro y hy
                            simp only [Finset.mem_insert] at hy ⊢
                            tauto)
                        · exact ihe.weaken_subset
                            (Finset.insert_subset_insert _
                              (Finset.subset_insert _ _))
                    | prop _ => cases heq
                    | falsePLL => cases heq
                    | and _ _ => cases heq
                    | or _ _ => cases heq
                    | ifThen _ _ => cases heq
      · -- A1: interA p (fuel+1) Γ C, Γ ⊢ C
        intro Γ C
        simp only [interA]
        refine G4s.orAll_elim ?_
        intro φ hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥-in-Γ clause
            split at hφ
            next hbot =>
              rcases List.mem_singleton.mp hφ with rfl
              exact G4s.botL (Finset.mem_insert_of_mem (memF hbot))
            next => cases hφ
          · -- the goal clauses
            cases C with
            | prop q =>
                rcases List.mem_append.mp hφ with hφ | hφ
                · split at hφ
                  next hq =>
                    rcases List.mem_singleton.mp hφ with rfl
                    exact G4s.init (Finset.mem_insert_of_mem (memF hq))
                  next => cases hφ
                · split at hφ
                  next => cases hφ
                  next =>
                    rcases List.mem_singleton.mp hφ with rfl
                    exact G4s.init (Finset.mem_insert_self _ _)
            | falsePLL => cases hφ
            | and C₁ C₂ =>
                rcases List.mem_singleton.mp hφ with rfl
                refine G4s.andL_ins ?_
                refine G4s.andR ?_ ?_
                · exact (ihA Γ C₁).weaken_subset
                    (Finset.insert_subset_insert _
                      (Finset.subset_insert _ _))
                · exact (ihA Γ C₂).weaken_subset (Finset.subset_insert _ _)
            | or C₁ C₂ =>
                rcases List.mem_cons.mp hφ with rfl | hφ'
                · exact G4s.orR1 (ihA Γ C₁)
                · rcases List.mem_singleton.mp hφ' with rfl
                  exact G4s.orR2 (ihA Γ C₂)
            | ifThen C₁ C₂ =>
                rcases List.mem_singleton.mp hφ with rfl
                refine G4s.impR ?_
                have ih' := ihA (C₁ :: Γ) C₂
                rw [List.toFinset_cons] at ih'
                exact ih'.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
            | somehow C' =>
                rcases List.mem_cons.mp hφ with rfl | hφ'
                · exact G4s.laxR (ihA Γ C')
                · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hφ'
                  cases X with
                  | somehow x =>
                      injection heq with heq'
                      subst heq'
                      refine G4s.laxL
                        (Finset.mem_insert_of_mem (memF hXΓ)) ?_
                      have ih' := ihA (x :: Γ) C'.somehow
                      rw [List.toFinset_cons] at ih'
                      exact ih'.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                  | prop _ => cases heq
                  | falsePLL => cases heq
                  | and _ _ => cases heq
                  | or _ _ => cases heq
                  | ifThen _ _ => cases heq
        · -- the left clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | somehow _ => cases hin
          | and A B =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4s.andL (Finset.mem_insert_of_mem (memF hFΓ)) ?_
              have ih' := ihA (A :: B :: Γ) C
              rw [List.toFinset_cons, List.toFinset_cons] at ih'
              exact ih'.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4s.andL_ins ?_
              refine G4s.orL (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (memF hFΓ))) ?_ ?_
              · have ih' := ihA (A :: Γ) C
                rw [List.toFinset_cons] at ih'
                exact ih'.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · have ih' := ihA (B :: Γ) C
                rw [List.toFinset_cons] at ih'
                exact ih'.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  rcases List.mem_append.mp hin with hin | hin
                  · split at hin
                    next hq =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine G4s.impLProp
                        (Finset.mem_insert_of_mem (memF hFΓ))
                        (Finset.mem_insert_of_mem (memF hq)) ?_
                      have ih' := ihA (B :: Γ) C
                      rw [List.toFinset_cons] at ih'
                      exact ih'.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                    next => cases hin
                  · split at hin
                    next => cases hin
                    next =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine G4s.andL_ins ?_
                      refine G4s.impLProp
                        (Finset.mem_insert_of_mem
                          (Finset.mem_insert_of_mem (memF hFΓ)))
                        (Finset.mem_insert_self _ _) ?_
                      have ih' := ihA (B :: Γ) C
                      rw [List.toFinset_cons] at ih'
                      exact ih'.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4s.impLAnd
                    (Finset.mem_insert_of_mem (memF hFΓ)) ?_
                  have ih' := ihA (A₁.ifThen (B₁.ifThen B) :: Γ) C
                  rw [List.toFinset_cons] at ih'
                  exact ih'.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4s.impLOr
                    (Finset.mem_insert_of_mem (memF hFΓ)) ?_
                  have ih' := ihA (A₁.ifThen B :: B₁.ifThen B :: Γ) C
                  rw [List.toFinset_cons, List.toFinset_cons] at ih'
                  exact ih'.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4s.andL_ins ?_
                  refine G4s.impLImp
                    (Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem (memF hFΓ))) ?_ ?_
                  · have ih' := ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁)
                    rw [List.toFinset_cons] at ih'
                    exact ih'.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                  · have ih' := ihA (B :: Γ) C
                    rw [List.toFinset_cons] at ih'
                    exact ih'.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · refine G4s.andL_ins ?_
                    refine G4s.impLLax
                      (Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem (memF hFΓ))) ?_ ?_
                    · exact (ihA Γ A₁).weaken_subset
                        (Finset.insert_subset_insert _
                          (Finset.subset_insert _ _))
                    · have ih' := ihA (B :: Γ) C
                      rw [List.toFinset_cons] at ih'
                      exact ih'.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                  · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin'
                    cases X with
                    | somehow x =>
                        injection heq with heq'
                        subst heq'
                        refine G4s.andL_ins ?_
                        refine G4s.impLLaxLax
                          (Finset.mem_insert_of_mem
                            (Finset.mem_insert_of_mem (memF hFΓ)))
                          (Finset.mem_insert_of_mem
                            (Finset.mem_insert_of_mem (memF hXΓ))) ?_ ?_
                        · have ih' := ihA (x :: Γ) A₁.somehow
                          rw [List.toFinset_cons] at ih'
                          exact ih'.weaken_subset (by
                            intro y hy
                            simp only [Finset.mem_insert] at hy ⊢
                            tauto)
                        · have ih' := ihA (B :: Γ) C
                          rw [List.toFinset_cons] at ih'
                          exact ih'.weaken_subset (by
                            intro y hy
                            simp only [Finset.mem_insert] at hy ⊢
                            tauto)
                    | prop _ => cases heq
                    | falsePLL => cases heq
                    | and _ _ => cases heq
                    | or _ _ => cases heq
                    | ifThen _ _ => cases heq

/-- **E1** (set level): the ∃-quantifier is a consequence of `Γ`. -/
theorem interE_sound (p : String) (fuel : Nat) (Γ : List PLLFormula) :
    G4s Γ.toFinset (interE p fuel Γ) := (inter_sound p fuel).1 Γ

/-- **A1** (set level): the ∀-quantifier suffices for `C` alongside
`Γ`. -/
theorem interA_sound (p : String) (fuel : Nat) (Γ : List PLLFormula)
    (C : PLLFormula) : G4s (insert (interA p fuel Γ C) Γ.toFinset) C :=
  (inter_sound p fuel).2 Γ C

/-- E1 at the list calculus. -/
theorem interE_sound_g4c (p : String) (fuel : Nat) (Γ : List PLLFormula) :
    G4c Γ (interE p fuel Γ) :=
  G4c.iff_set.mpr (interE_sound p fuel Γ)

/-- A1 at the list calculus. -/
theorem interA_sound_g4c (p : String) (fuel : Nat) (Γ : List PLLFormula)
    (C : PLLFormula) : G4c (interA p fuel Γ C :: Γ) C := by
  refine G4c.iff_set.mpr ?_
  rw [List.toFinset_cons]
  exact interA_sound p fuel Γ C

end PLLND
