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

end PLLND
