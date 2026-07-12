import LaxLogic.PLLG4UITrunc

/-!
# WIP scaffold: the absorption lemma (budget stabilization)

Target (docs/ui-endgame.md): above the jump-state threshold, adjacent
budgets are interderivable — the one genuinely novel lemma of the UI
tower.  Structure:

* `itp_absorb_base` — the base band `(K+1 → K)`: the cascade with the
  pigeonhole/splice argument.  THE crux.
* `itp_absorb_of_base` — the upper band by induction on `b − K`,
  consuming the base at all fuels; mechanically parallel to
  `itp_budget_mono` (agent-able).

Isolated below as micro-lemmas: the two boxed-position maps whose
exact budget annotations decide the cascade's shape.  Everything here
may contain `sorry`; nothing is imported by the library root.
-/

open PLLFormula

namespace PLLND

/-- Budget cap: overcounts the jump states
`{E} ∪ {A_F, ◯A_F : ◯A_F⊃B ∈ S} ∪ {A⊃B : (A⊃B)⊃D ∈ S}`. -/
def bcap (S : Finset PLLFormula) : Nat := 2 * S.card + 4

/-- Phase B (the crux): the base band. -/
theorem itp_absorb_base (p : String) (S : Finset PLLFormula) : ∀ fuel,
    (∀ Γ, G4c [itpE p S fuel (bcap S) Γ] (itpE p S fuel (bcap S + 1) Γ)) ∧
    (∀ Γ C, G4c [itpA p S fuel (bcap S + 1) Γ C]
      (itpA p S fuel (bcap S) Γ C)) := by
  sorry

/-! ### Replicated clause-table infrastructure

The packaged one-level unfoldings and member-wise mapping helpers of
`LaxLogic/PLLG4UITrunc.lean` (`itpEcls` … `itpAfull_map`) are `private`
there, hence invisible to this file; the band step below works over
them, so they are transcribed verbatim (the `_succ` lemmas re-check
them against `itpE`/`itpA` by `rfl`). -/

/-- The conjunct table of `itpE p S (f+1) b Γ`, references folded. -/
private def itpEcls (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) : List PLLFormula :=
  (if falsePLL ∈ Γ then [falsePLL] else [])
  ++ Γ.filterMap (fun F => match F with
      | .prop q => if q = p then none else some (prop q)
      | _ => none)
  ++ Γ.flatMap (fun F => match F with
      | .and A B =>
          if A ∈ Γ ∧ B ∈ Γ then []
          else if (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) then
            [itpE p S f b (A :: B :: Γ)]
          else []
      | .or A B =>
          if A ∈ Γ ∨ B ∈ Γ then []
          else if A ∈ S ∧ B ∈ S then
            [(itpE p S f b (A :: Γ)).or (itpE p S f b (B :: Γ))]
          else []
      | .ifThen (.prop q) B =>
          if B ∈ Γ then []
          else if B ∈ S then
            if PLLFormula.prop q ∈ Γ then [itpE p S f b (B :: Γ)]
            else if q = p then []
            else [(prop q).ifThen (itpE p S f b (B :: Γ))]
          else []
      | .ifThen (.and A B) D =>
          if A.ifThen (B.ifThen D) ∈ Γ then []
          else if A.ifThen (B.ifThen D) ∈ S then
            [itpE p S f b (A.ifThen (B.ifThen D) :: Γ)]
          else []
      | .ifThen (.or A B) D =>
          if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then []
          else if (A.ifThen D ∈ Γ ∨ A.ifThen D ∈ S) ∧
              (B.ifThen D ∈ Γ ∨ B.ifThen D ∈ S) then
            [itpE p S f b (A.ifThen D :: B.ifThen D :: Γ)]
          else []
      | .ifThen (.ifThen A B) D =>
          if D ∈ Γ then []
          else if D ∈ S then
            if B.ifThen D ∈ Γ then
              if (A.ifThen B).ifThen D ∈ S then
                match b with
                | 0 => []
                | b' + 1 =>
                    [((itpE p S f b' Γ).ifThen
                        (itpA p S f b' Γ (A.ifThen B))).ifThen
                      (itpE p S f b (D :: Γ))]
              else []
            else if B.ifThen D ∈ S then
              [((itpE p S f b (B.ifThen D :: Γ)).ifThen
                  (itpA p S f b (B.ifThen D :: Γ) (A.ifThen B))).ifThen
                (itpE p S f b (D :: Γ))]
            else []
          else []
      | .ifThen (.somehow A) B =>
          if B ∈ Γ then []
          else if B ∈ S then
            (if A.somehow.ifThen B ∈ S then
              match b with
              | 0 => []
              | b' + 1 =>
                  [(itpA p S f b' Γ A).ifThen
                     (itpE p S f b (B :: Γ)),
                   (((itpE p S f b' Γ).ifThen
                       (itpA p S f b' Γ A.somehow)).somehow).ifThen
                     (itpE p S f b (B :: Γ))]
            else [])
            ++ Γ.filterMap (fun X => match X with
                | .somehow x =>
                    if x ∈ Γ ∨ x ∉ S then none
                    else some ((((itpE p S f b (x :: Γ)).ifThen
                        (itpA p S f b (x :: Γ) A.somehow)).somehow).ifThen
                      (itpE p S f b (B :: Γ)))
                | _ => none)
          else []
      | .somehow χ =>
          if χ ∈ Γ ∨ χ ∉ S then []
          else [(itpE p S f b (χ :: Γ)).somehow]
      | _ => [])

/-- One-level unfolding of `itpE` at successor fuel. -/
private theorem itpE_succ (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) :
    itpE p S (f + 1) b Γ = andAll (itpEcls p S f b Γ) := rfl

/-- The goal-directed disjunct table of `itpA p S (f+1) b Γ C`. -/
private def itpAgoal (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  match C with
  | .prop q => if q = p then [] else [prop q]
  | .falsePLL => []
  | .and C₁ C₂ =>
      [(itpA p S f b Γ C₁).and (itpA p S f b Γ C₂)]
  | .or C₁ C₂ => [itpA p S f b Γ C₁, itpA p S f b Γ C₂]
  | .ifThen C₁ C₂ =>
      if C₁ ∈ Γ then
        match b with
        | 0 => []
        | b' + 1 =>
            [(itpE p S f b' (C₁ :: Γ)).ifThen
              (itpA p S f b (C₁ :: Γ) C₂)]
      else
        [(itpE p S f b (C₁ :: Γ)).ifThen
          (itpA p S f b (C₁ :: Γ) C₂)]
  | .somehow D =>
      match b with
      | 0 => []
      | b' + 1 =>
          [((itpE p S f b' Γ).ifThen
              (itpA p S f b Γ D)).somehow]

/-- The context-directed disjunct table of `itpA p S (f+1) b Γ C`. -/
private def itpAenv (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  Γ.flatMap (fun F => match F with
      | .prop q =>
          if q = p ∧ C = PLLFormula.prop p then [truePLL] else []
      | .and A B =>
          if A ∈ Γ ∧ B ∈ Γ then []
          else if (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) then
            [itpA p S f b (A :: B :: Γ) C]
          else []
      | .or A B =>
          if A ∈ Γ ∨ B ∈ Γ then []
          else if A ∈ S ∧ B ∈ S then
            [((itpE p S f b (A :: Γ)).ifThen
                (itpA p S f b (A :: Γ) C)).and
             ((itpE p S f b (B :: Γ)).ifThen
                (itpA p S f b (B :: Γ) C))]
          else []
      | .ifThen (.prop q) B =>
          if B ∈ Γ then []
          else if B ∈ S then
            if PLLFormula.prop q ∈ Γ then [itpA p S f b (B :: Γ) C]
            else if q = p then []
            else [(prop q).and (itpA p S f b (B :: Γ) C)]
          else []
      | .ifThen (.and A B) D =>
          if A.ifThen (B.ifThen D) ∈ Γ then []
          else if A.ifThen (B.ifThen D) ∈ S then
            [itpA p S f b (A.ifThen (B.ifThen D) :: Γ) C]
          else []
      | .ifThen (.or A B) D =>
          if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then []
          else if (A.ifThen D ∈ Γ ∨ A.ifThen D ∈ S) ∧
              (B.ifThen D ∈ Γ ∨ B.ifThen D ∈ S) then
            [itpA p S f b (A.ifThen D :: B.ifThen D :: Γ) C]
          else []
      | .ifThen (.ifThen A B) D =>
          if D ∈ Γ then []
          else if D ∈ S then
            if B.ifThen D ∈ Γ then
              if (A.ifThen B).ifThen D ∈ S then
                match b with
                | 0 => []
                | b' + 1 =>
                    [((itpE p S f b' Γ).ifThen
                        (itpA p S f b' Γ (A.ifThen B))).and
                      (itpA p S f b (D :: Γ) C)]
              else []
            else if B.ifThen D ∈ S then
              [(((itpE p S f b (B.ifThen D :: Γ)).ifThen
                  (itpA p S f b (B.ifThen D :: Γ) (A.ifThen B)))).and
                (itpA p S f b (D :: Γ) C)]
            else []
          else []
      | .ifThen (.somehow A) B =>
          if B ∈ Γ then []
          else if B ∈ S then
            (if A.somehow.ifThen B ∈ S then
              match b with
              | 0 => []
              | b' + 1 =>
                  [(itpA p S f b' Γ A).and
                     (itpA p S f b (B :: Γ) C),
                   (((itpE p S f b' Γ).ifThen
                       (itpA p S f b' Γ A.somehow)).somehow).and
                     (itpA p S f b (B :: Γ) C)]
            else [])
            ++ Γ.filterMap (fun X => match X with
                | .somehow x =>
                    if x ∈ Γ ∨ x ∉ S then none
                    else some (((((itpE p S f b (x :: Γ)).ifThen
                        (itpA p S f b (x :: Γ) A.somehow)).somehow)).and
                      (itpA p S f b (B :: Γ) C))
                | _ => none)
          else []
      | .somehow χ => (match C with
            | .somehow _ =>
                if χ ∈ Γ ∨ χ ∉ S then []
                else
                  [((itpE p S f b (χ :: Γ)).ifThen
                      (itpA p S f b (χ :: Γ) C)).somehow]
            | _ => [])
      | _ => [])

/-- The undecorated disjunct table (`others`) of `itpA p S (f+1) b Γ C`. -/
private def itpAoth (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  itpAgoal p S f b Γ C ++ itpAenv p S f b Γ C

/-- The full disjunct table of `itpA p S (f+1) b Γ C`, including the
truncation disjunct for ◯-goals. -/
private def itpAfull (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  match C with
  | .somehow _ =>
      itpAoth p S f b Γ C ++
        (if (itpAoth p S f b Γ C).isEmpty then []
         else match b with
           | 0 => []
           | b' + 1 =>
               [((itpE p S f b' Γ).ifThen
                   (orAll (itpAoth p S f b Γ C))).somehow])
  | _ => itpAoth p S f b Γ C

/-- One-level unfolding of `itpA` at successor fuel. -/
private theorem itpA_succ (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula) :
    itpA p S (f + 1) b Γ C = orAll (itpAfull p S f b Γ C) := rfl

/-! ### Member-wise mapping helpers -/

/-- Conjunction-table monotonicity from a member-wise mapping. -/
private theorem andAll_map {l L : List PLLFormula}
    (hmap : ∀ φ ∈ l, ∃ ψ ∈ L, G4c [ψ] φ) : G4c [andAll L] (andAll l) := by
  refine G4c.andAll_intro ?_
  intro φ hφ
  obtain ⟨ψ, hψ, hd⟩ := hmap φ hφ
  exact G4c.andAll_elim hψ hd

/-- Disjunction-table monotonicity from a member-wise mapping. -/
private theorem orAll_map {l L : List PLLFormula}
    (hmap : ∀ φ ∈ l, ∃ ψ ∈ L, G4c [φ] ψ) : G4c [orAll l] (orAll L) := by
  refine G4c.orAll_elim ?_
  intro φ hφ
  obtain ⟨ψ, hψ, hd⟩ := hmap φ hφ
  exact G4c.orAll_intro hψ hd

/-- Append two member-wise mappings. -/
private theorem map_append {l₁ l₂ L₁ L₂ : List PLLFormula}
    (h₁ : ∀ φ ∈ l₁, ∃ ψ ∈ L₁, G4c [φ] ψ)
    (h₂ : ∀ φ ∈ l₂, ∃ ψ ∈ L₂, G4c [φ] ψ) :
    ∀ φ ∈ l₁ ++ l₂, ∃ ψ ∈ L₁ ++ L₂, G4c [φ] ψ := by
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · obtain ⟨ψ, hψ, hd⟩ := h₁ φ hφ
    exact ⟨ψ, List.mem_append.mpr (Or.inl hψ), hd⟩
  · obtain ⟨ψ, hψ, hd⟩ := h₂ φ hφ
    exact ⟨ψ, List.mem_append.mpr (Or.inr hψ), hd⟩

/-- The ◯-goal disjunction with its truncation disjunct: a member-wise
mapping on the `others` plus a contravariant feed for the truncation
guard whenever the low-side truncation is live. -/
private theorem itpAfull_box_map {p : String} {S : Finset PLLFormula}
    {f₁ b₁ f₂ b₂ : Nat} {Γ : List PLLFormula} {D : PLLFormula}
    (hoth : ∀ φ ∈ itpAoth p S f₁ b₁ Γ (D.somehow),
        ∃ ψ ∈ itpAoth p S f₂ b₂ Γ (D.somehow), G4c [φ] ψ)
    (htr : ∀ b₁', b₁ = b₁' + 1 → ∃ b₂', b₂ = b₂' + 1 ∧
        G4c [itpE p S f₂ b₂' Γ] (itpE p S f₁ b₁' Γ)) :
    G4c [orAll (itpAfull p S f₁ b₁ Γ (D.somehow))]
        (orAll (itpAfull p S f₂ b₂ Γ (D.somehow))) := by
  simp only [itpAfull]
  refine G4c.orAll_elim ?_
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · obtain ⟨ψ, hψ, hd⟩ := hoth φ hφ
    exact G4c.orAll_intro (List.mem_append.mpr (Or.inl hψ)) hd
  · by_cases h1 : (itpAoth p S f₁ b₁ Γ (D.somehow)).isEmpty = true
    · rw [if_pos h1] at hφ; cases hφ
    · rw [if_neg h1] at hφ
      cases b₁ with
      | zero => cases hφ
      | succ b₁' =>
          rcases List.mem_singleton.mp hφ with rfl
          obtain ⟨b₂', rfl, hE⟩ := htr b₁' rfl
          have h2 : ¬ (itpAoth p S f₂ (b₂' + 1) Γ (D.somehow)).isEmpty = true := by
            intro h2
            have h2' : itpAoth p S f₂ (b₂' + 1) Γ (D.somehow) = [] := by
              simpa using h2
            cases hl : itpAoth p S f₁ (b₁' + 1) Γ (D.somehow) with
            | nil => rw [hl] at h1; simp at h1
            | cons a t =>
                obtain ⟨ψ, hψ, -⟩ := hoth a (by rw [hl]; exact .head _)
                rw [h2'] at hψ; cases hψ
          refine G4c.orAll_intro ?_ (box_mono (imp_mono hE (orAll_map hoth)))
          refine List.mem_append.mpr (Or.inr ?_)
          rw [if_neg h2]
          exact .head _

/-- Full-table monotonicity: dispatch on the goal shape (the
truncation disjunct exists only for ◯-goals). -/
private theorem itpAfull_map {p : String} {S : Finset PLLFormula}
    {f₁ b₁ f₂ b₂ : Nat} {Γ : List PLLFormula} {C : PLLFormula}
    (hoth : ∀ φ ∈ itpAoth p S f₁ b₁ Γ C,
        ∃ ψ ∈ itpAoth p S f₂ b₂ Γ C, G4c [φ] ψ)
    (htr : ∀ b₁', b₁ = b₁' + 1 → ∃ b₂', b₂ = b₂' + 1 ∧
        G4c [itpE p S f₂ b₂' Γ] (itpE p S f₁ b₁' Γ)) :
    G4c [orAll (itpAfull p S f₁ b₁ Γ C)]
        (orAll (itpAfull p S f₂ b₂ Γ C)) := by
  cases C with
  | somehow D => exact itpAfull_box_map hoth htr
  | prop q => simp only [itpAfull]; exact orAll_map hoth
  | falsePLL => simp only [itpAfull]; exact orAll_map hoth
  | and C₁ C₂ => simp only [itpAfull]; exact orAll_map hoth
  | or C₁ C₂ => simp only [itpAfull]; exact orAll_map hoth
  | ifThen C₁ C₂ => simp only [itpAfull]; exact orAll_map hoth

set_option maxHeartbeats 4000000 in
/-- Phase A's engine, one band step: if adjacent budgets `(n, n+1)` are
interderivable (in the absorb directions) at every fuel, so are
`(n+1, n+2)`.  A fuel induction structurally identical to
`itp_budget_mono`, with the E-direction reversed: the ungated component
pairs sit at `(n+1, n+2)` on the two sides — the inner fuel induction
hypothesis — while the budget-gated components sit one budget lower on
each side, i.e. at `(n, n+1)` — the previous band member, supplied by
`hprev` at all fuels (which is why the band induction must be outermost
and the fuel induction inner).  Both budgets are manifest successors
(`n+1`, `n+1+1`), so every budget gate is live and no `0`-case split is
needed: the `match` scrutinees reduce definitionally. -/
private theorem itp_absorb_step (p : String) (S : Finset PLLFormula)
    (n : Nat)
    (hprev : ∀ fuel,
      (∀ Γ, G4c [itpE p S fuel n Γ] (itpE p S fuel (n + 1) Γ)) ∧
      (∀ Γ C, G4c [itpA p S fuel (n + 1) Γ C] (itpA p S fuel n Γ C))) :
    ∀ (fuel : Nat),
    (∀ Γ, G4c [itpE p S fuel (n + 1) Γ] (itpE p S fuel (n + 1 + 1) Γ)) ∧
    (∀ Γ C, G4c [itpA p S fuel (n + 1 + 1) Γ C]
      (itpA p S fuel (n + 1) Γ C)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro Γ
        simp only [itpE]
        exact G4c.truePLL_intro _
      · intro Γ C
        simp only [itpA]
        exact G4c.botL (.head _)
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · -- [itpE p S (fuel+1) (n+1) Γ] ⊢ itpE p S (fuel+1) (n+1+1) Γ
        intro Γ
        rw [itpE_succ p S fuel (n + 1) Γ, itpE_succ p S fuel (n + 1 + 1) Γ]
        refine andAll_map ?_
        intro φ hφ
        simp only [itpEcls] at hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥ clause: identical at both budgets
            split at hφ
            next hbot =>
              rcases List.mem_singleton.mp hφ with rfl
              refine ⟨falsePLL, ?_, G4c.botL (.head _)⟩
              simp only [itpEcls]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inl (by rw [if_pos hbot]; exact .head _))))
            next => cases hφ
          · -- the atom clauses: identical at both budgets
            obtain ⟨F, hFΓ, heq⟩ := List.mem_filterMap.mp hφ
            cases F with
            | prop q =>
                simp only at heq
                split at heq
                next => cases heq
                next hq =>
                  injection heq with heq'
                  subst heq'
                  refine ⟨prop q, ?_, G4c.init (.head _)⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨prop q, hFΓ, ?_⟩))))
                  simp only
                  rw [if_neg hq]
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
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, ihE (A :: B :: Γ)⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.and B, hFΓ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, or_mono (ihE (A :: Γ)) (ihE (B :: Γ))⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.or B, hFΓ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next hg =>
                rcases List.mem_singleton.mp hin with rfl
                refine ⟨_, ?_, box_mono (ihE (χ :: Γ))⟩
                simp only [itpEcls]
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨χ.somehow, hFΓ, ?_⟩))
                simp only
                rw [if_neg hg]
                exact .head _
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine ⟨_, ?_, ihE (B :: Γ)⟩
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                          ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_,
                            imp_mono (G4c.init (.head _)) (ihE (B :: Γ))⟩
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                          exact .head _
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihE (A₁.ifThen (B₁.ifThen B) :: Γ)⟩
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                        ⟨(A₁.and B₁).ifThen B, hFΓ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihE (A₁.ifThen B :: B₁.ifThen B :: Γ)⟩
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                        ⟨(A₁.or B₁).ifThen B, hFΓ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDΓ =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABD =>
                          -- gated: sub-components at the previous band
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, imp_mono
                            (imp_mono ((hprev fuel).1 Γ)
                              ((hprev fuel).2 Γ (A₁.ifThen B₁)))
                            (ihE (B :: Γ))⟩
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩))
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_pos hBD, if_pos hABD]
                          exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, imp_mono
                            (imp_mono (ihE (B₁.ifThen B :: Γ))
                              (ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁)))
                            (ihE (B :: Γ))⟩
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩))
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_neg hBD, if_pos hBDS]
                          exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          -- gated: sub-components at the previous band
                          rcases List.mem_cons.mp hin with rfl | hin'
                          · refine ⟨_, ?_, imp_mono ((hprev fuel).2 Γ A₁)
                              (ihE (B :: Γ))⟩
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                            simp only
                            rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                            exact List.mem_append.mpr (Or.inl (.head _))
                          · rcases List.mem_singleton.mp hin' with rfl
                            refine ⟨_, ?_, imp_mono
                              (box_mono (imp_mono ((hprev fuel).1 Γ)
                                ((hprev fuel).2 Γ A₁.somehow)))
                              (ihE (B :: Γ))⟩
                            simp only [itpEcls]
                            refine List.mem_append.mpr (Or.inr
                              (List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                            simp only
                            rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                            exact List.mem_append.mpr
                              (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hg =>
                              injection heq with heq'
                              subst heq'
                              refine ⟨_, ?_, imp_mono
                                (box_mono (imp_mono (ihE (x :: Γ))
                                  (ihA (x :: Γ) A₁.somehow)))
                                (ihE (B :: Γ))⟩
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                              simp only
                              rw [if_neg hBΓ, if_pos hBS]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_filterMap.mpr ⟨x.somehow, hXΓ, ?_⟩))
                              simp only
                              rw [if_neg hg]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
      · -- [itpA p S (fuel+1) (n+1+1) Γ C] ⊢ itpA p S (fuel+1) (n+1) Γ C
        intro Γ C
        rw [itpA_succ p S fuel (n + 1 + 1) Γ C, itpA_succ p S fuel (n + 1) Γ C]
        have hGOAL : ∀ φ ∈ itpAgoal p S fuel (n + 1 + 1) Γ C,
            ∃ ψ ∈ itpAgoal p S fuel (n + 1) Γ C, G4c [φ] ψ := by
          intro φ hφ
          cases C with
          | prop q =>
              simp only [itpAgoal] at hφ ⊢
              split at hφ
              next => cases hφ
              next hq =>
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨prop q, ?_, G4c.init (.head _)⟩
                rw [if_neg hq]
                exact .head _
          | falsePLL =>
              simp only [itpAgoal] at hφ
              cases hφ
          | and C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_singleton.mp hφ with rfl
              exact ⟨_, .head _, and_mono (ihA Γ C₁) (ihA Γ C₂)⟩
          | or C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · exact ⟨_, .head _, ihA Γ C₁⟩
              · rcases List.mem_singleton.mp hφ' with rfl
                exact ⟨_, .tail _ (.head _), ihA Γ C₂⟩
          | ifThen C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              split at hφ
              next hpres =>
                -- gated: the guard at the previous band
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨_, ?_, imp_mono ((hprev fuel).1 (C₁ :: Γ))
                  (ihA (C₁ :: Γ) C₂)⟩
                rw [if_pos hpres]
                exact .head _
              next hpres =>
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨_, ?_, imp_mono (ihE (C₁ :: Γ))
                  (ihA (C₁ :: Γ) C₂)⟩
                rw [if_neg hpres]
                exact .head _
          | somehow D =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_singleton.mp hφ with rfl
              exact ⟨_, .head _,
                box_mono (imp_mono ((hprev fuel).1 Γ) (ihA Γ D))⟩
        have hENV : ∀ φ ∈ itpAenv p S fuel (n + 1 + 1) Γ C,
            ∃ ψ ∈ itpAenv p S fuel (n + 1) Γ C, G4c [φ] ψ := by
          intro φ hφ
          simp only [itpAenv] at hφ
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop q =>
              simp only at hin
              split at hin
              next hg =>
                rcases List.mem_singleton.mp hin with rfl
                refine ⟨truePLL, ?_, G4c.truePLL_intro _⟩
                simp only [itpAenv]
                refine List.mem_flatMap.mpr ⟨prop q, hFΓ, ?_⟩
                simp only
                rw [if_pos hg]
                exact .head _
              next => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, ihA (A :: B :: Γ) C⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨A.and B, hFΓ, ?_⟩
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, and_mono
                    (imp_mono (ihE (A :: Γ)) (ihA (A :: Γ) C))
                    (imp_mono (ihE (B :: Γ)) (ihA (B :: Γ) C))⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨A.or B, hFΓ, ?_⟩
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              · split at hin
                next => cases hin
                next hg =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, box_mono
                    (imp_mono (ihE (χ :: Γ)) (ihA (χ :: Γ) _))⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨χ.somehow, hFΓ, ?_⟩
                  simp only
                  rw [if_neg hg]
                  exact .head _
              all_goals cases hin
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine ⟨_, ?_, ihA (B :: Γ) C⟩
                        simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(prop q).ifThen B, hFΓ, ?_⟩
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, and_mono (G4c.init (.head _))
                            (ihA (B :: Γ) C)⟩
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hFΓ, ?_⟩
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                          exact .head _
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihA (A₁.ifThen (B₁.ifThen B) :: Γ) C⟩
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr
                        ⟨(A₁.and B₁).ifThen B, hFΓ, ?_⟩
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_,
                        ihA (A₁.ifThen B :: B₁.ifThen B :: Γ) C⟩
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr
                        ⟨(A₁.or B₁).ifThen B, hFΓ, ?_⟩
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDΓ =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABD =>
                          -- gated: sub-components at the previous band
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, and_mono
                            (imp_mono ((hprev fuel).1 Γ)
                              ((hprev fuel).2 Γ (A₁.ifThen B₁)))
                            (ihA (B :: Γ) C)⟩
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_pos hBD, if_pos hABD]
                          exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, and_mono
                            (imp_mono (ihE (B₁.ifThen B :: Γ))
                              (ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁)))
                            (ihA (B :: Γ) C)⟩
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_neg hBD, if_pos hBDS]
                          exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          -- gated: sub-components at the previous band
                          rcases List.mem_cons.mp hin with rfl | hin'
                          · refine ⟨_, ?_, and_mono ((hprev fuel).2 Γ A₁)
                              (ihA (B :: Γ) C)⟩
                            simp only [itpAenv]
                            refine List.mem_flatMap.mpr
                              ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                            simp only
                            rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                            exact List.mem_append.mpr (Or.inl (.head _))
                          · rcases List.mem_singleton.mp hin' with rfl
                            refine ⟨_, ?_, and_mono
                              (box_mono (imp_mono ((hprev fuel).1 Γ)
                                ((hprev fuel).2 Γ A₁.somehow)))
                              (ihA (B :: Γ) C)⟩
                            simp only [itpAenv]
                            refine List.mem_flatMap.mpr
                              ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                            simp only
                            rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                            exact List.mem_append.mpr
                              (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hg =>
                              injection heq with heq'
                              subst heq'
                              refine ⟨_, ?_, and_mono
                                (box_mono (imp_mono (ihE (x :: Γ))
                                  (ihA (x :: Γ) A₁.somehow)))
                                (ihA (B :: Γ) C)⟩
                              simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                              simp only
                              rw [if_neg hBΓ, if_pos hBS]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_filterMap.mpr ⟨x.somehow, hXΓ, ?_⟩))
                              simp only
                              rw [if_neg hg]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
        exact itpAfull_map (map_append hGOAL hENV)
          (fun b' hb => by
            obtain rfl : b' = n + 1 := by omega
            exact ⟨n, rfl, (hprev fuel).1 Γ⟩)

/-- Phase A: the upper band from the base, by induction on the slack;
each step is a fuel induction structurally parallel to
`itp_budget_mono` with the jump components consuming the previous
band member. -/
theorem itp_absorb_of_base (p : String) (S : Finset PLLFormula)
    (hbase : ∀ fuel,
      (∀ Γ, G4c [itpE p S fuel (bcap S) Γ] (itpE p S fuel (bcap S + 1) Γ)) ∧
      (∀ Γ C, G4c [itpA p S fuel (bcap S + 1) Γ C]
        (itpA p S fuel (bcap S) Γ C))) :
    ∀ (j fuel : Nat),
    (∀ Γ, G4c [itpE p S fuel (bcap S + j) Γ]
      (itpE p S fuel (bcap S + j + 1) Γ)) ∧
    (∀ Γ C, G4c [itpA p S fuel (bcap S + j + 1) Γ C]
      (itpA p S fuel (bcap S + j) Γ C)) := by
  intro j
  induction j with
  | zero => exact hbase
  | succ j jih => exact itp_absorb_step p S (bcap S + j) jih

/-- Packaged: all budgets above the cap are interderivable. -/
theorem itp_absorb (p : String) (S : Finset PLLFormula) {b : Nat}
    (hb : bcap S ≤ b) (fuel : Nat) :
    (∀ Γ, G4c [itpE p S fuel b Γ] (itpE p S fuel (b + 1) Γ)) ∧
    (∀ Γ C, G4c [itpA p S fuel (b + 1) Γ C] (itpA p S fuel b Γ C)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hb
  exact itp_absorb_of_base p S (itp_absorb_base p S) j fuel

/-! ### The boxed-position micro-obligations (exact annotations)

The cascade's only genuinely hard positions are under `◯(E ⇢ ·)`.
Candidate resolution: the guard `E` transports ambient into the box —
`laxL` the source box against the (◯-shaped) target, then the
antecedent `E` is available as ambient for the consequent map
(`box_guard_collapse`-style), and the repeat-shortcut's
budget-monotonicity move applies to the in-context inner value.
The two micro-lemmas below pin the annotation question: with the
source guard at `E @ b` and the target guard at `E @ b'` (`b' ≤ b`),
which direction of E-glue is needed, and does it stay inside the
band? -/

/-- γ-map, candidate form: source box at budgets (E@b, A@b), target
box at (E@b', A@b') with `b' + 1 = b`; the E-glue needed after
`laxL`+`laxR`+`impR` is `E@b'` ⊢-feeding the antecedent `E@b`, i.e.
budget-monotonicity of E in the LOW-to-HIGH direction — which is the
ABSORB direction, hence in-band only if `bcap S ≤ b'`. -/
theorem gamma_box_map (p : String) (S : Finset PLLFormula)
    (fuel b : Nat) (Γ : List PLLFormula) (g : PLLFormula)
    (hA : G4c ((itpE p S fuel b Γ) ::
                (itpA p S fuel b Γ g) :: [])
              (itpA p S fuel (b - 1) Γ g)) :
    G4c [((itpE p S fuel b Γ).ifThen (itpA p S fuel b Γ g)).somehow]
        (((itpE p S fuel (b - 1) Γ).ifThen
          (itpA p S fuel (b - 1) Γ g)).somehow) := by
  sorry

end PLLND
