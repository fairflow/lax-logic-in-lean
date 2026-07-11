import LaxLogic.PLLG4UIStab

/-!
# Uniform interpolation, phase 4: the truncated quantifiers (v3)

The v2 quantifiers (`PLLG4UI.lean`) are adequate at every fuel above
the consumer's height (`PLLG4UIAdq.lean`), but the fuel cannot be
eliminated by a stabilization argument: the A-side hits an off-by-one
cascade at same-set positions (`docs/ui-endgame.md`).  This file
rebuilds the definition so that no fuel is needed — uniformity holds
*by construction*:

* **omission** — context clauses whose mirrored premise is the
  conclusion's own sequent (all inserted pieces already present, same
  goal) are dropped; the adequacy proof already skips those steps
  (retention absorbs them), and the dropped clause is provably
  redundant *as a formula* (it is set-congruent to the whole);
* **jump budget** — v2's clause shapes are kept verbatim, including
  every `◯(E ⇢ A)`-guard, but each *same-context* recursive
  reference (the `impLLax` head/γ clauses, the `impLImp` side premise
  at a present piece, the `A13` guard at a present antecedent, and
  the `E`-components of the ◯-goal disjuncts) recurses at budget
  `b − 1`; context growth pays into the space defect instead.
  Premise-1 chains keep the context identical, so minimal consumers
  never need more budget than the space's jump-goal count; the
  absorption lemma makes budgets above that threshold provably
  interchangeable — a congruence, usable in any position;
* **N-truncation** — the self-referential ◯-goal disjunct is replaced
  by `◯(E ⇢ ⋁ other disjuncts)`; its consumption opens with `laxL`
  and modus ponens, its landing closes by identity after cutting in
  the induction hypothesis (the monad-multiplication move of
  `lax_fixpoint`).

Design lesson recorded from the first attempt (2026-07-11): an
*ambient-relative* equivalence such as the bare law
`◯(E ⇢ Z) ⊣⊢ ◯Z given E` (proved below as `box_guard_collapse` /
`box_guard_intro`, still useful at consumption sites) is NOT a
congruence and must not be applied inside negatively-occurring
subterms of the definition — the γ-clause antecedents have no
ambient `E` to redeem them, and on the gap-theorem context the
algebraic probe caught exactly that loss.  Budget-annotation is the
congruence-grade device; guards stay.

This file: the G4c-level proof engines, the measure layer, and the
definition.  The re-proved tower follows.
-/

open PLLFormula

namespace PLLND

/-! ### Guard absorption (the bare law)

`◯(E ⇢ Z)` and `◯Z` are interchangeable in any context that holds
`E`: collapse is retained modus ponens under the box, introduction is
monotonicity.  This is what lets the same-context clauses of the
truncated quantifiers drop the self-referential `E`-guards that v2
carried (and that made its recursion non-well-founded). -/

/-- Collapse: `E, ◯(E ⇢ Z) ⊢ ◯Z`. -/
theorem box_guard_collapse (E Z : PLLFormula) :
    G4c [E, (E.ifThen Z).somehow] Z.somehow := by
  refine G4c.laxL (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inl rfl)))) ?_
  -- E ⇢ Z, E, ◯(E ⇢ Z) ⊢ ◯Z: reorder and fire the context MP
  exact (G4c.laxR (G4c.mp E Z [(E.ifThen Z).somehow])).perm
    (List.Perm.swap _ _ _)

/-- Introduction: `◯Z ⊢ ◯(E ⇢ Z)`. -/
theorem box_guard_intro (E Z : PLLFormula) :
    G4c [Z.somehow] ((E.ifThen Z).somehow) :=
  box_mono (G4c.impR (G4c.identity_mem (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))

/-! ### laxL lifting

Consumption of the truncated ◯-goal disjunct: a boxed hypothesis may
be opened against a ◯-shaped goal (retention keeps the box). -/

/-- `X, Γ ⊢ ◯C  ⟹  ◯X, Γ ⊢ ◯C`. -/
theorem laxL_lift {X C : PLLFormula} {Γ : List PLLFormula}
    (d : G4c (X :: Γ) C.somehow) : G4c (X.somehow :: Γ) C.somehow :=
  G4c.laxL (List.mem_cons.mpr (Or.inl rfl))
    (((d.weaken X.somehow).perm (List.Perm.swap _ _ _)))

/-! ### The truncated quantifiers

`itpE p S fuel b Γ` / `itpA p S fuel b Γ C`.  Recursion structure:

* **space guards** — context-growing clauses driven by a `Γ`-formula
  fire only when their new pieces lie in the space `S` (a
  piece-closed finset fixed at instantiation); real runs always
  satisfy this, and it makes the growth pay strictly into
  `defect := (S \ Γ.toFinset).card`.  Goal-driven growth (`A13` at a
  fresh antecedent) needs no space guard: the goal-weight slot pays.
* **budget `b`** — every same-context recursive reference (`impLLax`
  head/γ, `impLImp` side premise at a present piece, `A13` at a
  present antecedent, the `E`-components of the ◯-goal disjuncts)
  recurses at `b − 1`; at `b = 0` those clauses are dropped (values
  below the jump-goal threshold are never consumed).
* **fuel** — a shadow parameter: every recursive call strictly
  decreases `mu := (defect + b)·(W₀+1) + goalweight` (`W₀` bounds the
  space's weights and the initial goal's), so above `mu` the fuel is
  syntactically irrelevant; the indifference lemma turns this into
  unfold equations for the packaged, fuel-free quantifiers.
-/

/-- Distance of the context set from the space: how many space
formulas the context has not yet absorbed.  Every space-guarded
context growth strictly decreases it. -/
def defect (S : Finset PLLFormula) (Γ : List PLLFormula) : Nat :=
  (S \ Γ.toFinset).card

theorem defect_cons_le (S : Finset PLLFormula) (x : PLLFormula)
    (Γ : List PLLFormula) : defect S (x :: Γ) ≤ defect S Γ := by
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_sdiff] at hy ⊢
  refine ⟨hy.1, fun hmem => hy.2 ?_⟩
  simp only [List.toFinset_cons, Finset.mem_insert]
  exact Or.inr hmem

theorem defect_cons_lt {S : Finset PLLFormula} {x : PLLFormula}
    {Γ : List PLLFormula} (hS : x ∈ S) (hΓ : x ∉ Γ) :
    defect S (x :: Γ) < defect S Γ := by
  have h1 : S \ (x :: Γ).toFinset = (S \ Γ.toFinset).erase x := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons,
      Finset.mem_insert, not_or]
    tauto
  rw [defect, h1]
  exact Finset.card_erase_lt_of_mem
    (Finset.mem_sdiff.mpr ⟨hS, fun h => hΓ (List.mem_toFinset.mp h)⟩)

theorem defect_cons_eq {S : Finset PLLFormula} {x : PLLFormula}
    {Γ : List PLLFormula} (hΓ : x ∈ Γ) :
    defect S (x :: Γ) = defect S Γ := by
  unfold defect
  congr 1
  ext y
  simp only [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_insert]
  constructor
  · rintro ⟨hyS, hy⟩; exact ⟨hyS, fun h => hy (Or.inr h)⟩
  · rintro ⟨hyS, hy⟩
    refine ⟨hyS, fun h => hy ?_⟩
    rcases h with rfl | h
    · exact List.mem_toFinset.mpr hΓ
    · exact h

theorem defect_le_of_subset {S : Finset PLLFormula}
    {Γ₁ Γ₂ : List PLLFormula} (h : Γ₁.toFinset ⊆ Γ₂.toFinset) :
    defect S Γ₂ ≤ defect S Γ₁ := by
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_sdiff] at hy ⊢
  exact ⟨hy.1, fun hmem => hy.2 (h hmem)⟩

/-- The recursion measure shadowed by the fuel parameter: `slot` is
`0` for `itpE` and the goal weight for `itpA`; `W0` bounds every goal
weight in play (the space's sup and the initial goal). -/
def mu (S : Finset PLLFormula) (W0 b slot : Nat)
    (Γ : List PLLFormula) : Nat :=
  (defect S Γ + b) * (W0 + 1) + slot

theorem mu_slot_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {Γ : List PLLFormula} (h : slot' < slot) :
    mu S W0 b slot' Γ < mu S W0 b slot Γ :=
  Nat.add_lt_add_left h _

theorem mu_jump_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {Γ : List PLLFormula} (h : slot' ≤ W0) :
    mu S W0 b slot' Γ < mu S W0 (b + 1) slot Γ := by
  unfold mu
  have h1 : (defect S Γ + b) * (W0 + 1) + slot' <
      (defect S Γ + (b + 1)) * (W0 + 1) := by
    have : (defect S Γ + (b + 1)) * (W0 + 1)
        = (defect S Γ + b) * (W0 + 1) + (W0 + 1) := by ring
    omega
  omega

theorem mu_growth_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {Γ Γ' : List PLLFormula} (hd : defect S Γ' < defect S Γ)
    (h : slot' ≤ W0) : mu S W0 b slot' Γ' < mu S W0 b slot Γ := by
  unfold mu
  have h1 : (defect S Γ' + b) * (W0 + 1) + slot' <
      (defect S Γ + b) * (W0 + 1) := by
    have h2 : (defect S Γ' + b) + 1 ≤ defect S Γ + b := by omega
    have h3 : ((defect S Γ' + b) + 1) * (W0 + 1) ≤
        (defect S Γ + b) * (W0 + 1) := Nat.mul_le_mul_right _ h2
    have : ((defect S Γ' + b) + 1) * (W0 + 1)
        = (defect S Γ' + b) * (W0 + 1) + (W0 + 1) := by ring
    omega
  omega

theorem mu_same_set_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {x : PLLFormula} {Γ : List PLLFormula} (hx : x ∈ Γ)
    (h : slot' < slot) : mu S W0 b slot' (x :: Γ) < mu S W0 b slot Γ := by
  unfold mu
  rw [defect_cons_eq hx]
  omega

/-- Weight bounds for jump goals extracted from a space formula. -/
theorem weight_le_of_mem_left {S : Finset PLLFormula} {W0 : Nat}
    (hW : S.sup PLLFormula.weight ≤ W0) {F : PLLFormula} (hF : F ∈ S) :
    F.weight ≤ W0 :=
  le_trans (Finset.le_sup hF) hW

mutual

/-- ∃-quantifier, truncated form (v3). -/
def itpE (p : String) (S : Finset PLLFormula) :
    Nat → Nat → List PLLFormula → PLLFormula
  | 0, _, _ => truePLL
  | fuel + 1, b, Γ =>
      andAll (
        (if falsePLL ∈ Γ then [falsePLL] else [])
        ++ Γ.filterMap (fun F => match F with
            | .prop q => if q = p then none else some (prop q)
            | _ => none)
        ++ Γ.flatMap (fun F => match F with
            | .and A B =>
                if A ∈ Γ ∧ B ∈ Γ then []
                else if (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) then
                  [itpE p S fuel b (A :: B :: Γ)]
                else []
            | .or A B =>
                if A ∈ Γ ∨ B ∈ Γ then []
                else if A ∈ S ∧ B ∈ S then
                  [(itpE p S fuel b (A :: Γ)).or (itpE p S fuel b (B :: Γ))]
                else []
            | .ifThen (.prop q) B =>
                if B ∈ Γ then []
                else if B ∈ S then
                  if PLLFormula.prop q ∈ Γ then [itpE p S fuel b (B :: Γ)]
                  else if q = p then []
                  else [(prop q).ifThen (itpE p S fuel b (B :: Γ))]
                else []
            | .ifThen (.and A B) D =>
                if A.ifThen (B.ifThen D) ∈ Γ then []
                else if A.ifThen (B.ifThen D) ∈ S then
                  [itpE p S fuel b (A.ifThen (B.ifThen D) :: Γ)]
                else []
            | .ifThen (.or A B) D =>
                if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then []
                else if (A.ifThen D ∈ Γ ∨ A.ifThen D ∈ S) ∧
                    (B.ifThen D ∈ Γ ∨ B.ifThen D ∈ S) then
                  [itpE p S fuel b (A.ifThen D :: B.ifThen D :: Γ)]
                else []
            | .ifThen (.ifThen A B) D =>
                if D ∈ Γ then []
                else if D ∈ S then
                  if B.ifThen D ∈ Γ then
                    if (A.ifThen B).ifThen D ∈ S then
                      match b with
                      | 0 => []
                      | b' + 1 =>
                          [((itpE p S fuel b' Γ).ifThen
                              (itpA p S fuel b' Γ (A.ifThen B))).ifThen
                            (itpE p S fuel b (D :: Γ))]
                    else []
                  else if B.ifThen D ∈ S then
                    [((itpE p S fuel b (B.ifThen D :: Γ)).ifThen
                        (itpA p S fuel b (B.ifThen D :: Γ) (A.ifThen B))).ifThen
                      (itpE p S fuel b (D :: Γ))]
                  else []
                else []
            | .ifThen (.somehow A) B =>
                if B ∈ Γ then []
                else if B ∈ S then
                  (if A.somehow.ifThen B ∈ S then
                    match b with
                    | 0 => []
                    | b' + 1 =>
                        [(itpA p S fuel b' Γ A).ifThen
                           (itpE p S fuel b (B :: Γ)),
                         (((itpE p S fuel b' Γ).ifThen
                             (itpA p S fuel b' Γ A.somehow)).somehow).ifThen
                           (itpE p S fuel b (B :: Γ))]
                  else [])
                  ++ Γ.filterMap (fun X => match X with
                      | .somehow x =>
                          if x ∈ Γ ∨ x ∉ S then none
                          else some ((((itpE p S fuel b (x :: Γ)).ifThen
                              (itpA p S fuel b (x :: Γ) A.somehow)).somehow).ifThen
                            (itpE p S fuel b (B :: Γ)))
                      | _ => none)
                else []
            | .somehow χ =>
                if χ ∈ Γ ∨ χ ∉ S then []
                else [(itpE p S fuel b (χ :: Γ)).somehow]
            | _ => []))

/-- ∀-quantifier, truncated form (v3). -/
def itpA (p : String) (S : Finset PLLFormula) :
    Nat → Nat → List PLLFormula → PLLFormula → PLLFormula
  | 0, _, _, _ => falsePLL
  | fuel + 1, b, Γ, C =>
      let env : List PLLFormula := Γ.flatMap (fun F => match F with
            | .prop q =>
                if q = p ∧ C = PLLFormula.prop p then [truePLL] else []
            | .and A B =>
                if A ∈ Γ ∧ B ∈ Γ then []
                else if (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) then
                  [itpA p S fuel b (A :: B :: Γ) C]
                else []
            | .or A B =>
                if A ∈ Γ ∨ B ∈ Γ then []
                else if A ∈ S ∧ B ∈ S then
                  [((itpE p S fuel b (A :: Γ)).ifThen
                      (itpA p S fuel b (A :: Γ) C)).and
                   ((itpE p S fuel b (B :: Γ)).ifThen
                      (itpA p S fuel b (B :: Γ) C))]
                else []
            | .ifThen (.prop q) B =>
                if B ∈ Γ then []
                else if B ∈ S then
                  if PLLFormula.prop q ∈ Γ then [itpA p S fuel b (B :: Γ) C]
                  else if q = p then []
                  else [(prop q).and (itpA p S fuel b (B :: Γ) C)]
                else []
            | .ifThen (.and A B) D =>
                if A.ifThen (B.ifThen D) ∈ Γ then []
                else if A.ifThen (B.ifThen D) ∈ S then
                  [itpA p S fuel b (A.ifThen (B.ifThen D) :: Γ) C]
                else []
            | .ifThen (.or A B) D =>
                if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then []
                else if (A.ifThen D ∈ Γ ∨ A.ifThen D ∈ S) ∧
                    (B.ifThen D ∈ Γ ∨ B.ifThen D ∈ S) then
                  [itpA p S fuel b (A.ifThen D :: B.ifThen D :: Γ) C]
                else []
            | .ifThen (.ifThen A B) D =>
                if D ∈ Γ then []
                else if D ∈ S then
                  if B.ifThen D ∈ Γ then
                    if (A.ifThen B).ifThen D ∈ S then
                      match b with
                      | 0 => []
                      | b' + 1 =>
                          [((itpE p S fuel b' Γ).ifThen
                              (itpA p S fuel b' Γ (A.ifThen B))).and
                            (itpA p S fuel b (D :: Γ) C)]
                    else []
                  else if B.ifThen D ∈ S then
                    [(((itpE p S fuel b (B.ifThen D :: Γ)).ifThen
                        (itpA p S fuel b (B.ifThen D :: Γ) (A.ifThen B)))).and
                      (itpA p S fuel b (D :: Γ) C)]
                  else []
                else []
            | .ifThen (.somehow A) B =>
                if B ∈ Γ then []
                else if B ∈ S then
                  (if A.somehow.ifThen B ∈ S then
                    match b with
                    | 0 => []
                    | b' + 1 =>
                        [(itpA p S fuel b' Γ A).and
                           (itpA p S fuel b (B :: Γ) C),
                         (((itpE p S fuel b' Γ).ifThen
                             (itpA p S fuel b' Γ A.somehow)).somehow).and
                           (itpA p S fuel b (B :: Γ) C)]
                  else [])
                  ++ Γ.filterMap (fun X => match X with
                      | .somehow x =>
                          if x ∈ Γ ∨ x ∉ S then none
                          else some (((((itpE p S fuel b (x :: Γ)).ifThen
                              (itpA p S fuel b (x :: Γ) A.somehow)).somehow)).and
                            (itpA p S fuel b (B :: Γ) C))
                      | _ => none)
                else []
            | .somehow χ => (match C with
                  | .somehow _ =>
                      if χ ∈ Γ ∨ χ ∉ S then []
                      else
                        [((itpE p S fuel b (χ :: Γ)).ifThen
                            (itpA p S fuel b (χ :: Γ) C)).somehow]
                  | _ => [])
            | _ => [])
      let goal : List PLLFormula := (match C with
            | .prop q => if q = p then [] else [prop q]
            | .falsePLL => []
            | .and C₁ C₂ =>
                [(itpA p S fuel b Γ C₁).and (itpA p S fuel b Γ C₂)]
            | .or C₁ C₂ => [itpA p S fuel b Γ C₁, itpA p S fuel b Γ C₂]
            | .ifThen C₁ C₂ =>
                if C₁ ∈ Γ then
                  match b with
                  | 0 => []
                  | b' + 1 =>
                      [(itpE p S fuel b' (C₁ :: Γ)).ifThen
                        (itpA p S fuel b (C₁ :: Γ) C₂)]
                else
                  [(itpE p S fuel b (C₁ :: Γ)).ifThen
                    (itpA p S fuel b (C₁ :: Γ) C₂)]
            | .somehow D =>
                match b with
                | 0 => []
                | b' + 1 =>
                    [((itpE p S fuel b' Γ).ifThen
                        (itpA p S fuel b Γ D)).somehow])
      let others := goal ++ env
      orAll (match C with
        | .somehow _ =>
            others ++
              (if others.isEmpty then []
               else match b with
                 | 0 => []
                 | b' + 1 =>
                     [((itpE p S fuel b' Γ).ifThen (orAll others)).somehow])
        | _ => others)

end

end PLLND
