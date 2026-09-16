/-
W-adaptation of `FRJ/ExtractV.lean` for the NEW calculus `FRJW`
(`FRJ/CalculusW.lean`): `lift` takes `⊃∉`'s place as a regular-premise
node — same index (`Unit`), same contributed pre-model (`preR d`) — and
every other clause is the V-clause re-proved over the W-family.

# `Mod(D)`: the labelled model extracted from a disproof

Section 3.1, transported to the family `FRJWr`/`FRJWi`.  The
whole `PreModel` layer — the data of `Mod(D)`, `leaf`/`leafF`/`join`,
`toKripke`, `join_force_comp`, `RootAbove` — is derivation-free and is
reused from `FRJ.Extract` verbatim.  Only the extraction functions and
their lemmas, which recurse over derivations, are re-defined here.

The three V-joins label their fresh root with the constructor's own
conclusion context `joinCtxAtVBase Ξs Θs F ++ kept` (resp.
`joinCtxOrVBase Ξs Θs ++ kept`), which is exactly what `hΓ` says `Γ'`
denotes, so `preR_root_lbl` closes as before.  `preR_closed` routes
through the `FRJ.V` step relation: the base-vs-kept split is discharged
once and for all inside `FRJ.V.lhs_subset_of_step` (every kept member
lies in `Θ^⊃∩ ⊆ Θs j`), so the closure argument here is verbatim the
paper one, with the `KeptChain` certificate handed to the step.
-/
import FRJ.StepW
import FRJ.Extract

namespace FRJ.W

open FRJ Form

/-! ## The regular sub-disproofs of an irregular disproof

`lift` and `◯∉` are the rules taking a regular premise (and `Ax^I◯`
mounts a leaf), so these are exactly those nodes.  They index the worlds
an irregular disproof contributes to the model built below it. -/

/-- The index of the regular sub-disproofs of an irregular disproof. -/
def RegIdx {G : Form} : {Ξ Θ : List Form} → {C : Form} → FRJWi G Ξ Θ C → Type
  | _, _, _, .axI _ _ _ _ => Empty
  | _, _, _, .andI1 d _ => RegIdx d
  | _, _, _, .andI2 d _ => RegIdx d
  | _, _, _, .orI d₁ d₂ _ _ _ _ _ => Sum (RegIdx d₁) (RegIdx d₂)
  | _, _, _, .impInI d _ _ _ _ _ _ => RegIdx d
  | _, _, _, .lift _ _ => Unit
  | _, _, _, .circNotIn _ _ _ _ => Unit
  | _, _, _, .axIC _ _ _ _ _ _ => Unit

/-- `RegIdx` has decidable equality, constructively. -/
instance regIdxDecEq {G : Form} : ∀ {Ξ Θ : List Form} {C : Form}
    (d : FRJWi G Ξ Θ C), DecidableEq (RegIdx d)
  | _, _, _, .axI _ _ _ _ => fun a _ => a.elim
  | _, _, _, .andI1 d _ => regIdxDecEq d
  | _, _, _, .andI2 d _ => regIdxDecEq d
  | _, _, _, .orI d₁ d₂ _ _ _ _ _ =>
      have _ := regIdxDecEq d₁
      have _ := regIdxDecEq d₂
      inferInstanceAs (DecidableEq (Sum _ _))
  | _, _, _, .impInI d _ _ _ _ _ _ => regIdxDecEq d
  | _, _, _, .lift _ _ => inferInstanceAs (DecidableEq Unit)
  | _, _, _, .circNotIn _ _ _ _ => inferInstanceAs (DecidableEq Unit)
  | _, _, _, .axIC _ _ _ _ _ _ => inferInstanceAs (DecidableEq Unit)

/-- An enumeration of `RegIdx`, constructively (no `Fintype.ofFinite`,
hence no `Classical.choice`). -/
def regIdxElems {G : Form} : ∀ {Ξ Θ : List Form} {C : Form}
    (d : FRJWi G Ξ Θ C), List (RegIdx d)
  | _, _, _, .axI _ _ _ _ => []
  | _, _, _, .andI1 d _ => regIdxElems d
  | _, _, _, .andI2 d _ => regIdxElems d
  | _, _, _, .orI d₁ d₂ _ _ _ _ _ =>
      (regIdxElems d₁).map Sum.inl ++ (regIdxElems d₂).map Sum.inr
  | _, _, _, .impInI d _ _ _ _ _ _ => regIdxElems d
  | _, _, _, .lift _ _ => [()]
  | _, _, _, .circNotIn _ _ _ _ => [()]
  | _, _, _, .axIC _ _ _ _ _ _ => [()]

theorem regIdxComplete {G : Form} : ∀ {Ξ Θ : List Form} {C : Form}
    (d : FRJWi G Ξ Θ C) (i : RegIdx d), i ∈ regIdxElems d
  | _, _, _, .axI _ _ _ _, i => i.elim
  | _, _, _, .andI1 d _, i => regIdxComplete d i
  | _, _, _, .andI2 d _, i => regIdxComplete d i
  | _, _, _, .orI d₁ d₂ _ _ _ _ _, i => by
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ =>
          exact List.mem_append_left _ (List.mem_map.mpr ⟨i₁, regIdxComplete d₁ i₁, rfl⟩)
      | .inr i₂ =>
          exact List.mem_append_right _ (List.mem_map.mpr ⟨i₂, regIdxComplete d₂ i₂, rfl⟩)
  | _, _, _, .impInI d _ _ _ _ _ _, i => regIdxComplete d i
  | _, _, _, .lift _ _, _ => List.mem_cons_self
  | _, _, _, .circNotIn _ _ _ _, _ => List.mem_cons_self
  | _, _, _, .axIC _ _ _ _ _ _, _ => List.mem_cons_self

/-! ### The index set of a join

A join contributes one world per regular sub-derivation of each premise,
so its index is `(j : Fin (n+1)) × RegIdx (prem j)`.  `PreModel.join`
needs that index enumerated; `List.finRange` and `regIdxElems` do it
without `Fintype`, hence without `Classical.choice`. -/

/-- Every `⟨j, i⟩` with `j` a premise and `i` a regular sub-derivation
of it. -/
def premIdxElems {G : Form} {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j)) :
    List ((j : Fin (n + 1)) × RegIdx (prem j)) :=
  (List.finRange (n + 1)).flatMap
    (fun j => (regIdxElems (prem j)).map (fun i => ⟨j, i⟩))

theorem premIdxComplete {G : Form} {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (prem : ∀ j, FRJWi G (Ξs j) (Θs j) (rhs j))
    (ji : (j : Fin (n + 1)) × RegIdx (prem j)) : ji ∈ premIdxElems prem := by
  obtain ⟨j, i⟩ := ji
  exact List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
    List.mem_map.mpr ⟨i, regIdxComplete (prem j) i, rfl⟩⟩


/-! ## `Mod(D)`, extracted

`Ax^R` contributes its single world; `∧` and `⊃∈` on regular sequents
change neither the world nor its label (they leave `Γ` alone), so they
pass the model through; a join creates the fresh root and places below
it every world contributed by its premises.  A V-join's fresh root is
labelled by its own conclusion context, base + kept. -/

mutual

/-- The pre-model of a regular derivation.  Its root is the paper's
`φ(σ)` for the root sequent `σ`.  A promise join places, besides the
premises' contributed models, one component per PROMISE premise, and
designates exactly those as the root's modal successors; a fallible join
places one declared fallible leaf and designates it. -/
def preR {G : Form} : {t : Tag} → {Γ : List Form} → {C : Form} → FRJWr G t Γ C → PreModel
  | _, _, _, .axR F _ _ _ => PreModel.leaf (rm (gAt G) F)
  | _, _, _, .andR1 d _ => preR d
  | _, _, _, .andR2 d _ => preR d
  | _, Γ, _, .impIn d _ _ => preR d
  | _, Γ, _, .circIn d _ _ => preR d
  | _, _, _, @FRJWr.joinAt _ n Ξs Θs _ F kept prem _ _ _ _ _ _ _ _ _ =>
      PreModel.join (premIdxElems prem) (premIdxComplete prem)
        (joinCtxAtVBase Ξs Θs F ++ kept)
        (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
        (fun _ => false)
  | _, _, _, @FRJWr.joinAtP _ n k Ξs Θs rhs F _ tps Δs Ds prem dps _ _ _ _ _ _ _ _ _ _ =>
      PreModel.join (sumElems (premIdxElems prem) (List.finRange (k + 1)))
        (sumElems_complete (premIdxComplete prem) List.mem_finRange)
        (joinCtxAtP Ξs Θs rhs F Δs)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun i => preR (dps i)))
        (Sum.elim (fun _ => false) (fun _ => true))
  | _, _, _, @FRJWr.joinAtF _ n Ξs Θs rhs F prem _ _ _ _ _ _ _ =>
      PreModel.join (sumElems (premIdxElems prem) [()])
        (sumElems_complete (premIdxComplete prem) (fun _ => List.mem_cons_self))
        (joinCtxAtF Ξs Θs rhs F)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ : Unit => PreModel.leafF (joinCtxAtF Ξs Θs rhs F)))
        (Sum.elim (fun _ => false) (fun _ => true))
  | _, _, _, @FRJWr.joinOr _ n Ξs Θs _ C₁ C₂ kept prem _ _ _ _ _ _ _ _ =>
      PreModel.join (premIdxElems prem) (premIdxComplete prem)
        (joinCtxOrVBase Ξs Θs ++ kept)
        (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
        (fun _ => false)
  | _, _, _, @FRJWr.joinOrP _ n k Ξs Θs rhs C₁ C₂ _ tps Δs Ds prem dps _ _ _ _ _ _ _ _ _ =>
      PreModel.join (sumElems (premIdxElems prem) (List.finRange (k + 1)))
        (sumElems_complete (premIdxComplete prem) List.mem_finRange)
        (joinCtxOrP Ξs Θs rhs Δs)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun i => preR (dps i)))
        (Sum.elim (fun _ => false) (fun _ => true))
  | _, _, _, @FRJWr.joinOrF _ n Ξs Θs rhs C₁ C₂ prem _ _ _ _ _ _ =>
      PreModel.join (sumElems (premIdxElems prem) [()])
        (sumElems_complete (premIdxComplete prem) (fun _ => List.mem_cons_self))
        (joinCtxOrF Ξs Θs rhs)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ : Unit => PreModel.leafF (joinCtxOrF Ξs Θs rhs)))
        (Sum.elim (fun _ => false) (fun _ => true))
  | _, _, _, @FRJWr.joinCirc _ n Ξs Θs _ Z kept prem _ _ _ _ _ _ _ _ =>
      PreModel.join (premIdxElems prem) (premIdxComplete prem)
        (joinCtxOrVBase Ξs Θs ++ kept)
        (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
        (fun _ => false)
  | _, _, _, @FRJWr.joinCircP _ n k Ξs Θs rhs Z tps Δs Ds prem dps _ _ _ _ _ _ _ _ _ =>
      PreModel.join (sumElems (premIdxElems prem) (List.finRange (k + 1)))
        (sumElems_complete (premIdxComplete prem) List.mem_finRange)
        (joinCtxOrP Ξs Θs rhs Δs)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun i => preR (dps i)))
        (Sum.elim (fun _ => false) (fun _ => true))

/-- The pre-models an irregular disproof contributes, one per
regular-premise (`lift`/`◯∉`) or `Ax^I◯` node. -/
def preI {G : Form} : {Ξ Θ : List Form} → {C : Form} →
    (d : FRJWi G Ξ Θ C) → RegIdx d → PreModel
  | _, _, _, .axI _ _ _ _, i => (i : Empty).elim
  | _, _, _, .andI1 d _, i => preI d i
  | _, _, _, .andI2 d _, i => preI d i
  | _, _, _, .orI d₁ d₂ _ _ _ _ _, i =>
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ => preI d₁ i₁
      | .inr i₂ => preI d₂ i₂
  | _, _, _, .impInI d _ _ _ _ _ _, i => preI d i
  | _, _, _, .lift d _, _ => preR d
  | _, _, _, .circNotIn d _ _ _, _ => preR d
  | _, Θ, _, .axIC _ _ _ _ _ _, _ => PreModel.leaf Θ

end


/-! ## The extracted data is a model

Three facts, in the order the paper needs them: the root of `Mod(D)` is
labelled by `D`'s own context; every world an irregular derivation
contributes is the `φ` of a regular sequent occurring in it; and hence
labels shrink modulo closure as one goes down — which is Lemma 3.4(iii)
transported to the model, and is exactly what makes `V` monotone. -/

/-- The root of `preR d` carries `d`'s own context.  (`∧` and `⊃∈` leave
`Γ` alone, and a join's root is labelled by its conclusion's context —
for the V-joins, base + kept, which is exactly what `hΓ` denotes.) -/
theorem preR_root_lbl {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJWr G t Γ C), (preR d).lbl (preR d).root ≐ Γ
  | _, _, _, .axR _ _ _ hΓ => hΓ.symm
  | _, _, _, .andR1 d _ => preR_root_lbl d
  | _, _, _, .andR2 d _ => preR_root_lbl d
  | _, _, _, .impIn d _ _ => preR_root_lbl d
  | _, _, _, .circIn d _ _ => preR_root_lbl d
  | _, _, _, .joinAt _ _ _ _ _ _ _ _ hΓ => hΓ.symm
  | _, _, _, .joinAtP _ _ _ _ _ _ _ _ _ _ hΓ => hΓ.symm
  | _, _, _, .joinAtF _ _ _ _ _ _ hΓ => hΓ.symm
  | _, _, _, .joinOr _ _ _ _ _ _ _ hΓ => hΓ.symm
  | _, _, _, .joinOrP _ _ _ _ _ _ _ _ _ hΓ => hΓ.symm
  | _, _, _, .joinOrF _ _ _ _ _ hΓ => hΓ.symm
  | _, _, _, .joinCirc _ _ _ _ _ _ _ hΓ => hΓ.symm
  | _, _, _, .joinCircP _ _ _ _ _ _ _ _ _ hΓ => hΓ.symm

/-- Every pre-model an irregular derivation contributes is the model of a
sequent occurring in it, and its root carries that sequent's left
formulas.  For the `lift`/`◯∉` nodes the sequent is the regular premise;
for `Ax^I◯` (which has no premise) it is the axiom's own irregular
sequent — its zone IS the mounted world's label. -/
theorem preI_spec {G : Form} : ∀ {Ξ Θ : List Form} {C : Form}
    (d : FRJWi G Ξ Θ C) (i : RegIdx d),
    ∃ s : Sequent, OccI d s ∧
      (preI d i).lbl (preI d i).root ≐ s.lhs
  | _, _, _, .axI _ _ _ _, i => (i : Empty).elim
  | _, _, _, .andI1 d _, i => by
      obtain ⟨s, hocc, hlbl⟩ := preI_spec d i
      exact ⟨s, .andI1 hocc, hlbl⟩
  | _, _, _, .andI2 d _, i => by
      obtain ⟨s, hocc, hlbl⟩ := preI_spec d i
      exact ⟨s, .andI2 hocc, hlbl⟩
  | _, _, _, .orI d₁ d₂ _ _ _ _ _, i => by
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ =>
          obtain ⟨s, hocc, hlbl⟩ := preI_spec d₁ i₁
          exact ⟨s, .orI₁ hocc, hlbl⟩
      | .inr i₂ =>
          obtain ⟨s, hocc, hlbl⟩ := preI_spec d₂ i₂
          exact ⟨s, .orI₂ hocc, hlbl⟩
  | _, _, _, .impInI d _ _ _ _ _ _, i => by
      obtain ⟨s, hocc, hlbl⟩ := preI_spec d i
      exact ⟨s, .impInI hocc, hlbl⟩
  | _, _, _, .lift d _, _ =>
      ⟨_, .lift (.root d), preR_root_lbl d⟩
  | _, _, _, .circNotIn d _ _ _, _ =>
      ⟨_, .circNotIn (.root d), preR_root_lbl d⟩
  | _, Θ, _, .axIC F _ _ _ _ _, _ =>
      ⟨.irr [] Θ (.circ F), .root _, CtxEq.refl _⟩

mutual

theorem preR_closed {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJWr G t Γ C), ClosedLbl (preR d)
  | _, _, _, .axR _ _ _ _ => fun _ _ _ X hX => .base hX
  | _, _, _, .andR1 d _ => preR_closed d
  | _, _, _, .andR2 d _ => preR_closed d
  | _, _, _, .impIn d _ _ => preR_closed d
  | _, _, _, .circIn d _ _ => preR_closed d
  | _, _, _, @FRJWr.joinAtP _ n k Ξs Θs rhs F t' tps Δs Ds prem dps hJ1 _ _ hJ7 _ _ _ _ _ _ => by
      intro w v hle X hX
      cases v with
      | none => cases hle with
        | root => exact .base hX
      | some jb =>
          obtain ⟨x, b⟩ := jb
          cases hle with
          | root =>
              cases x with
              | inl ji =>
                  obtain ⟨s', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
                  refine clo_trans (fun Y hY => ?_)
                    (lhs_clo_of_steps
                      ((occI_steps hocc).tail
                        ⟨_, Step.joinAtP (F := F) (Δs := Δs) ji.1 hJ1 (CtxEq.refl _)⟩) X hX)
                  refine preI_closed (prem ji.1) ji.2 _ _
                    ((preI (prem ji.1) ji.2).root_le b) Y ?_
                  exact (hlbl Y).mpr hY
              | inr i =>
                  refine clo_trans (fun Y hY => ?_) (joinCtxAtP_clo i X hX)
                  refine preR_closed (dps i) _ _ ((preR (dps i)).root_le b) Y ?_
                  exact (preR_root_lbl (dps i) Y).mpr hY
          | comp hab =>
              cases x with
              | inl ji => exact preI_closed (prem ji.1) ji.2 _ _ hab X hX
              | inr i => exact preR_closed (dps i) _ _ hab X hX
  | _, _, _, @FRJWr.joinAtF _ n Ξs Θs rhs F prem hJ1 _ _ _ _ _ _ => by
      intro w v hle X hX
      cases v with
      | none => cases hle with
        | root => exact .base hX
      | some jb =>
          obtain ⟨x, b⟩ := jb
          cases hle with
          | root =>
              cases x with
              | inl ji =>
                  obtain ⟨s', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
                  refine clo_trans (fun Y hY => ?_)
                    (lhs_clo_of_steps
                      ((occI_steps hocc).tail
                        ⟨_, Step.joinAtF (F := F) ji.1 hJ1 (CtxEq.refl _)⟩) X hX)
                  refine preI_closed (prem ji.1) ji.2 _ _
                    ((preI (prem ji.1) ji.2).root_le b) Y ?_
                  exact (hlbl Y).mpr hY
              | inr _ => exact .base hX
          | comp hab =>
              cases x with
              | inl ji => exact preI_closed (prem ji.1) ji.2 _ _ hab X hX
              | inr _ => exact .base hX
  | _, _, _, @FRJWr.joinOrP _ n k Ξs Θs rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 _ _ hJ7 _ _ _ _ _ => by
      intro w v hle X hX
      cases v with
      | none => cases hle with
        | root => exact .base hX
      | some jb =>
          obtain ⟨x, b⟩ := jb
          cases hle with
          | root =>
              cases x with
              | inl ji =>
                  obtain ⟨s', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
                  refine clo_trans (fun Y hY => ?_)
                    (lhs_clo_of_steps
                      ((occI_steps hocc).tail
                        ⟨_, Step.joinOrP (C₁ := C₁) (C₂ := C₂) (Δs := Δs) ji.1 hJ1 (CtxEq.refl _)⟩) X hX)
                  refine preI_closed (prem ji.1) ji.2 _ _
                    ((preI (prem ji.1) ji.2).root_le b) Y ?_
                  exact (hlbl Y).mpr hY
              | inr i =>
                  refine clo_trans (fun Y hY => ?_) (joinCtxOrP_clo i X hX)
                  refine preR_closed (dps i) _ _ ((preR (dps i)).root_le b) Y ?_
                  exact (preR_root_lbl (dps i) Y).mpr hY
          | comp hab =>
              cases x with
              | inl ji => exact preI_closed (prem ji.1) ji.2 _ _ hab X hX
              | inr i => exact preR_closed (dps i) _ _ hab X hX
  | _, _, _, @FRJWr.joinOrF _ n Ξs Θs rhs C₁ C₂ prem hJ1 _ _ _ _ _ => by
      intro w v hle X hX
      cases v with
      | none => cases hle with
        | root => exact .base hX
      | some jb =>
          obtain ⟨x, b⟩ := jb
          cases hle with
          | root =>
              cases x with
              | inl ji =>
                  obtain ⟨s', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
                  refine clo_trans (fun Y hY => ?_)
                    (lhs_clo_of_steps
                      ((occI_steps hocc).tail
                        ⟨_, Step.joinOrF (C₁ := C₁) (C₂ := C₂) ji.1 hJ1 (CtxEq.refl _)⟩) X hX)
                  refine preI_closed (prem ji.1) ji.2 _ _
                    ((preI (prem ji.1) ji.2).root_le b) Y ?_
                  exact (hlbl Y).mpr hY
              | inr _ => exact .base hX
          | comp hab =>
              cases x with
              | inl ji => exact preI_closed (prem ji.1) ji.2 _ _ hab X hX
              | inr _ => exact .base hX
  | _, _, _, @FRJWr.joinCircP _ n k Ξs Θs rhs Z tps Δs Ds prem dps hJ1 _ _ _ _ _ _ _ _ => by
      intro w v hle X hX
      cases v with
      | none => cases hle with
        | root => exact .base hX
      | some jb =>
          obtain ⟨x, b⟩ := jb
          cases hle with
          | root =>
              cases x with
              | inl ji =>
                  obtain ⟨s', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
                  refine clo_trans (fun Y hY => ?_)
                    (lhs_clo_of_steps
                      ((occI_steps hocc).tail
                        ⟨_, Step.joinCircP (Z := Z) (Δs := Δs) ji.1 hJ1 (CtxEq.refl _)⟩) X hX)
                  refine preI_closed (prem ji.1) ji.2 _ _
                    ((preI (prem ji.1) ji.2).root_le b) Y ?_
                  exact (hlbl Y).mpr hY
              | inr i =>
                  refine clo_trans (fun Y hY => ?_) (joinCtxOrP_clo i X hX)
                  refine preR_closed (dps i) _ _ ((preR (dps i)).root_le b) Y ?_
                  exact (preR_root_lbl (dps i) Y).mpr hY
          | comp hab =>
              cases x with
              | inl ji => exact preI_closed (prem ji.1) ji.2 _ _ hab X hX
              | inr i => exact preR_closed (dps i) _ _ hab X hX
  | _, _, _, @FRJWr.joinCirc _ n Ξs Θs rhs Z kept prem hJ1 _ _ hkc _ _ _ _ => by
      intro w v hle X hX
      cases v with
      | none => cases hle with
        | root => exact .base hX
      | some jb =>
          obtain ⟨ji, b⟩ := jb
          cases hle with
          | root =>
              obtain ⟨s', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
              refine clo_trans (fun Y hY => ?_)
                (lhs_clo_of_steps
                  ((occI_steps hocc).tail
                    ⟨_, Step.joinCirc (Z := Z) ji.1 hJ1 hkc (CtxEq.refl _)⟩) X hX)
              refine preI_closed (prem ji.1) ji.2 _ _
                ((preI (prem ji.1) ji.2).root_le b) Y ?_
              rw [hlbl]; exact hY
          | comp hab => exact preI_closed (prem _) _ _ _ hab X hX
  | _, _, _, @FRJWr.joinAt _ n Ξs Θs rhs F kept prem hJ1 _ _ hkc _ _ _ _ _ => by
      intro w v hle X hX
      cases v with
      | none => cases hle with
        | root => exact .base hX
      | some jb =>
          obtain ⟨ji, b⟩ := jb
          cases hle with
          | root =>
              obtain ⟨s', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
              refine clo_trans (fun Y hY => ?_)
                (lhs_clo_of_steps
                  ((occI_steps hocc).tail
                    ⟨_, Step.joinAt (F := F) ji.1 hJ1 hkc (CtxEq.refl _)⟩) X hX)
              refine preI_closed (prem ji.1) ji.2 _ _
                ((preI (prem ji.1) ji.2).root_le b) Y ?_
              rw [hlbl]; exact hY
          | comp hab => exact preI_closed (prem _) _ _ _ hab X hX
  | _, _, _, @FRJWr.joinOr _ n Ξs Θs rhs C₁ C₂ kept prem hJ1 _ _ hkc _ _ _ _ => by
      intro w v hle X hX
      cases v with
      | none => cases hle with
        | root => exact .base hX
      | some jb =>
          obtain ⟨ji, b⟩ := jb
          cases hle with
          | root =>
              obtain ⟨s', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
              refine clo_trans (fun Y hY => ?_)
                (lhs_clo_of_steps
                  ((occI_steps hocc).tail
                    ⟨_, Step.joinOr (C₁ := C₁) (C₂ := C₂) ji.1 hJ1 hkc (CtxEq.refl _)⟩) X hX)
              refine preI_closed (prem ji.1) ji.2 _ _
                ((preI (prem ji.1) ji.2).root_le b) Y ?_
              rw [hlbl]; exact hY
          | comp hab => exact preI_closed (prem _) _ _ _ hab X hX

theorem preI_closed {G : Form} : ∀ {Ξ Θ : List Form} {C : Form}
    (d : FRJWi G Ξ Θ C) (i : RegIdx d), ClosedLbl (preI d i)
  | _, _, _, .axI _ _ _ _, i => (i : Empty).elim
  | _, _, _, .andI1 d _, i => preI_closed d i
  | _, _, _, .andI2 d _, i => preI_closed d i
  | _, _, _, .orI d₁ d₂ _ _ _ _ _, i => by
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ => exact preI_closed d₁ i₁
      | .inr i₂ => exact preI_closed d₂ i₂
  | _, _, _, .impInI d _ _ _ _ _ _, i => preI_closed d i
  | _, _, _, .lift d _, _ => preR_closed d
  | _, _, _, .circNotIn d _ _ _, _ => preR_closed d
  | _, _, _, .axIC _ _ _ _ _ _, _ => fun _ _ _ X hX => .base hX

end


/-! ## `Mod(D)` as a Kripke model -/

/-- The model extracted from a regular derivation, `Mod(D)`. -/
def modR {G : Form} {t : Tag} {Γ : List Form} {C : Form} (d : FRJWr G t Γ C) : Kripke :=
  (preR d).toKripke (preR_closed d)

@[simp] theorem modR_V {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJWr G t Γ C) (w : (preR d).W) (p : String) :
    (modR d).V w p ↔ (Form.atom p ∈ (preR d).lbl w ∨ (preR d).fal w) := Iff.rfl

@[simp] theorem modR_root {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJWr G t Γ C) : (modR d).root = (preR d).root := rfl

@[simp] theorem modR_le {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJWr G t Γ C)
    (w v : (preR d).W) : (modR d).le w v ↔ (preR d).le w v := Iff.rfl


end FRJ.W
