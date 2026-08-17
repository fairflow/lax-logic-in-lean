/-
# `Mod(D)`: the labelled model extracted from a derivation

Section 3.1.  The paper's model is `Mod(D) = ⟨PS(D), ≤, ρ, V⟩` with
`V(σ) = Lhs(σ) ∩ PV`, and it justifies that this is a Kripke model by

  "by Lemma 3.4(iii) and (Cl5), `σ₁ ≤ σ₂` implies `V(σ₁) ⊆ V(σ₂)`,
   hence the definition of `V` is sound."

So the labelling of worlds by `Lhs` is not bookkeeping we add: it is what
makes `V` monotone, and hence what makes `Mod(D)` a model at all.  An
`LModel` is therefore a Kripke model together with

* `lbl`     — `Lhs(σ)` at each world,
* `val_eq`  — `V(σ) = Lhs(σ) ∩ PV`, the paper's definition of `V`,
* `lbl_clo` — Lemma 3.4(iii) transported to the model order.

What is deliberately NOT here is `∀ w, w ⊩ lbl w`.  That is Lemma
3.9(i) at p-sequents, i.e. part of what the soundness proof concludes,
and it is proved as a theorem rather than carried as a field.
-/
import FRJ.Step
import FRJ.Model

namespace FRJ

open Form



/-! ## Pre-models: the data of `Mod(D)`, before its valuation is justified

`Kripke` demands `V_mono`, but for `Mod(D)` that fact *is* Lemma
3.4(iii) applied to the model being defined — so it cannot be supplied
while defining it.  We therefore build the data first (worlds, order,
labels), prove `lbl_clo` of it afterwards by induction, and only then
package it as a Kripke model with `V(σ) = Lhs(σ) ∩ PV`. -/

/-- The data of an extracted model: a finite poset with a minimum, each
world labelled by the left formulas of its p-sequent. -/
structure PreModel where
  W : Type
  elems : List W
  complete : ∀ w, w ∈ elems
  decEq : DecidableEq W
  le : W → W → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  /-- the order is decidable: what keeps the extracted model computable,
  and hence the development free of `Classical.choice`. -/
  decLe : ∀ a b, Decidable (le a b)
  root : W
  root_le : ∀ a, le root a
  lbl : W → List Form
  /-- the modal relation, DECLARED BY THE DERIVATION: a join wires its
  fresh root to the roots of its promise components.  (Before the promise
  rules, `rm` was the uniform `Eq`, which fixed the identity nucleus; see
  `docs/frj-w3.md` §6a.) -/
  rm : W → W → Prop
  rm_refl : ∀ a, rm a a
  rm_trans : ∀ {a b c}, rm a b → rm b c → rm a c
  rm_sub : ∀ {a b}, rm a b → le a b
  decRm : ∀ a b, Decidable (rm a b)
  /-- the fallible worlds: only the declared fallible leaves of `⋈^⊥`. -/
  fal : W → Prop
  fal_mono : ∀ {a b}, le a b → fal a → fal b
  decFal : ∀ a, Decidable (fal a)

attribute [instance] PreModel.decEq

/-- The order on a fresh root placed below a disjoint union. -/
inductive PJLe {ι : Type} (Ms : ι → PreModel) :
    Option ((i : ι) × (Ms i).W) → Option ((i : ι) × (Ms i).W) → Prop
  | root (x : Option ((i : ι) × (Ms i).W)) : PJLe Ms none x
  | comp {i : ι} {a b : (Ms i).W} : (Ms i).le a b → PJLe Ms (some ⟨i, a⟩) (some ⟨i, b⟩)

/-- The modal relation of a join: each component keeps its own `rm`, and
the fresh root sees — besides itself — exactly the `rm`-cones of the
roots of the components `iP` designates as its PROMISES. -/
inductive PJRm {ι : Type} (Ms : ι → PreModel) (iP : ι → Bool) :
    Option ((i : ι) × (Ms i).W) → Option ((i : ι) × (Ms i).W) → Prop
  | rroot : PJRm Ms iP none none
  | prom {i : ι} {a : (Ms i).W} (hi : iP i = true)
      (hra : (Ms i).rm (Ms i).root a) :
      PJRm Ms iP none (some ⟨i, a⟩)
  | comp {i : ι} {a b : (Ms i).W} : (Ms i).rm a b → PJRm Ms iP (some ⟨i, a⟩) (some ⟨i, b⟩)

namespace PreModel

/-- `Ax^R`: a single world, barren and infallible. -/
def leaf (Γ : List Form) : PreModel where
  W := Unit
  elems := [()]
  complete := fun _ => List.mem_cons_self
  decEq := inferInstance
  le := fun _ _ => True
  le_refl := fun _ => trivial
  le_trans := fun _ _ => trivial
  le_antisymm := fun {a b} _ _ => Subsingleton.elim a b
  decLe := fun _ _ => isTrue trivial
  root := ()
  root_le := fun _ => trivial
  lbl := fun _ => Γ
  rm := fun _ _ => True
  rm_refl := fun _ => trivial
  rm_trans := fun _ _ => trivial
  rm_sub := fun _ => trivial
  decRm := fun _ _ => isTrue trivial
  fal := fun _ => False
  fal_mono := fun _ h => h
  decFal := fun _ => isFalse (fun h => h)

/-- The DECLARED FALLIBLE world of `⋈^⊥`: a single fallible world.  It is
the one world of the model that is not the `φ(σ)` of a p-sequent — a
fallible world forces everything, so it refutes nothing and can carry no
refutation premise (`docs/frj-lifting.md` §4); its label is the join's
own context, which it forces trivially. -/
def leafF (Γ : List Form) : PreModel where
  W := Unit
  elems := [()]
  complete := fun _ => List.mem_cons_self
  decEq := inferInstance
  le := fun _ _ => True
  le_refl := fun _ => trivial
  le_trans := fun _ _ => trivial
  le_antisymm := fun {a b} _ _ => Subsingleton.elim a b
  decLe := fun _ _ => isTrue trivial
  root := ()
  root_le := fun _ => trivial
  lbl := fun _ => Γ
  rm := fun _ _ => True
  rm_refl := fun _ => trivial
  rm_trans := fun _ _ => trivial
  rm_sub := fun _ => trivial
  decRm := fun _ _ => isTrue trivial
  fal := fun _ => True
  fal_mono := fun _ _ => trivial
  decFal := fun _ => isTrue trivial

/-- A join: a fresh root labelled `Γ₀`, below the disjoint union, with the
components `iP` designates wired to the root as its modal successors. -/
def join {ι : Type} [DecidableEq ι] (ιe : List ι) (ιc : ∀ i, i ∈ ιe)
    (Γ₀ : List Form) (Ms : ι → PreModel) (iP : ι → Bool) : PreModel where
  W := Option ((i : ι) × (Ms i).W)
  elems := none :: ιe.flatMap (fun i => ((Ms i).elems).map (fun a => some ⟨i, a⟩))
  complete := by
    rintro (_ | ⟨i, a⟩)
    · exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i, ιc i, ?_⟩)
      exact List.mem_map.mpr ⟨a, (Ms i).complete a, rfl⟩
  decEq := inferInstance
  le := PJLe Ms
  le_refl := by
    rintro (_ | ⟨i, a⟩)
    · exact .root _
    · exact .comp ((Ms i).le_refl a)
  le_trans := by
    rintro _ _ _ (_ | ⟨hab⟩) h2
    · exact .root _
    · cases h2 with
      | comp hbc => exact .comp ((Ms _).le_trans hab hbc)
  le_antisymm := by
    rintro _ _ (_ | ⟨hab⟩) h2
    · cases h2 with
      | root => rfl
    · cases h2 with
      | comp hba => exact congrArg _ (Sigma.ext rfl (heq_of_eq ((Ms _).le_antisymm hab hba)))
  decLe := by
    rintro (_ | ⟨i, a⟩) y
    · exact isTrue (.root _)
    · cases y with
      | none => exact isFalse (fun h => by cases h)
      | some jb =>
          obtain ⟨j, b⟩ := jb
          by_cases hij : i = j
          · subst hij
            have : Decidable ((Ms i).le a b) := (Ms i).decLe a b
            exact decidable_of_iff ((Ms i).le a b)
              ⟨fun h => .comp h, fun h => by cases h; assumption⟩
          · exact isFalse (fun h => by cases h; exact hij rfl)
  root := none
  root_le := fun _ => .root _
  lbl := fun x => match x with
    | none => Γ₀
    | some ⟨i, a⟩ => (Ms i).lbl a
  rm := PJRm Ms iP
  rm_refl := by
    rintro (_ | ⟨i, a⟩)
    · exact .rroot
    · exact .comp ((Ms i).rm_refl a)
  rm_trans := by
    rintro _ _ _ h1 h2
    cases h1 with
    | rroot => exact h2
    | prom hi hra =>
        cases h2 with
        | comp hab => exact .prom hi ((Ms _).rm_trans hra hab)
    | comp hab =>
        cases h2 with
        | comp hbc => exact .comp ((Ms _).rm_trans hab hbc)
  rm_sub := by
    rintro _ _ h
    cases h with
    | rroot => exact .root _
    | prom hi hra => exact .root _
    | comp hab => exact .comp ((Ms _).rm_sub hab)
  decRm := by
    rintro (_ | ⟨i, a⟩) y
    · cases y with
      | none => exact isTrue .rroot
      | some jb =>
          obtain ⟨j, b⟩ := jb
          by_cases hj : iP j = true
          · have : Decidable ((Ms j).rm (Ms j).root b) := (Ms j).decRm _ b
            exact decidable_of_iff ((Ms j).rm (Ms j).root b)
              ⟨fun h => .prom hj h, fun h => by cases h; assumption⟩
          · exact isFalse (fun h => by cases h with | prom hi _ => exact hj hi)
    · cases y with
      | none => exact isFalse (fun h => by cases h)
      | some jb =>
          obtain ⟨j, b⟩ := jb
          by_cases hij : i = j
          · subst hij
            have : Decidable ((Ms i).rm a b) := (Ms i).decRm a b
            exact decidable_of_iff ((Ms i).rm a b)
              ⟨fun h => .comp h, fun h => by cases h; assumption⟩
          · exact isFalse (fun h => by cases h; exact hij rfl)
  fal := fun x => match x with
    | none => False
    | some ⟨i, a⟩ => (Ms i).fal a
  fal_mono := by
    rintro _ _ h hf
    cases h with
    | root x =>
        cases hf
    | comp hab => exact (Ms _).fal_mono hab hf
  decFal := by
    rintro (_ | ⟨i, a⟩)
    · exact isFalse (fun h => h)
    · exact (Ms i).decFal a

variable {ι : Type} [DecidableEq ι] {ιe : List ι} {ιc : ∀ i, i ∈ ιe}
  {Γ₀ : List Form} {Ms : ι → PreModel} {iP : ι → Bool}

theorem join_le_comp {i : ι} {a : (Ms i).W} {y : (join ιe ιc Γ₀ Ms iP).W}
    (h : (join ιe ιc Γ₀ Ms iP).le (some ⟨i, a⟩) y) :
    ∃ b : (Ms i).W, (Ms i).le a b ∧ y = some ⟨i, b⟩ := by
  cases h with
  | comp hab => exact ⟨_, hab, rfl⟩

/-- The modal analogue: everything modally above a component world stays
in the same component, with the component's own `rm`. -/
theorem join_rm_comp {i : ι} {a : (Ms i).W} {y : (join ιe ιc Γ₀ Ms iP).W}
    (h : (join ιe ιc Γ₀ Ms iP).rm (some ⟨i, a⟩) y) :
    ∃ b : (Ms i).W, (Ms i).rm a b ∧ y = some ⟨i, b⟩ := by
  cases h with
  | comp hab => exact ⟨_, hab, rfl⟩

/-- The modal successors of the fresh root: itself, or a world in the
`rm`-cone of a designated promise component's root. -/
theorem join_rm_root {y : (join ιe ιc Γ₀ Ms iP).W}
    (h : (join ιe ιc Γ₀ Ms iP).rm none y) :
    y = none ∨ ∃ (i : ι) (a : (Ms i).W),
      iP i = true ∧ (Ms i).rm (Ms i).root a ∧ y = some ⟨i, a⟩ := by
  cases h with
  | rroot => exact Or.inl rfl
  | prom hi hra => exact Or.inr ⟨_, _, hi, hra, rfl⟩

/-- With no designated promises the root is BARREN. -/
theorem join_rm_root_barren (hP : ∀ i, iP i = false) {y : (join ιe ιc Γ₀ Ms iP).W}
    (h : (join ιe ιc Γ₀ Ms iP).rm none y) : y = none := by
  rcases join_rm_root h with h | ⟨i, a, hi, -, -⟩
  · exact h
  · exact absurd hi (by simp [hP i])

/-- Package a pre-model as a Kripke model once `lbl_clo` is known: the
valuation is the paper's `V(σ) = Lhs(σ) ∩ PV`, and its monotonicity is
exactly Lemma 3.4(iii) together with (Cl5). -/
def toKripke (P : PreModel)
    (h : ∀ (w v : P.W), P.le w v → ∀ X ∈ P.lbl w, Clo (P.lbl v) X) : Kripke where
  W := P.W
  elems := P.elems
  complete := P.complete
  decEq := P.decEq
  le := P.le
  le_refl := P.le_refl
  le_trans := P.le_trans
  le_antisymm := P.le_antisymm
  root := P.root
  root_le := P.root_le
  -- fallible worlds validate every atom (`full_F` of the constraint
  -- semantics); at all other worlds the valuation is the paper's
  -- `V(σ) = Lhs(σ) ∩ PV`.
  V := fun w p => Form.atom p ∈ P.lbl w ∨ P.fal w
  V_mono := fun {a b} hle p hp => hp.elim
    (fun hp => Or.inl (clo_pv (h a b hle _ hp)))
    (fun hp => Or.inr (P.fal_mono hle hp))
  -- the modal relation and the fallible set are the pre-model's own,
  -- DECLARED BY THE DERIVATION (a promise join wires its root to its
  -- promise components; everything else is barren).
  Rm := P.rm
  rm_refl := P.rm_refl
  rm_trans := fun h₁ h₂ => P.rm_trans h₁ h₂
  sub_mi := fun h => P.rm_sub h
  Fal := P.fal
  fal_mono := fun hle hf => P.fal_mono hle hf
  fal_V := fun hf _ => Or.inr hf
  decLe := P.decLe
  decV := fun w p =>
    have : Decidable (P.fal w) := P.decFal w
    inferInstanceAs (Decidable (_ ∨ _))
  decRm := P.decRm
  decFal := P.decFal

@[simp] theorem toKripke_le (P : PreModel) (h) (w v : P.W) :
    (P.toKripke h).le w v ↔ P.le w v := Iff.rfl

@[simp] theorem toKripke_V (P : PreModel) (h) (w : P.W) (p : String) :
    (P.toKripke h).V w p ↔ (Form.atom p ∈ P.lbl w ∨ P.fal w) := Iff.rfl

@[simp] theorem toKripke_Rm (P : PreModel) (h) (w v : P.W) :
    (P.toKripke h).Rm w v ↔ P.rm w v := Iff.rfl

@[simp] theorem toKripke_Fal (P : PreModel) (h) (w : P.W) :
    (P.toKripke h).Fal w ↔ P.fal w := Iff.rfl

/-- **At a BARREN world the modality is invisible**: if the world's only
modal successor is itself, it refutes `◯A` as soon as it refutes `A`.
This is the soundness of `◯∈` at barren roots; the tag machinery
(`tag_cone`) extends it along promise chains.  (Before the promise rules
`rm` was equality everywhere and this held globally — the identity
nucleus, `docs/frj-w3.md` §6a.) -/
theorem toKripke_not_force_circ_of_barren (P : PreModel) (h) {a : P.W}
    (hbar : ∀ u, P.rm a u → u = a) {A : Form}
    (hA : ¬ (P.toKripke h).force a A) :
    ¬ (P.toKripke h).force a (.circ A) := by
  intro hf
  obtain ⟨c, hc, hcA⟩ := hf a ((P.toKripke h).le_refl a)
  exact hA ((hbar c hc) ▸ hcA)

end PreModel

/-! ## The regular sub-derivations of an irregular derivation

`⊃∉` is the only rule taking a regular premise, so these are exactly the
`⊃∉` nodes.  They index the worlds an irregular derivation contributes
to the model built below it. -/

/-- The index of the regular sub-derivations of an irregular derivation. -/
def RegIdx {G : Form} : {St Th : List Form} → {C : Form} → FRJi G St Th C → Type
  | _, _, _, .axI _ _ _ => Empty
  | _, _, _, .andI1 d _ => RegIdx d
  | _, _, _, .andI2 d _ => RegIdx d
  | _, _, _, .orI d₁ d₂ _ _ _ => Sum (RegIdx d₁) (RegIdx d₂)
  | _, _, _, .impInI d _ _ _ => RegIdx d
  | _, _, _, .impNotIn _ _ _ _ _ => Unit

/-- `RegIdx` has decidable equality, constructively. -/
instance regIdxDecEq {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJi G St Th C), DecidableEq (RegIdx d)
  | _, _, _, .axI _ _ _ => fun a _ => a.elim
  | _, _, _, .andI1 d _ => regIdxDecEq d
  | _, _, _, .andI2 d _ => regIdxDecEq d
  | _, _, _, .orI d₁ d₂ _ _ _ =>
      have _ := regIdxDecEq d₁
      have _ := regIdxDecEq d₂
      inferInstanceAs (DecidableEq (Sum _ _))
  | _, _, _, .impInI d _ _ _ => regIdxDecEq d
  | _, _, _, .impNotIn _ _ _ _ _ => inferInstanceAs (DecidableEq Unit)

/-- An enumeration of `RegIdx`, constructively (no `Fintype.ofFinite`,
hence no `Classical.choice`). -/
def regIdxElems {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJi G St Th C), List (RegIdx d)
  | _, _, _, .axI _ _ _ => []
  | _, _, _, .andI1 d _ => regIdxElems d
  | _, _, _, .andI2 d _ => regIdxElems d
  | _, _, _, .orI d₁ d₂ _ _ _ =>
      (regIdxElems d₁).map Sum.inl ++ (regIdxElems d₂).map Sum.inr
  | _, _, _, .impInI d _ _ _ => regIdxElems d
  | _, _, _, .impNotIn _ _ _ _ _ => [()]

theorem regIdxComplete {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJi G St Th C) (i : RegIdx d), i ∈ regIdxElems d
  | _, _, _, .axI _ _ _, i => i.elim
  | _, _, _, .andI1 d _, i => regIdxComplete d i
  | _, _, _, .andI2 d _, i => regIdxComplete d i
  | _, _, _, .orI d₁ d₂ _ _ _, i => by
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ =>
          exact List.mem_append_left _ (List.mem_map.mpr ⟨i₁, regIdxComplete d₁ i₁, rfl⟩)
      | .inr i₂ =>
          exact List.mem_append_right _ (List.mem_map.mpr ⟨i₂, regIdxComplete d₂ i₂, rfl⟩)
  | _, _, _, .impInI d _ _ _, i => regIdxComplete d i
  | _, _, _, .impNotIn _ _ _ _ _, _ => List.mem_cons_self

/-! ### The index set of a join

A join contributes one world per regular sub-derivation of each premise,
so its index is `(j : Fin (n+1)) × RegIdx (prem j)`.  `PreModel.join`
needs that index enumerated; `List.finRange` and `regIdxElems` do it
without `Fintype`, hence without `Classical.choice`. -/

/-- Every `⟨j, i⟩` with `j` a premise and `i` a regular sub-derivation
of it. -/
def premIdxElems {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (prem : ∀ j, FRJi G (stab j) (th j) (rhs j)) :
    List ((j : Fin (n + 1)) × RegIdx (prem j)) :=
  (List.finRange (n + 1)).flatMap
    (fun j => (regIdxElems (prem j)).map (fun i => ⟨j, i⟩))

theorem premIdxComplete {G : Form} {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form}
    (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
    (ji : (j : Fin (n + 1)) × RegIdx (prem j)) : ji ∈ premIdxElems prem := by
  obtain ⟨j, i⟩ := ji
  exact List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
    List.mem_map.mpr ⟨i, regIdxComplete (prem j) i, rfl⟩⟩


/-! ## `Mod(D)`, extracted

`Ax^R` contributes its single world; `∧` and `⊃∈` on regular sequents
change neither the world nor its label (they leave `Γ` alone), so they
pass the model through; a join creates the fresh root and places below
it every world contributed by its premises. -/

/-- The component list of a join with one extra component family `κ`
(the promises, or the fallible leaf). -/
def sumElems {ι κ : Type} (ie : List ι) (ke : List κ) : List (ι ⊕ κ) :=
  ie.map Sum.inl ++ ke.map Sum.inr

theorem sumElems_complete {ι κ : Type} {ie : List ι} {ke : List κ}
    (hι : ∀ i, i ∈ ie) (hκ : ∀ k, k ∈ ke) : ∀ x : ι ⊕ κ, x ∈ sumElems ie ke := by
  rintro (i | k)
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨i, hι i, rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨k, hκ k, rfl⟩)

mutual

/-- The pre-model of a regular derivation.  Its root is the paper's
`φ(σ)` for the root sequent `σ`.  A promise join places, besides the
premises' contributed models, one component per PROMISE premise, and
designates exactly those as the root's modal successors; a fallible join
places one declared fallible leaf and designates it. -/
def preR {G : Form} : {t : Tag} → {Γ : List Form} → {C : Form} → FRJr G t Γ C → PreModel
  | _, _, _, .axR F _ _ => PreModel.leaf (rm (gAt G) F)
  | _, _, _, .andR1 d _ => preR d
  | _, _, _, .andR2 d _ => preR d
  | _, _, _, .impIn d _ _ => preR d
  | _, _, _, .circIn d _ _ => preR d
  | _, _, _, @FRJr.joinAt _ n stab th rhs F prem _ _ _ _ _ _ =>
      PreModel.join (premIdxElems prem) (premIdxComplete prem)
        (joinCtxAt stab th rhs F)
        (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
        (fun _ => false)
  | _, _, _, @FRJr.joinAtP _ n k stab th rhs F _ tps Δs Ds prem dps _ _ _ _ _ _ _ _ =>
      PreModel.join (sumElems (premIdxElems prem) (List.finRange (k + 1)))
        (sumElems_complete (premIdxComplete prem) List.mem_finRange)
        (joinCtxAtP stab th rhs F Δs)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun i => preR (dps i)))
        (Sum.elim (fun _ => false) (fun _ => true))
  | _, _, _, @FRJr.joinAtF _ n stab th rhs F prem _ _ _ _ _ =>
      PreModel.join (sumElems (premIdxElems prem) [()])
        (sumElems_complete (premIdxComplete prem) (fun _ => List.mem_cons_self))
        (joinCtxAtF stab th rhs F)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ : Unit => PreModel.leafF (joinCtxAtF stab th rhs F)))
        (Sum.elim (fun _ => false) (fun _ => true))
  | _, _, _, @FRJr.joinOr _ n stab th rhs C₁ C₂ prem _ _ _ _ _ =>
      PreModel.join (premIdxElems prem) (premIdxComplete prem)
        (joinCtxOr stab th rhs)
        (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
        (fun _ => false)
  | _, _, _, @FRJr.joinOrP _ n k stab th rhs C₁ C₂ _ tps Δs Ds prem dps _ _ _ _ _ _ _ =>
      PreModel.join (sumElems (premIdxElems prem) (List.finRange (k + 1)))
        (sumElems_complete (premIdxComplete prem) List.mem_finRange)
        (joinCtxOrP stab th rhs Δs)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun i => preR (dps i)))
        (Sum.elim (fun _ => false) (fun _ => true))
  | _, _, _, @FRJr.joinOrF _ n stab th rhs C₁ C₂ prem _ _ _ _ =>
      PreModel.join (sumElems (premIdxElems prem) [()])
        (sumElems_complete (premIdxComplete prem) (fun _ => List.mem_cons_self))
        (joinCtxOrF stab th rhs)
        (Sum.elim
          (fun (ji : (j : Fin (n + 1)) × RegIdx (prem j)) => preI (prem ji.1) ji.2)
          (fun _ : Unit => PreModel.leafF (joinCtxOrF stab th rhs)))
        (Sum.elim (fun _ => false) (fun _ => true))

/-- The pre-models an irregular derivation contributes, one per `⊃∉`
node. -/
def preI {G : Form} : {St Th : List Form} → {C : Form} →
    (d : FRJi G St Th C) → RegIdx d → PreModel
  | _, _, _, .axI _ _ _, i => (i : Empty).elim
  | _, _, _, .andI1 d _, i => preI d i
  | _, _, _, .andI2 d _, i => preI d i
  | _, _, _, .orI d₁ d₂ _ _ _, i =>
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ => preI d₁ i₁
      | .inr i₂ => preI d₂ i₂
  | _, _, _, .impInI d _ _ _, i => preI d i
  | _, _, _, .impNotIn d _ _ _ _, _ => preR d

end


/-! ## The extracted data is a model

Three facts, in the order the paper needs them: the root of `Mod(D)` is
labelled by `D`'s own context; every world an irregular derivation
contributes is the `φ` of a regular sequent occurring in it; and hence
labels shrink modulo closure as one goes down — which is Lemma 3.4(iii)
transported to the model, and is exactly what makes `V` monotone. -/

/-- The root of `preR d` carries `d`'s own context.  (`∧` and `⊃∈` leave
`Γ` alone, and a join's root is labelled by its conclusion's context.) -/
theorem preR_root_lbl {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C), (preR d).lbl (preR d).root = Γ
  | _, _, _, .axR _ _ _ => rfl
  | _, _, _, .andR1 d _ => preR_root_lbl d
  | _, _, _, .andR2 d _ => preR_root_lbl d
  | _, _, _, .impIn d _ _ => preR_root_lbl d
  | _, _, _, .circIn d _ _ => preR_root_lbl d
  | _, _, _, .joinAt _ _ _ _ _ _ _ => rfl
  | _, _, _, .joinAtP _ _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, .joinAtF _ _ _ _ _ _ => rfl
  | _, _, _, .joinOr _ _ _ _ _ _ => rfl
  | _, _, _, .joinOrP _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, .joinOrF _ _ _ _ _ => rfl

/-- Every pre-model an irregular derivation contributes is the model of a
regular sequent occurring in it, and its root carries that sequent's
context. -/
theorem preI_spec {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJi G St Th C) (i : RegIdx d),
    ∃ (Γ' : List Form) (C' : Form), OccI d (.reg Γ' C') ∧
      (preI d i).lbl (preI d i).root = Γ'
  | _, _, _, .axI _ _ _, i => (i : Empty).elim
  | _, _, _, .andI1 d _, i => by
      obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec d i
      exact ⟨Γ', C', .andI1 hocc, hlbl⟩
  | _, _, _, .andI2 d _, i => by
      obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec d i
      exact ⟨Γ', C', .andI2 hocc, hlbl⟩
  | _, _, _, .orI d₁ d₂ _ _ _, i => by
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ =>
          obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec d₁ i₁
          exact ⟨Γ', C', .orI₁ hocc, hlbl⟩
      | .inr i₂ =>
          obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec d₂ i₂
          exact ⟨Γ', C', .orI₂ hocc, hlbl⟩
  | _, _, _, .impInI d _ _ _, i => by
      obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec d i
      exact ⟨Γ', C', .impInI hocc, hlbl⟩
  | _, _, _, .impNotIn d _ _ _ _, _ =>
      ⟨_, _, .impNotIn (.root d), preR_root_lbl d⟩

/-- Labels shrink modulo closure going down: Lemma 3.4(iii) in the
model. -/
abbrev ClosedLbl (P : PreModel) : Prop :=
  ∀ (w v : P.W), P.le w v → ∀ X ∈ P.lbl w, Clo (P.lbl v) X

mutual

theorem preR_closed {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C), ClosedLbl (preR d)
  | _, _, _, .axR _ _ _ => fun _ _ _ X hX => .base hX
  | _, _, _, .andR1 d _ => preR_closed d
  | _, _, _, .andR2 d _ => preR_closed d
  | _, _, _, .impIn d _ _ => preR_closed d
  | _, _, _, .circIn d _ _ => preR_closed d
  | _, _, _, @FRJr.joinAtP _ n k stab th rhs F t' tps Δs Ds prem dps hJ1 _ _ hJ7 _ _ _ _ => by
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
                  obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
                  refine clo_trans (fun Y hY => ?_)
                    (lhs_clo_of_steps
                      ((occI_steps hocc).tail
                        ⟨_, Step.joinAtP (F := F) (Δs := Δs) ji.1 hJ1⟩) X hX)
                  refine preI_closed (prem ji.1) ji.2 _ _
                    ((preI (prem ji.1) ji.2).root_le b) Y ?_
                  rw [hlbl]; exact hY
              | inr i =>
                  refine clo_trans (fun Y hY => ?_) (hJ7 i X hX)
                  refine preR_closed (dps i) _ _ ((preR (dps i)).root_le b) Y ?_
                  rw [preR_root_lbl (dps i)]; exact hY
          | comp hab =>
              cases x with
              | inl ji => exact preI_closed (prem ji.1) ji.2 _ _ hab X hX
              | inr i => exact preR_closed (dps i) _ _ hab X hX
  | _, _, _, @FRJr.joinAtF _ n stab th rhs F prem hJ1 _ _ _ _ => by
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
                  obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
                  refine clo_trans (fun Y hY => ?_)
                    (lhs_clo_of_steps
                      ((occI_steps hocc).tail
                        ⟨_, Step.joinAtF (F := F) ji.1 hJ1⟩) X hX)
                  refine preI_closed (prem ji.1) ji.2 _ _
                    ((preI (prem ji.1) ji.2).root_le b) Y ?_
                  rw [hlbl]; exact hY
              | inr _ => exact .base hX
          | comp hab =>
              cases x with
              | inl ji => exact preI_closed (prem ji.1) ji.2 _ _ hab X hX
              | inr _ => exact .base hX
  | _, _, _, @FRJr.joinOrP _ n k stab th rhs C₁ C₂ t' tps Δs Ds prem dps hJ1 _ _ hJ7 _ _ _ => by
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
                  obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
                  refine clo_trans (fun Y hY => ?_)
                    (lhs_clo_of_steps
                      ((occI_steps hocc).tail
                        ⟨_, Step.joinOrP (C₁ := C₁) (C₂ := C₂) (Δs := Δs) ji.1 hJ1⟩) X hX)
                  refine preI_closed (prem ji.1) ji.2 _ _
                    ((preI (prem ji.1) ji.2).root_le b) Y ?_
                  rw [hlbl]; exact hY
              | inr i =>
                  refine clo_trans (fun Y hY => ?_) (hJ7 i X hX)
                  refine preR_closed (dps i) _ _ ((preR (dps i)).root_le b) Y ?_
                  rw [preR_root_lbl (dps i)]; exact hY
          | comp hab =>
              cases x with
              | inl ji => exact preI_closed (prem ji.1) ji.2 _ _ hab X hX
              | inr i => exact preR_closed (dps i) _ _ hab X hX
  | _, _, _, @FRJr.joinOrF _ n stab th rhs C₁ C₂ prem hJ1 _ _ _ => by
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
                  obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
                  refine clo_trans (fun Y hY => ?_)
                    (lhs_clo_of_steps
                      ((occI_steps hocc).tail
                        ⟨_, Step.joinOrF (C₁ := C₁) (C₂ := C₂) ji.1 hJ1⟩) X hX)
                  refine preI_closed (prem ji.1) ji.2 _ _
                    ((preI (prem ji.1) ji.2).root_le b) Y ?_
                  rw [hlbl]; exact hY
              | inr _ => exact .base hX
          | comp hab =>
              cases x with
              | inl ji => exact preI_closed (prem ji.1) ji.2 _ _ hab X hX
              | inr _ => exact .base hX
  | _, _, _, @FRJr.joinAt _ n stab th rhs F prem hJ1 _ _ _ _ _ => by
      intro w v hle X hX
      cases v with
      | none => cases hle with
        | root => exact .base hX
      | some jb =>
          obtain ⟨ji, b⟩ := jb
          cases hle with
          | root =>
              obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
              refine clo_trans (fun Y hY => ?_)
                (lhs_clo_of_steps
                  ((occI_steps hocc).tail ⟨_, Step.joinAt (F := F) ji.1 hJ1⟩) X hX)
              refine preI_closed (prem ji.1) ji.2 _ _
                ((preI (prem ji.1) ji.2).root_le b) Y ?_
              rw [hlbl]; exact hY
          | comp hab => exact preI_closed (prem _) _ _ _ hab X hX
  | _, _, _, @FRJr.joinOr _ n stab th rhs C₁ C₂ prem hJ1 _ _ _ _ => by
      intro w v hle X hX
      cases v with
      | none => cases hle with
        | root => exact .base hX
      | some jb =>
          obtain ⟨ji, b⟩ := jb
          cases hle with
          | root =>
              obtain ⟨Γ', C', hocc, hlbl⟩ := preI_spec (prem ji.1) ji.2
              refine clo_trans (fun Y hY => ?_)
                (lhs_clo_of_steps
                  ((occI_steps hocc).tail
                    ⟨_, Step.joinOr (C₁ := C₁) (C₂ := C₂) ji.1 hJ1⟩) X hX)
              refine preI_closed (prem ji.1) ji.2 _ _
                ((preI (prem ji.1) ji.2).root_le b) Y ?_
              rw [hlbl]; exact hY
          | comp hab => exact preI_closed (prem _) _ _ _ hab X hX

theorem preI_closed {G : Form} : ∀ {St Th : List Form} {C : Form}
    (d : FRJi G St Th C) (i : RegIdx d), ClosedLbl (preI d i)
  | _, _, _, .axI _ _ _, i => (i : Empty).elim
  | _, _, _, .andI1 d _, i => preI_closed d i
  | _, _, _, .andI2 d _, i => preI_closed d i
  | _, _, _, .orI d₁ d₂ _ _ _, i => by
      match (i : Sum (RegIdx d₁) (RegIdx d₂)) with
      | .inl i₁ => exact preI_closed d₁ i₁
      | .inr i₂ => exact preI_closed d₂ i₂
  | _, _, _, .impInI d _ _ _, i => preI_closed d i
  | _, _, _, .impNotIn d _ _ _ _, _ => preR_closed d

end


/-! ## `Mod(D)` as a Kripke model -/

/-- The model extracted from a regular derivation, `Mod(D)`. -/
def modR {G : Form} {t : Tag} {Γ : List Form} {C : Form} (d : FRJr G t Γ C) : Kripke :=
  (preR d).toKripke (preR_closed d)

@[simp] theorem modR_V {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C) (w : (preR d).W) (p : String) :
    (modR d).V w p ↔ (Form.atom p ∈ (preR d).lbl w ∨ (preR d).fal w) := Iff.rfl

@[simp] theorem modR_root {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C) : (modR d).root = (preR d).root := rfl

@[simp] theorem modR_le {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJr G t Γ C)
    (w v : (preR d).W) : (modR d).le w v ↔ (preR d).le w v := Iff.rfl


/-! ## Forcing transfers to a component of a join

A component of `PreModel.join` is upward closed, so no formula changes
truth value there.  (Forcing depends only on the pre-model's order and
labels, not on which proof of `ClosedLbl` is used to package it, so the
two packagings may be chosen independently.) -/

theorem join_force_comp {ι : Type} [DecidableEq ι] {ιe : List ι}
    {ιc : ∀ i, i ∈ ιe} {Γ₀ : List Form} {Ms : ι → PreModel} {iP : ι → Bool}
    (h : ClosedLbl (PreModel.join ιe ιc Γ₀ Ms iP)) {i : ι}
    (h' : ClosedLbl (Ms i)) :
    ∀ (A : Form) (a : (Ms i).W),
      ((PreModel.join ιe ιc Γ₀ Ms iP).toKripke h).force (some ⟨i, a⟩) A ↔
        ((Ms i).toKripke h').force a A := by
  intro A
  induction A with
  | atom p => intro a; exact Iff.rfl
  | bot => intro a; exact Iff.rfl
  | and A B ihA ihB => intro a; simp only [Kripke.force_and, ihA, ihB]
  | or A B ihA ihB => intro a; simp only [Kripke.force_or, ihA, ihB]
  | imp A B ihA ihB =>
      intro a
      simp only [Kripke.force_imp]
      constructor
      · intro hf b hab hA
        exact (ihB b).mp (hf (some ⟨i, b⟩) (.comp hab) ((ihA b).mpr hA))
      · intro hf y hy hA
        obtain ⟨b, hab, hy'⟩ :=
          PreModel.join_le_comp (ιe := ιe) (ιc := ιc) (Γ₀ := Γ₀) (Ms := Ms) (iP := iP) hy
        rw [hy'] at hA ⊢
        exact (ihB b).mpr (hf b hab ((ihA b).mp hA))
  | circ A ihA =>
      -- each component keeps its own modal relation (`join_rm_comp`), so
      -- the witnesses transfer verbatim in both directions.
      intro a
      simp only [Kripke.force_circ]
      constructor
      · intro hf b hab
        obtain ⟨y, hmy, hy⟩ := hf (some ⟨i, b⟩) (.comp hab)
        obtain ⟨c, hbc, hy'⟩ :=
          PreModel.join_rm_comp (ιe := ιe) (ιc := ιc) (Γ₀ := Γ₀) (Ms := Ms) (iP := iP) hmy
        rw [hy'] at hy
        exact ⟨c, hbc, (ihA c).mp hy⟩
      · intro hf y hy
        obtain ⟨b, hab, hy'⟩ :=
          PreModel.join_le_comp (ιe := ιe) (ιc := ιc) (Γ₀ := Γ₀) (Ms := Ms) (iP := iP) hy
        obtain ⟨c, hbc, hc⟩ := hf b hab
        rw [hy']
        exact ⟨some ⟨i, c⟩, .comp hbc, (ihA c).mpr hc⟩

/-- The paper's `σ_p ≤ φ(σ₁)` placement, in the only form the soundness
proof uses it: the ROOT of a contributed model sits above `w`, with the
same formulas forced there. -/
def RootAbove (P : PreModel) (hP : ClosedLbl P) (w : P.W)
    (Q : PreModel) (hQ : ClosedLbl Q) : Prop :=
  ∃ v : P.W, P.le w v ∧
    ∀ A : Form, (P.toKripke hP).force v A ↔ (Q.toKripke hQ).force Q.root A


end FRJ
