import LaxLogic.PLLFinComp
import LaxLogic.PLLConfluentComplete

/-!
# `canonFinC` — the confluent finite canonical model (PCLL)  [WIP]

Branch `ui-confluence`.  The finite analogue of `PLLConfluentComplete`'s
`canonU`/`obInv`: worlds `{T : FTheory // MaxIn cl T}` as in `canonFin`,
but `Rₘ` is the `obInv` relation with the `◯◯ → ◯` collapse kept LOCAL
(Matthew's steer): we propagate the COLLAPSED box `boxOf χ` (= `χ` if `χ`
is already `◯ψ`, else `◯χ`).  Because `boxOf` always returns a `◯` and is
idempotent on `◯`s, transitivity closes with no `◯◯` ever entering `cl` —
so `cl` stays a finite subformula-closed set.
-/

open PLLFormula

namespace PLLND
namespace FinComp

open SetDeriv
open ConfluentU

variable {cl : Finset PLLFormula}

/-- The collapsed box: `◯χ` normalised by `◯◯ = ◯`.  Always a `◯`, and
idempotent (`boxOf (boxOf χ) = boxOf χ`). -/
def boxOf : PLLFormula → PLLFormula
  | .somehow ψ => .somehow ψ
  | φ => φ.somehow

@[simp] theorem boxOf_somehow (ψ : PLLFormula) :
    boxOf (.somehow ψ) = .somehow ψ := rfl

theorem boxOf_idem (χ : PLLFormula) : boxOf (boxOf χ) = boxOf χ := by
  cases χ <;> rfl

/-- The confluent backing: `v`'s closure-decisions come from an infinite
closed prime `DerivU` theory (a `canonU` world).  Exactly what a
cl-restriction of a `canonU` world carries; it is what makes `obInv`
prime, hence what makes the finite model confluent. -/
def Backed (cl : Finset PLLFormula) (v : FTheory) : Prop :=
  ∃ T : Set PLLFormula, SClosed T ∧ SPrime T ∧ ∀ φ ∈ cl, (φ ∈ v.val ↔ φ ∈ T)

/-- **Confluent finite worlds**: closure-maximal triples that carry a
backing.  (The backing is essential — over bare `MaxIn` worlds `obInv` is
inconsistent and the model is not confluent.) -/
abbrev WC (cl : Finset PLLFormula) := {v : FTheory // MaxIn cl v ∧ Backed cl v}

/-- The ◯-unit at the canonical level: `χ ∈ val` and `◯χ ∈ cl` give
`◯χ ∈ val`, by `laxIntro` and deductive closure. -/
theorem boxUnit {T : {T : FTheory // MaxIn cl T}} {χ : PLLFormula}
    (hbox : χ.somehow ∈ cl) (hχ : χ ∈ T.1.val) : χ.somehow ∈ T.1.val :=
  T.2.ded_closed hbox
    (setDeriv_coe_iff.mpr ⟨.laxIntro (.iden (Finset.mem_toList.mpr hχ))⟩)

/-- Confluent `Rₘ` (finite `obInv`, `◯◯`-collapsed): `val ⊆ val`, and
every collapsed box `boxOf χ ∈ cl` whose `χ` is validated at `U` is
validated at `T`. -/
def RmC (cl : Finset PLLFormula) (T U : {T : FTheory // MaxIn cl T}) : Prop :=
  T.1.val ⊆ U.1.val ∧
    ∀ χ : PLLFormula, boxOf χ ∈ cl → χ ∈ U.1.val → boxOf χ ∈ T.1.val

theorem RmC_refl (T : {T : FTheory // MaxIn cl T}) : RmC cl T T := by
  refine ⟨subset_rfl, fun χ hbox hχ => ?_⟩
  cases χ with
  | somehow ψ => exact hχ
  | prop a => exact boxUnit hbox hχ
  | falsePLL => exact boxUnit hbox hχ
  | and a b => exact boxUnit hbox hχ
  | or a b => exact boxUnit hbox hχ
  | ifThen a b => exact boxUnit hbox hχ

theorem RmC_trans {T U V : {T : FTheory // MaxIn cl T}}
    (h : RmC cl T U) (h' : RmC cl U V) : RmC cl T V := by
  refine ⟨h.1.trans h'.1, fun χ hbox hχ => ?_⟩
  have hU : boxOf χ ∈ U.1.val := h'.2 χ hbox hχ
  have hbb : boxOf (boxOf χ) = boxOf χ := boxOf_idem χ
  have hT : boxOf (boxOf χ) ∈ T.1.val :=
    h.2 (boxOf χ) (by rw [hbb]; exact hbox) hU
  rwa [hbb] at hT

/-- **The confluent finite canonical model.**  As `canonFin`, but with
`Rₘ` the collapsed `obInv` relation `RmC`. -/
def canonFinC (cl : Finset PLLFormula) : ConstraintModel where
  W := WC cl
  Ri T T' := T.1.val ⊆ T'.1.val
  Rm a b := RmC cl ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩
  F := {T | PLLFormula.falsePLL ∈ T.1.val}
  V a := {T | PLLFormula.prop a ∉ cl ∨ PLLFormula.prop a ∈ T.1.val}
  refl_i _ := subset_rfl
  trans_i h h' := h.trans h'
  refl_m a := RmC_refl ⟨a.1, a.2.1⟩
  trans_m h h' := RmC_trans h h'
  sub_mi h := h.1
  hered_F h hw := h hw
  hered_V h hw := hw.imp_right (fun h' => h h')
  full_F {a} {T} hw := by
    by_cases hcl : PLLFormula.prop a ∈ cl
    · exact .inr (T.2.1.ded_closed hcl (falso _ (of_mem (Finset.mem_coe.mpr hw))))
    · exact .inl hcl

-- audit: the confluent Rm + model are sorry-free
#print axioms RmC_trans
#print axioms canonFinC

/-! ## `obInvW` — the confluent canonical successor  [WIP]

Needs `cl` to be ◯-ADEQUATE: `boxOf φ ∈ cl` for every `φ ∈ cl`.  Finite
(`Sub ∪ {◯φ : φ ∈ Sub}`), because `boxOf` collapses `◯◯`. -/

/-- ◯-adequacy of the closure. -/
def OBoxAdeq (cl : Finset PLLFormula) : Prop := ∀ φ ∈ cl, boxOf φ ∈ cl

/-- The `obInv` world's underlying triple: `val = {ψ ∈ cl | boxOf ψ ∈
val(v)}`, its complement as `fal`, no promises. -/
def obInvFT (cl : Finset PLLFormula) (v : {T : FTheory // MaxIn cl T}) :
    FTheory :=
  ⟨cl.filter (fun ψ => boxOf ψ ∈ v.1.val),
   cl.filter (fun ψ => boxOf ψ ∉ v.1.val), ∅⟩

theorem obInvFT_val_iff {cl : Finset PLLFormula}
    {v : {T : FTheory // MaxIn cl T}} {ψ : PLLFormula} :
    ψ ∈ (obInvFT cl v).val ↔ ψ ∈ cl ∧ boxOf ψ ∈ v.1.val :=
  Finset.mem_filter

/-! ## The confluent backing — transferring `obInv_prime` to the finite level

The finite obInv is consistent only over worlds that arise as
cl-restrictions of `PLLConfluentComplete`'s infinite closed-prime
`DerivU` theories (`canonU` worlds).  We carry that backing explicitly and
transfer the two facts we need — `obInv_closed`/`obInv_prime` — verbatim.
No new Lindenbaum, no new completeness: `DerivU ⊇ LaxND`, so these worlds
still satisfy the ambient `MaxIn`. -/

/-- `LaxND`-derivability from a set implies `DerivU`-derivability (`SDeriv`). -/
theorem sderiv_of_setderiv {Γ : Set PLLFormula} {φ : PLLFormula}
    (h : Γ ⊩ φ) : SDeriv Γ φ := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  exact ⟨L, hL, DerivU.of_nd p⟩

/-- In a deductively closed (`SClosed`) set the collapsed and raw boxes
agree: `boxOf ψ ∈ T ↔ ◯ψ ∈ T` (the box case is `◯R`/`◯M`). -/
theorem boxOf_mem_iff {T : Set PLLFormula} (hc : SClosed T) (ψ : PLLFormula) :
    boxOf ψ ∈ T ↔ PLLFormula.somehow ψ ∈ T := by
  cases ψ with
  | somehow ψ' =>
      simp only [boxOf_somehow]
      constructor
      · intro h; exact hc _ (SDeriv.unit (SDeriv.of_mem h))
      · intro h
        -- `◯◯ψ' ⊃ ◯ψ'` inline (the `canonU.trans_m` term)
        have hM : LaxND ([] : List PLLFormula)
            ((somehow (somehow ψ')).ifThen (somehow ψ')) :=
          .impIntro (.laxElim (φ := somehow ψ') (.iden (by simp)) (.iden (by simp)))
        exact hc _ (SDeriv.mp ⟨[], by simp, DerivU.of_nd hM⟩ (SDeriv.of_mem h))
  | prop a => exact Iff.rfl
  | falsePLL => exact Iff.rfl
  | and a b => exact Iff.rfl
  | or a b => exact Iff.rfl
  | ifThen a b => exact Iff.rfl

/-- Primeness over a finite disjunction: a closed prime set containing
`⋁Ds` (nonempty) contains one of the `Ds` (the `⊥`-tail is absorbed by
closure). -/
theorem sprime_bigOr {U : Set PLLFormula} (hc : SClosed U) (hp : SPrime U) :
    ∀ (Ds : List PLLFormula), bigOr Ds ∈ U → Ds ≠ [] → ∃ D ∈ Ds, D ∈ U := by
  intro Ds
  induction Ds with
  | nil => intro _ hne; exact absurd rfl hne
  | cons D Ds' ih =>
      intro h _
      rcases hp D (bigOr Ds') h with hD | hrest
      · exact ⟨D, List.mem_cons_self .., hD⟩
      · by_cases hDs' : Ds' = []
        · subst hDs'
          have hDU : D ∈ U := hc D ⟨[PLLFormula.falsePLL], by simpa [bigOr] using hrest,
            DerivU.of_nd (.falsoElim D (.iden (by simp)))⟩
          exact ⟨D, List.mem_cons_self .., hDU⟩
        · obtain ⟨D', hD'mem, hD'U⟩ := ih hrest hDs'
          exact ⟨D', List.mem_cons_of_mem _ hD'mem, hD'U⟩

/-- **The heart, now TRUE.**  Over a ◯-adequate closure and a backed
world, the finite obInv successor is consistent — because its `val` is a
subset of the (prime, by `obInv_prime`) infinite `obInv T`, so any derived
disjunction of `fal`-formulas would put a `fal`-formula's box back in
`val v`.  Pure transfer of `obInv_closed`/`obInv_prime`. -/
theorem obInvFT_cons_of_backed {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl)
    {v : {T : FTheory // MaxIn cl T}} (hback : Backed cl v.1) :
    (obInvFT cl v).Cons := by
  obtain ⟨T, hTc, hTp, hTmatch⟩ := hback
  -- `val (obInvFT cl v) ⊆ obInv T`
  have hsub : (↑(obInvFT cl v).val : Set PLLFormula) ⊆ obInv T := by
    intro ψ hψ
    obtain ⟨hψcl, hbv⟩ := obInvFT_val_iff.mp (Finset.mem_coe.mp hψ)
    show PLLFormula.somehow ψ ∈ T
    exact (boxOf_mem_iff hTc ψ).mp ((hTmatch _ (hadeq _ hψcl)).mp hbv)
  intro Ds Ts hDs hTs hne hder
  have hTsnil : Ts = [] := by
    cases Ts with
    | nil => rfl
    | cons K Ts => exact absurd (hTs K (List.mem_cons_self ..)) (by simp [obInvFT])
  subst hTsnil
  rw [disjOf_nil_right, FTheory.toTheory_val] at hder
  have hne' : Ds ≠ [] := by simpa using hne
  have hbig : bigOr Ds ∈ obInv T :=
    obInv_closed hTc (bigOr Ds) (SDeriv.mono hsub (sderiv_of_setderiv hder))
  obtain ⟨D, hDmem, hDobinv⟩ :=
    sprime_bigOr (obInv_closed hTc) (obInv_prime hTc hTp) Ds hbig hne'
  have hDfal := hDs D hDmem
  simp only [FTheory.toTheory_fal, Finset.mem_coe, obInvFT, Finset.mem_filter] at hDfal
  obtain ⟨hDcl, hDbv⟩ := hDfal
  have hbT : boxOf D ∈ T := (boxOf_mem_iff hTc D).mpr hDobinv
  exact hDbv ((hTmatch _ (hadeq _ hDcl)).mpr hbT)

-- audit: the backed heart is kernel-clean (pure transfer of obInv_prime)
#print axioms obInvFT_cons_of_backed

/-- Closure-maximality of the obInv successor, over a **backed** world:
`Cons` is `obInvFT_cons_of_backed`; `InCl`/totality are structural. -/
theorem obInvFT_maxIn {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl)
    (v : {T : FTheory // MaxIn cl T}) (hb : Backed cl v.1) :
    MaxIn cl (obInvFT cl v) := by
  refine ⟨obInvFT_cons_of_backed hadeq hb,
    ⟨Finset.filter_subset _ _, Finset.filter_subset _ _,
      Finset.empty_subset _⟩, ?_⟩
  intro φ hφ
  by_cases h : boxOf φ ∈ v.1.val
  · exact .inl (Finset.mem_filter.mpr ⟨hφ, h⟩)
  · exact .inr (Finset.mem_filter.mpr ⟨hφ, h⟩)

/-- The obInv successor is itself backed: by `obInv T` (prime via
`obInv_prime`), which matches `obInvFT`'s `val` on `cl` (`boxOf_mem_iff`).
So `obInvW` maps confluent worlds to confluent worlds. -/
theorem obInvFT_backed {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl)
    (v : {T : FTheory // MaxIn cl T}) (hb : Backed cl v.1) :
    Backed cl (obInvFT cl v) := by
  obtain ⟨T, hTc, hTp, hTmatch⟩ := hb
  refine ⟨obInv T, obInv_closed hTc, obInv_prime hTc hTp, ?_⟩
  intro φ hφcl
  rw [obInvFT_val_iff]
  constructor
  · rintro ⟨-, hbv⟩
    show PLLFormula.somehow φ ∈ T
    exact (boxOf_mem_iff hTc φ).mp ((hTmatch _ (hadeq _ hφcl)).mp hbv)
  · intro hoi
    refine ⟨hφcl, (hTmatch _ (hadeq _ hφcl)).mpr ((boxOf_mem_iff hTc φ).mpr hoi)⟩

/-- **The confluent canonical successor** `obInvW : WC cl → WC cl`. -/
def obInvW {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl) (w : WC cl) : WC cl :=
  ⟨obInvFT cl ⟨w.1, w.2.1⟩,
   obInvFT_maxIn hadeq ⟨w.1, w.2.1⟩ w.2.2,
   obInvFT_backed hadeq ⟨w.1, w.2.1⟩ w.2.2⟩

/-- **The confluent row-witness**: `w Rₘ obInvW w` in `canonFinC`.  The
`val`-inclusion uses ◯-adequacy + `boxUnit` for non-boxes and
`boxOf`-fixity for boxes; the `obInv` clause is definitional. -/
theorem rm_obInvW {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl) (w : WC cl) :
    (canonFinC cl).Rm w (obInvW hadeq w) := by
  refine ⟨fun χ hχ => ?_, fun χ _ hχ => (Finset.mem_filter.mp hχ).2⟩
  have hχcl : χ ∈ cl := w.2.1.2.1.1 hχ
  refine Finset.mem_filter.mpr ⟨hχcl, ?_⟩
  cases χ with
  | somehow ψ => exact hχ
  | prop a => exact boxUnit (T := ⟨w.1, w.2.1⟩) (hadeq _ hχcl) hχ
  | falsePLL => exact boxUnit (T := ⟨w.1, w.2.1⟩) (hadeq _ hχcl) hχ
  | and a b => exact boxUnit (T := ⟨w.1, w.2.1⟩) (hadeq _ hχcl) hχ
  | or a b => exact boxUnit (T := ⟨w.1, w.2.1⟩) (hadeq _ hχcl) hχ
  | ifThen a b => exact boxUnit (T := ⟨w.1, w.2.1⟩) (hadeq _ hχcl) hχ

-- audit: the confluent successor is kernel-clean
#print axioms obInvW
#print axioms rm_obInvW

end FinComp
end PLLND
