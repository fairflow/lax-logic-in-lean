import Mathlib.Order.Completion
import Mathlib.Order.Nucleus
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.CompleteBooleanAlgebra
import Meta.Audit

/-!
# A nucleus extends to the MacNeille completion

2026-10-22.  Matthew's question: does the lax modality `◯` of F0 (the
Lindenbaum algebra of variable-free PLL formulas) extend to the
Dedekind–MacNeille completion `DM(F0)` as a nucleus?  This file proves the
general theorem; the F0 instance needs packaging that does not exist yet
(see the closing note).

**§1, the ◯-free instance (CLAUDE.md rule 8).**  For a Heyting algebra `H`,
Mathlib's `DedekindCut H` (the MacNeille completion, a complete lattice) is a
frame, i.e. a complete Heyting algebra, with

    X ⇨ Y = ⋀ { ↓(h ⇨ k) : h ∈ X.left, k ∈ Y.right },

and `DedekindCut.principal` is a Heyting algebra embedding (it preserves `⊓`,
`⊔`, `⇨`, `⊥`, `⊤` and reflects `≤`) that is join-dense and meet-dense.  The
frame structure is a SCOPED instance (`open MacNeille`): for a linear order
Mathlib already gives `DedekindCut α` a Heyting implication, and a global
instance here would make a second, non-defeq one.

**§2, the abstract theorem.**  Let `L` be a frame, `e : H → L` a Heyting
algebra homomorphism that reflects `≤` and is join-dense, and `j` a nucleus on
`H`.  Then

    k x = ⨅ { e (j a) : a ∈ H, x ≤ e a }

is a nucleus on `L` with `k (e a) = e (j a)`, and every monotone `k'` with
`k' ∘ e = e ∘ j` satisfies `k' ≤ k`.  Meet-density is NOT used.  The one
non-trivial law is `k x ⊓ k y ≤ k (x ⊓ y)`; it rests on two facts:

* `j (h ⇨ j b) = h ⇨ j b` in `H` (`nucleus_himp_fix`);
* `x ⊓ y ≤ e (j a) → k x ⊓ y ≤ e (j a)` (`ext_inf_le`), by join-density of
  `y` and frame distributivity.

**§3, the instance at `DedekindCut H`** (`dmNucleus`).

**Uniqueness is REFUTED** in general: `wip/f0MacNeilleNonUnique.lean` gives a
bounded chain `G` (a Heyting algebra), a nucleus on it, and two different
nuclei on `DM(G)` extending it.  The nuclei extending `j` are exactly the
interval from `leastExt` to `extNucleus` (`extends_iff_mem_Icc`); at F0
whether that interval is a single point is OPEN.
-/

namespace MacNeille

open Set

/-! ## §1 The MacNeille completion of a Heyting algebra is a frame -/

section DM

variable {H : Type*} [HeytingAlgebra H]

/-- Heyting implication of cuts: the meet of the principal cuts `↓(h ⇨ k)`,
`h` in the left set of `X`, `k` in the right set of `Y`. -/
def cutHimp (X Y : DedekindCut H) : DedekindCut H :=
  sInf {Z | ∃ h ∈ X.left, ∃ k ∈ Y.right, Z = DedekindCut.principal (h ⇨ k)}

theorem mem_left_cutHimp {X Y : DedekindCut H} {z : H} :
    z ∈ (cutHimp X Y).left ↔ ∀ h ∈ X.left, ∀ k ∈ Y.right, z ≤ h ⇨ k := by
  simp only [cutHimp, Concept.extent_sInf, mem_iInter, mem_setOf_eq]
  constructor
  · intro hz h hh k hk
    exact hz _ ⟨h, hh, k, hk, rfl⟩
  · rintro hz _ ⟨h, hh, k, hk, rfl⟩
    exact hz h hh k hk

/-- The adjunction `Z ≤ X ⇨ Y ↔ Z ⊓ X ≤ Y` for cuts. -/
theorem le_cutHimp_iff (Z X Y : DedekindCut H) : Z ≤ cutHimp X Y ↔ Z ⊓ X ≤ Y := by
  constructor
  · intro hZ g hg
    obtain ⟨hgZ, hgX⟩ := hg
    have h1 := mem_left_cutHimp.mp (hZ hgZ)
    show g ∈ Y.left
    rw [← DedekindCut.lowerBounds_right]
    intro k hk
    have h2 := h1 g hgX k hk
    rwa [le_himp_iff, inf_idem] at h2
  · intro h z hz
    rw [mem_left_cutHimp]
    intro g hg k hk
    rw [le_himp_iff]
    have hzg : z ⊓ g ∈ (Z ⊓ X).left :=
      ⟨Concept.isLowerSet_extent_le Z inf_le_left hz,
       Concept.isLowerSet_extent_le X inf_le_right hg⟩
    exact Concept.rel_extent_intent (h hzg) hk

/-- **The MacNeille completion of a Heyting algebra is a frame** (a complete
Heyting algebra).  Scoped: see the module docstring. -/
scoped instance instFrame : Order.Frame (DedekindCut H) where
  __ := (inferInstance : CompleteLattice (DedekindCut H))
  himp := cutHimp
  le_himp_iff := le_cutHimp_iff
  compl X := cutHimp X ⊥
  himp_bot _ := rfl

theorem himp_eq_cutHimp (X Y : DedekindCut H) : X ⇨ Y = cutHimp X Y := rfl

open DedekindCut

theorem principal_inf (a b : H) : principal (a ⊓ b) = principal a ⊓ principal b := by
  apply DedekindCut.ext
  ext x
  simp

theorem principal_sup (a b : H) : principal (a ⊔ b) = principal a ⊔ principal b := by
  apply DedekindCut.ext'
  ext x
  simp

theorem principal_bot : principal (⊥ : H) = ⊥ := by
  apply DedekindCut.ext'
  ext x
  simp

theorem principal_top : principal (⊤ : H) = ⊤ := by
  apply DedekindCut.ext
  ext x
  simp

theorem principal_himp (a b : H) : principal (a ⇨ b) = principal a ⇨ principal b := by
  apply DedekindCut.ext
  ext x
  rw [himp_eq_cutHimp, mem_left_cutHimp, left_principal, mem_Iic]
  constructor
  · intro hx h hh k hk
    exact hx.trans (himp_le_himp hh hk)
  · intro hx
    exact hx a (mem_Iic.mpr le_rfl) b (mem_Ici.mpr le_rfl)

/-- `principal` as a Heyting algebra homomorphism. -/
def principalHom : HeytingHom H (DedekindCut H) where
  toFun := principal
  map_sup' := principal_sup
  map_inf' := principal_inf
  map_bot' := principal_bot
  map_himp' := principal_himp

@[simp] theorem principalHom_apply (a : H) : principalHom a = principal a := rfl

/-- Join-density: every cut is the join of the principal cuts below it. -/
theorem sSup_principal_left (X : DedekindCut H) : sSup (principal '' X.left) = X := by
  apply DedekindCut.ext'
  ext k
  simp only [Concept.intent_sSup, mem_iInter, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, right_principal, mem_Ici]
  rw [← DedekindCut.upperBounds_left]
  exact Iff.rfl

/-- Meet-density: every cut is the meet of the principal cuts above it. -/
theorem sInf_principal_right (X : DedekindCut H) : sInf (principal '' X.right) = X := by
  apply DedekindCut.ext
  ext h
  simp only [Concept.extent_sInf, mem_iInter, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, left_principal, mem_Iic]
  rw [← DedekindCut.lowerBounds_right]
  exact Iff.rfl

end DM

/-! ## §2 The abstract theorem -/

/-- A Heyting algebra homomorphism into a frame that reflects `≤` and is
join-dense.  This is all §2 uses. -/
structure JoinDenseHeytingEmbedding (H L : Type*) [HeytingAlgebra H] [Order.Frame L] where
  /-- the embedding -/
  toHom : HeytingHom H L
  /-- it reflects (and preserves) the order -/
  le_iff : ∀ a b, toHom a ≤ toHom b ↔ a ≤ b
  /-- every element is the join of the embedded elements below it -/
  join_dense : ∀ x : L, sSup (toHom '' {a | toHom a ≤ x}) = x

/-- The bundle the brief asks for: in addition, meet-dense.  (§2 does not use
`meet_dense`.) -/
structure DenseHeytingEmbedding (H L : Type*) [HeytingAlgebra H] [Order.Frame L]
    extends JoinDenseHeytingEmbedding H L where
  /-- every element is the meet of the embedded elements above it -/
  meet_dense : ∀ x : L, sInf (toHom '' {a | x ≤ toHom a}) = x

section Nucleus

variable {H : Type*} [HeytingAlgebra H]

/-- In `H`, `h ⇨ j b` is `j`-fixed. -/
theorem nucleus_himp_fix (j : Nucleus H) (h b : H) : j (h ⇨ j b) = h ⇨ j b := by
  apply le_antisymm _ j.le_apply
  rw [le_himp_iff]
  calc j (h ⇨ j b) ⊓ h ≤ j (h ⇨ j b) ⊓ j h := inf_le_inf_left _ j.le_apply
    _ = j ((h ⇨ j b) ⊓ h) := j.map_inf.symm
    _ = j (j b ⊓ h) := by rw [himp_inf_self]
    _ ≤ j (j b) := j.monotone inf_le_left
    _ = j b := j.idempotent b

variable {L : Type*} [Order.Frame L] (E : JoinDenseHeytingEmbedding H L) (j : Nucleus H)

namespace JoinDenseHeytingEmbedding

/-- The candidate extension `k x = ⨅ { e (j a) : x ≤ e a }`. -/
def extFun (x : L) : L := ⨅ (a : H) (_ : x ≤ E.toHom a), E.toHom (j a)

variable {E j}

theorem mono (a b : H) (h : a ≤ b) : E.toHom a ≤ E.toHom b := (E.le_iff a b).mpr h

theorem extFun_le {x : L} {a : H} (h : x ≤ E.toHom a) : E.extFun j x ≤ E.toHom (j a) :=
  iInf₂_le a h

theorem le_extFun_iff {x z : L} :
    z ≤ E.extFun j x ↔ ∀ a, x ≤ E.toHom a → z ≤ E.toHom (j a) := by
  simp [extFun]

theorem extFun_mono {x y : L} (h : x ≤ y) : E.extFun j x ≤ E.extFun j y :=
  le_extFun_iff.mpr fun _ ha => extFun_le (h.trans ha)

theorem le_extFun (x : L) : x ≤ E.extFun j x :=
  le_extFun_iff.mpr fun _ ha => ha.trans (E.mono _ _ j.le_apply)

theorem extFun_apply (a : H) : E.extFun j (E.toHom a) = E.toHom (j a) := by
  apply le_antisymm (extFun_le le_rfl)
  rw [le_extFun_iff]
  intro b hb
  exact E.mono _ _ (j.monotone ((E.le_iff a b).mp hb))

/-- The key inequality: `x ⊓ y ≤ e (j a) → k x ⊓ y ≤ e (j a)`. -/
theorem ext_inf_le {x y : L} {a : H} (hxy : x ⊓ y ≤ E.toHom (j a)) :
    E.extFun j x ⊓ y ≤ E.toHom (j a) := by
  rw [← E.join_dense y, inf_sSup_eq]
  refine iSup₂_le ?_
  rintro _ ⟨h, hh, rfl⟩
  have hhy : E.toHom h ≤ y := hh
  have h1 : x ≤ E.toHom (h ⇨ j a) := by
    rw [map_himp, le_himp_iff]
    exact (inf_le_inf_left x hhy).trans hxy
  have h2 : E.extFun j x ≤ E.toHom h ⇨ E.toHom (j a) := by
    have := extFun_le (j := j) h1
    rwa [nucleus_himp_fix, map_himp] at this
  exact le_himp_iff.mp h2

theorem extFun_inf (x y : L) : E.extFun j (x ⊓ y) = E.extFun j x ⊓ E.extFun j y := by
  apply le_antisymm
  · exact le_inf (extFun_mono inf_le_left) (extFun_mono inf_le_right)
  · rw [le_extFun_iff]
    intro a ha
    have h1 : x ⊓ y ≤ E.toHom (j a) := ha.trans (E.mono _ _ j.le_apply)
    have h2 : E.extFun j x ⊓ y ≤ E.toHom (j a) := ext_inf_le h1
    have h3 : y ⊓ E.extFun j x ≤ E.toHom (j a) := by rwa [inf_comm]
    have h4 : E.extFun j y ⊓ E.extFun j x ≤ E.toHom (j a) := ext_inf_le h3
    rwa [inf_comm] at h4

theorem extFun_idem (x : L) : E.extFun j (E.extFun j x) ≤ E.extFun j x := by
  rw [le_extFun_iff]
  intro a ha
  calc E.extFun j (E.extFun j x) ≤ E.extFun j (E.toHom (j a)) := extFun_mono (extFun_le ha)
    _ = E.toHom (j (j a)) := extFun_apply _
    _ = E.toHom (j a) := by rw [j.idempotent]

variable (E j)

/-- **The extension of `j` to `L`, as a nucleus.** -/
def extNucleus : Nucleus L where
  toFun := E.extFun j
  map_inf' := extFun_inf
  idempotent' := extFun_idem
  le_apply' := le_extFun

theorem extNucleus_apply (x : L) :
    E.extNucleus j x = ⨅ (a : H) (_ : x ≤ E.toHom a), E.toHom (j a) := rfl

/-- **It extends `j`.** -/
theorem extNucleus_comm (a : H) : E.extNucleus j (E.toHom a) = E.toHom (j a) :=
  extFun_apply a

/-- **It is the greatest monotone extension.** -/
theorem le_extNucleus (k' : L → L) (hk' : Monotone k')
    (hext : ∀ a, k' (E.toHom a) = E.toHom (j a)) (x : L) : k' x ≤ E.extNucleus j x :=
  le_extFun_iff.mpr fun a ha => (hk' ha).trans_eq (hext a)

/-- In particular it is the greatest nucleus extending `j`. -/
theorem nucleus_le_extNucleus (k' : Nucleus L) (hext : ∀ a, k' (E.toHom a) = E.toHom (j a)) :
    k' ≤ E.extNucleus j :=
  fun x => E.le_extNucleus j k' k'.monotone hext x

/-- **The abstract theorem** in the form of the brief. -/
theorem exists_nucleus_extension :
    ∃ k : Nucleus L, (∀ a, k (E.toHom a) = E.toHom (j a)) ∧
      ∀ k' : L → L, Monotone k' → (∀ a, k' (E.toHom a) = E.toHom (j a)) → ∀ x, k' x ≤ k x :=
  ⟨E.extNucleus j, E.extNucleus_comm j, E.le_extNucleus j⟩

/-- The least nucleus extending `j`: the meet of all of them. -/
def leastExt : Nucleus L := sInf {k : Nucleus L | ∀ a, k (E.toHom a) = E.toHom (j a)}

theorem leastExt_comm (a : H) : E.leastExt j (E.toHom a) = E.toHom (j a) := by
  apply le_antisymm
  · rw [leastExt, Nucleus.sInf_apply]
    have hmem : E.extNucleus j ∈ {k : Nucleus L | ∀ a, k (E.toHom a) = E.toHom (j a)} :=
      E.extNucleus_comm j
    exact (iInf₂_le (E.extNucleus j) hmem).trans_eq (E.extNucleus_comm j a)
  · rw [leastExt, Nucleus.sInf_apply]
    exact le_iInf₂ fun k hk => (hk a).ge

/-- **The nuclei extending `j` are exactly the interval `[leastExt, extNucleus]`.** -/
theorem extends_iff_mem_Icc (k : Nucleus L) :
    (∀ a, k (E.toHom a) = E.toHom (j a)) ↔ E.leastExt j ≤ k ∧ k ≤ E.extNucleus j := by
  constructor
  · intro hk
    exact ⟨sInf_le hk, E.nucleus_le_extNucleus j k hk⟩
  · rintro ⟨h₁, h₂⟩ a
    apply le_antisymm
    · exact (h₂ (E.toHom a)).trans_eq (E.extNucleus_comm j a)
    · exact (E.leastExt_comm j a).symm.le.trans (h₁ (E.toHom a))

end JoinDenseHeytingEmbedding

end Nucleus

/-! ## §3 The instance at the MacNeille completion -/

section Instance

variable {H : Type*} [HeytingAlgebra H]

open DedekindCut

/-- `principal : H → DM(H)` as a dense Heyting embedding (§1 packaged). -/
def dmEmbedding : DenseHeytingEmbedding H (DedekindCut H) where
  toHom := principalHom
  le_iff _ _ := principal_le_principal
  join_dense X := by
    have : principalHom '' {a | principalHom a ≤ X} = principal '' X.left := by
      ext Z
      simp [principal_le_iff]
    rw [this, sSup_principal_left]
  meet_dense X := by
    have : principalHom '' {a | X ≤ principalHom a} = principal '' X.right := by
      ext Z
      simp [le_principal_iff]
    rw [this, sInf_principal_right]

/-- **A nucleus on a Heyting algebra extends to its MacNeille completion.** -/
def dmNucleus (j : Nucleus H) : Nucleus (DedekindCut H) :=
  dmEmbedding.toJoinDenseHeytingEmbedding.extNucleus j

theorem dmNucleus_principal (j : Nucleus H) (a : H) :
    dmNucleus j (principal a) = principal (j a) :=
  dmEmbedding.toJoinDenseHeytingEmbedding.extNucleus_comm j a

theorem le_dmNucleus (j : Nucleus H) (k' : DedekindCut H → DedekindCut H) (hk' : Monotone k')
    (hext : ∀ a, k' (principal a) = principal (j a)) (X : DedekindCut H) :
    k' X ≤ dmNucleus j X :=
  dmEmbedding.toJoinDenseHeytingEmbedding.le_extNucleus j k' hk' hext X

end Instance

end MacNeille

/-! ## Pins

Measured 2026-10-22; each bound was watched failing first (declared `[]`,
which every declaration below exceeds).  `Classical.choice` enters from
Mathlib by two routes (`#choice_path`, 2026-10-22): Mathlib's `Nucleus` API
(`Nucleus.monotone` and `Nucleus.le_apply` go through
`InfHomClass.toOrderHomClass`, whose proof uses `Classical.propDecidable`),
already in `nucleus_himp_fix`; and the order on cuts, `Concept.instPartialOrder`,
through `Set.instCompleteAtomicBooleanAlgebra` (`Classical.skolem`).  Accepted
here as model theory, per the brief. -/

#axioms_within MacNeille.instFrame [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.principal_himp [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.principal_top [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.principalHom [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.sSup_principal_left [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.sInf_principal_right [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.dmEmbedding [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.nucleus_himp_fix [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.JoinDenseHeytingEmbedding.extNucleus [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.JoinDenseHeytingEmbedding.extNucleus_comm [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.JoinDenseHeytingEmbedding.le_extNucleus [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.JoinDenseHeytingEmbedding.nucleus_le_extNucleus [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.JoinDenseHeytingEmbedding.exists_nucleus_extension [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.JoinDenseHeytingEmbedding.extends_iff_mem_Icc [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.dmNucleus [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.dmNucleus_principal [propext, Classical.choice, Quot.sound]
#axioms_within MacNeille.le_dmNucleus [propext, Classical.choice, Quot.sound]

/-! ## The F0 instance: packaging that does not exist yet

F0 is `PLLND.RNClass = Quotient closedSetoid` (`LaxLogic/ClosedFragmentLattice.lean`),
which carries `DistribLattice` and `BoundedOrder` instances only.  The instance
`dmNucleus` at `H = F0` needs, in addition:

* `HeytingAlgebra RNClass`: `⇨` lifted from `ifThen` (respects `LaxEquiv`) and
  `le_himp_iff`, a pointwise fact of the forcing clause for `⊃` plus
  heredity (`ConstraintModel.force_hered`);
* `Nucleus RNClass`: `◯` lifted from `somehow`, with `x ≤ ◯x` (the `laxIntro`
  case of `soundness`), `◯◯x ≤ ◯x` and `◯x ⊓ ◯y ≤ ◯(x ⊓ y)` (from `refl_m`,
  `trans_m`, `sub_mi`, `force_hered`).

Neither exists in the repository (searched 2026-10-22).  Not built here: the
brief stops at §2 when this packaging is missing. -/
