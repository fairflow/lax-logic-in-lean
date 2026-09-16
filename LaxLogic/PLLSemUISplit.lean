import LaxLogic.PLLSemUILaw

/-!
# The split variant, and `∀p.(((p ⊃ ◯⊥) ⊃ p) ⊃ p) = ◯⊥`

The third frame-changing p-variant construction (after the doubling
`emVariant` and the levelled `lobVariant`), built for the frontier row
`((p ⊃ ◯⊥) ⊃ p) ⊃ p` — the row where both existing transforms stop at
`¬¬◯⊥` while the true ∀p-value is `◯⊥` (`poolAll_insufficient_frontier`
certifies the gap).

**The construction.**  Given a model `C` and a world `z`, adjoin an
isomorphic copy of the Rᵢ-cluster of `z` (the worlds two-way
Rᵢ-related to it) *strictly above* the cluster itself:

* every copy sits above every original world below the cluster and
  below the strict Rᵢ-cone over it (which the copies share);
* the copies carry the cluster's internal `Rₘ`-structure, and each
  copy's `Rₘ`-row escapes only to the *strict* `Rₘ`-successors of the
  world it duplicates — so `Rₘ ⊆ Rᵢ` survives, and no original world
  gains a constraint successor;
* fallibility and all valuations are inherited pointwise;
* `p` is decorated on the copies, the strict cone, and the fallible
  worlds (`splitSet`).

The projection back onto `C` is a total p-bisimulation
(`splitVariant_pbisim`): the copy of `v` is a p-variant of `v`.  On a
poset the cluster is `{z}` and the copy is the single point `⋆` of the
route-doc design (§0(u)); duplicating the whole cluster is what the
pointwise m-zigzag demands when the preorder is not antisymmetric.

**The payoff** (PROVED): at any world `z` whose `Rₘ`-row is
fallibility-free, the copy `⋆` of `z` forces `p` but never `◯⊥` — its
constraint row is `z`'s own, shifted off the cluster — so every
cluster world forcing `p ⊃ ◯⊥` is contradicted through `⋆`, and `z`
forces `(p ⊃ ◯⊥) ⊃ p` without forcing `p`
(`splitVariant_not_frontier`).  Hence

    ∀p.(((p ⊃ ◯⊥) ⊃ p) ⊃ p) = ◯⊥        (`semAll_frontier`)

closing the frontier row: the value the transform pool provably cannot
derive (`poolAll_not_derives_value`) is reached by the split.  The
split of the 3-chain `w < c < f` (`Rₘ = id ∪ {c→f}`, top fallible) at
its root is world-for-world the certified 4-chain countermodel
`frontierCM` — the countermodel found by the sweep *was* this
construction.

The split also subsumes the doubling on the excluded-middle value:
`semAll_em_p_via_split` re-proves `∀p.(p ∨ ¬p) = ⊥` with the cluster
copy as the generic p-point.  Iterated splits do NOT subsume the
levelled construction: `splitTower_oneW_forces_lob` (final section)
shows every member of the split tower over the one-world model forces
`◯(◯p ⊃ p)` everywhere — splits keep constraint arrows inside
Rᵢ-clusters, and the levelled construction's sideways step is exactly
an arrow leaving its cluster.  OPEN: the syntactic transform layer
over the split (the analogue of `lowT`/`sideT` feeding the graded
reconstruction law): the copies form an Rᵢ-blob whose ⊃-clauses are
anchored at the cluster rather than pointwise, so a formula-level
transform needs the cluster/strict sort distinction absorbed — next
session's problem.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-! ## The split model -/

/-- Worlds of the split: the original worlds, plus one copy of each
world in the Rᵢ-cluster of `z`. -/
abbrev SplitW (C : ConstraintModel) (z : C.W) : Type :=
  C.W ⊕ {v : C.W // C.Ri v z ∧ C.Ri z v}

/-- The split order: copies sit above everything below the cluster
(including the cluster itself), below the strict cone over it, and are
mutually related (as the cluster is). -/
def splitRi (C : ConstraintModel) (z : C.W) : SplitW C z → SplitW C z → Prop
  | .inl x, .inl y => C.Ri x y
  | .inl x, .inr _ => C.Ri x z
  | .inr _, .inl y => C.Ri z y ∧ ¬ C.Ri y z
  | .inr _, .inr _ => True

/-- The split constraint relation: the original one on originals, the
cluster's own `Rₘ`-structure between copies, and from a copy to an
original only along the duplicated world's *strict* `Rₘ`-successors.
No original world reaches a copy. -/
def splitRm (C : ConstraintModel) (z : C.W) : SplitW C z → SplitW C z → Prop
  | .inl x, .inl y => C.Rm x y
  | .inl _, .inr _ => False
  | .inr u, .inl y => C.Rm u.1 y ∧ ¬ C.Ri y z
  | .inr u, .inr t => C.Rm u.1 t.1

/-- The split model (before the `p`-decoration): fallibility and all
valuations inherited pointwise. -/
def splitModel (C : ConstraintModel) (z : C.W) : ConstraintModel where
  W := SplitW C z
  Ri := splitRi C z
  Rm := splitRm C z
  F := fun a => match a with
    | .inl x => x ∈ C.F
    | .inr u => u.1 ∈ C.F
  V := fun q a => match a with
    | .inl x => x ∈ C.V q
    | .inr u => u.1 ∈ C.V q
  refl_i := by
    intro a
    rcases a with x | u
    · exact C.refl_i x
    · exact True.intro
  trans_i := by
    intro a b c h₁ h₂
    rcases a with x | u <;> rcases b with y | t <;> rcases c with y' | s
    · exact C.trans_i h₁ h₂
    · exact C.trans_i h₁ h₂
    · exact C.trans_i h₁ h₂.1
    · exact h₁
    · exact ⟨C.trans_i h₁.1 h₂, fun h => h₁.2 (C.trans_i h₂ h)⟩
    · exact True.intro
    · exact h₂
    · exact True.intro
  refl_m := by
    intro a
    rcases a with x | u
    · exact C.refl_m x
    · exact C.refl_m u.1
  trans_m := by
    intro a b c h₁ h₂
    rcases a with x | u <;> rcases b with y | t <;> rcases c with y' | s
    · exact C.trans_m h₁ h₂
    · exact h₂.elim
    · exact h₁.elim
    · exact h₁.elim
    · exact ⟨C.trans_m h₁.1 h₂, fun h => h₁.2 (C.trans_i (C.sub_mi h₂) h)⟩
    · exact h₂.elim
    · exact ⟨C.trans_m h₁ h₂.1, h₂.2⟩
    · exact C.trans_m h₁ h₂
  sub_mi := by
    intro a b h
    rcases a with x | u <;> rcases b with y | t
    · exact C.sub_mi h
    · exact h.elim
    · exact ⟨C.trans_i u.2.2 (C.sub_mi h.1), h.2⟩
    · exact True.intro
  hered_F := by
    intro a b h hF
    rcases a with x | u <;> rcases b with y | t
    · exact C.hered_F h hF
    · exact C.hered_F (C.trans_i h t.2.2) hF
    · exact C.hered_F h.1 (C.hered_F u.2.1 hF)
    · exact C.hered_F t.2.2 (C.hered_F u.2.1 hF)
  hered_V := by
    intro q a b h hV
    rcases a with x | u <;> rcases b with y | t
    · exact C.hered_V h hV
    · exact C.hered_V (C.trans_i h t.2.2) hV
    · exact C.hered_V h.1 (C.hered_V u.2.1 hV)
    · exact C.hered_V t.2.2 (C.hered_V u.2.1 hV)
  full_F := by
    intro q a hF
    rcases a with x | u
    · exact C.full_F hF
    · exact C.full_F hF

/-- The `p`-decoration of the split: the strict cone over the cluster,
every cluster copy, and the fallible worlds. -/
def splitSet (C : ConstraintModel) (z : C.W) : Set (splitModel C z).W :=
  fun a => match a with
    | .inl y => (C.Ri z y ∧ ¬ C.Ri y z) ∨ y ∈ C.F
    | .inr _ => True

/-- The split variant: the split model with `p` decorated on
`splitSet`. -/
def splitVariant (C : ConstraintModel) (p : String) (z : C.W) :
    ConstraintModel :=
  redecorate (splitModel C z) p (splitSet C z)
    (by intro a b h hS
        rcases a with y | u <;> rcases b with y' | t
        · rcases hS with ⟨hzy, hyz⟩ | hF
          · exact Or.inl ⟨C.trans_i hzy h, fun h' => hyz (C.trans_i h h')⟩
          · exact Or.inr (C.hered_F h hF)
        · exact True.intro
        · exact Or.inl h
        · exact True.intro)
    (by intro a hF
        rcases a with y | u
        · exact Or.inr hF
        · exact True.intro)

/-- Projection of the split onto the base model: each copy goes to the
world it duplicates. -/
def splitProj (C : ConstraintModel) (z : C.W) : (splitModel C z).W → C.W
  | .inl y => y
  | .inr u => u.1

/-- **The projection is a p-bisimulation**: every world of the split
variant is a p-variant of its projection.  The m-zigzag at a copy is
exact because the copies carry the cluster's internal `Rₘ`-structure;
the two `by_cases` route an original-side successor to its copy when it
stays in the cluster and to itself when it escapes. -/
def splitVariant_pbisim (C : ConstraintModel) (p : String) (z : C.W) :
    PBisim p C (splitVariant C p z) where
  Z := fun x a => splitProj C z a = x
  atoms := by
    rintro x a rfl q hq
    show splitProj C z a ∈ C.V q ↔
      a ∈ (if q = p then splitSet C z else (splitModel C z).V q)
    rw [if_neg hq]
    rcases a with y | u
    · exact Iff.rfl
    · exact Iff.rfl
  fall := by
    rintro x a rfl
    rcases a with y | u
    · exact Iff.rfl
    · exact Iff.rfl
  iforth := by
    rintro x a rfl v hv
    rcases a with y | ⟨u, huz, hzu⟩
    · exact ⟨.inl v, hv, rfl⟩
    · by_cases hvz : C.Ri v z
      · exact ⟨.inr ⟨v, hvz, C.trans_i hzu hv⟩, True.intro, rfl⟩
      · exact ⟨.inl v, ⟨C.trans_i hzu hv, hvz⟩, rfl⟩
  iback := by
    rintro x a rfl a' ha'
    rcases a with y | ⟨u, huz, hzu⟩ <;> rcases a' with y' | ⟨u', huz', hzu'⟩
    · exact ⟨y', ha', rfl⟩
    · exact ⟨u', C.trans_i ha' hzu', rfl⟩
    · exact ⟨y', C.trans_i huz ha'.1, rfl⟩
    · exact ⟨u', C.trans_i huz hzu', rfl⟩
  mforth := by
    rintro x a rfl u hu
    rcases a with y | ⟨t, htz, hzt⟩
    · exact ⟨.inl u, hu, rfl⟩
    · by_cases huz : C.Ri u z
      · exact ⟨.inr ⟨u, huz, C.trans_i hzt (C.sub_mi hu)⟩, hu, rfl⟩
      · exact ⟨.inl u, ⟨hu, huz⟩, rfl⟩
  mback := by
    rintro x a rfl a' ha'
    rcases a with y | ⟨t, htz, hzt⟩ <;> rcases a' with y' | ⟨u', huz', hzu'⟩
    · exact ⟨y', ha', rfl⟩
    · exact ha'.elim
    · exact ⟨y', ha'.1, rfl⟩
    · exact ⟨u', ha', rfl⟩

/-! ## The refutation at the frontier row -/

/-- **The split refutes the frontier row** at any world whose
`Rₘ`-row is fallibility-free.  `z`'s copy `⋆` forces `p` but not `◯⊥`
(its constraint row is `z`'s own), so no cluster world can force
`p ⊃ ◯⊥`; every world above `z` outside the cluster forces `p`
outright.  Hence `z` forces `(p ⊃ ◯⊥) ⊃ p` — but `z` itself is
neither in the decoration nor fallible, so it does not force `p`. -/
theorem splitVariant_not_frontier (C : ConstraintModel) (p : String)
    (z : C.W) (hz : ∀ u, C.Rm z u → u ∉ C.F) :
    ¬ (splitVariant C p z).force (.inl z)
      ((((PLLFormula.prop p).ifThen PLLFormula.falsePLL.somehow).ifThen
        (.prop p)).ifThen (.prop p)) := by
  intro hM
  have hzF : z ∉ C.F := hz z (C.refl_m z)
  -- the copy of `z` forces `p` …
  have hstar_p : (splitVariant C p z).force
      (.inr ⟨z, C.refl_i z, C.refl_i z⟩) (.prop p) := by
    show (Sum.inr ⟨z, C.refl_i z, C.refl_i z⟩ : (splitModel C z).W) ∈
      (if p = p then splitSet C z else (splitModel C z).V p)
    rw [if_pos rfl]
    exact True.intro
  -- … but not `◯⊥`: its constraint row is `z`'s, fallibility-free
  have hstar_nbox : ¬ (splitVariant C p z).force
      (.inr ⟨z, C.refl_i z, C.refl_i z⟩) PLLFormula.falsePLL.somehow := by
    intro hbox
    obtain ⟨d, hd, hdF⟩ := hbox _ ((splitVariant C p z).refl_i _)
    rcases d with t | t
    · exact hz t hd.1 hdF
    · exact hz t.1 hd hdF
  -- `z` forces the antecedent `(p ⊃ ◯⊥) ⊃ p` …
  have hA : (splitVariant C p z).force (.inl z)
      (((PLLFormula.prop p).ifThen PLLFormula.falsePLL.somehow).ifThen
        (.prop p)) := by
    intro b hb himp
    rcases b with y | u
    · by_cases hyz : C.Ri y z
      · -- a cluster world sees ⋆; forcing `p ⊃ ◯⊥` there is impossible
        exact absurd
          (himp (.inr ⟨z, C.refl_i z, C.refl_i z⟩) hyz hstar_p) hstar_nbox
      · -- a strict-cone world is in the decoration
        show (Sum.inl y : (splitModel C z).W) ∈
          (if p = p then splitSet C z else (splitModel C z).V p)
        rw [if_pos rfl]
        exact Or.inl ⟨hb, hyz⟩
    · -- every copy is in the decoration
      show (Sum.inr u : (splitModel C z).W) ∈
        (if p = p then splitSet C z else (splitModel C z).V p)
      rw [if_pos rfl]
      exact True.intro
  -- … but not `p`
  have hp : (Sum.inl z : (splitModel C z).W) ∈
      (if p = p then splitSet C z else (splitModel C z).V p) :=
    hM (.inl z) ((splitVariant C p z).refl_i _) hA
  rw [if_pos rfl] at hp
  rcases hp with ⟨-, hns⟩ | hF
  · exact hns (C.refl_i z)
  · exact hzF hF

/-! ## The frontier value -/

/-- **`∀p.(((p ⊃ ◯⊥) ⊃ p) ⊃ p) = ◯⊥`** — the frontier-row value, by
the split.  Below `◯⊥` every future forces `p ⊃ ◯⊥` outright, so a
`(p⊃◯⊥)⊃p`-world forces `p`; conversely a world without `◯⊥` has a
future whose `Rₘ`-row is fallibility-free, and the split there is a
p-variant refuting the row. -/
theorem semAll_frontier (p : String) :
    IsSemAll p
      ((((PLLFormula.prop p).ifThen PLLFormula.falsePLL.somehow).ifThen
        (.prop p)).ifThen (.prop p))
      PLLFormula.falsePLL.somehow := by
  refine ⟨by simp, ?_⟩
  intro C w
  constructor
  · intro hw v hv N B v' hZ
    have hbox : N.force v' PLLFormula.falsePLL.somehow :=
      (force_iff_of_bisim B (by simp) hZ).mp (C.force_hered hv hw)
    intro x hx hxA
    exact hxA x (N.refl_i x)
      (fun y hxy _ => N.force_hered (N.trans_i hx hxy) hbox)
  · intro h' x hwx
    by_contra hno
    have hz : ∀ u, C.Rm x u → u ∉ C.F := fun u hu hF => hno ⟨u, hu, hF⟩
    exact splitVariant_not_frontier C p x hz
      (h' x hwx (splitVariant C p x) (splitVariant_pbisim C p x) (.inl x) rfl)

/-- The pinned frontier row of `PLLSemUILaw` has ∀p-value `◯⊥`. -/
theorem semAll_frontierRow :
    IsSemAll "p" frontierRow PLLFormula.falsePLL.somehow :=
  semAll_frontier "p"

/-- `◯⊥ ⊢ ((p ⊃ ◯⊥) ⊃ p) ⊃ p` — the lower half as a derivability
corollary (previously known only through a found proof term). -/
theorem boxBot_derives_frontier :
    Nonempty (LaxND [PLLFormula.falsePLL.somehow] frontierRow) :=
  semAll_lower semAll_frontierRow

/-- **The transform pool cannot derive the value it fails to match**:
`poolAll` does not derive `◯⊥` at the frontier row (else, composing
with `boxBot_derives_frontier`, it would derive the row itself,
against the certified countermodel).  The split reaches what the pool
provably cannot. -/
theorem poolAll_not_derives_value :
    poolAll "p" frontierRow ⊬ PLLFormula.falsePLL.somehow := by
  rintro ⟨d⟩
  obtain ⟨e⟩ := boxBot_derives_frontier
  exact poolAll_insufficient_frontier ⟨compose e d⟩

/-! ## The split subsumes the doubling -/

/-- `∀p.(p ∨ ¬p) = ⊥` again, now via the split: the cluster copy over
`w` is the generic p-point (`w` is not in the decoration, its copy
is).  One construction covers the doubling's value and the frontier
row. -/
theorem semAll_em_p_via_split (p : String) :
    IsSemAll p ((PLLFormula.prop p).or ((PLLFormula.prop p).ifThen
      .falsePLL)) .falsePLL := by
  refine ⟨by simp, ?_⟩
  intro C w
  constructor
  · intro hw v hv N B v' hZ
    exact N.force_of_fallible ((B.fall hZ).mp (C.hered_F hv hw))
  · intro h'
    have hforce := h' w (C.refl_i w) (splitVariant C p w)
      (splitVariant_pbisim C p w) (.inl w) rfl
    rcases hforce with hp | hnp
    · have hp' : (Sum.inl w : (splitModel C w).W) ∈
          (if p = p then splitSet C w else (splitModel C w).V p) := hp
      rw [if_pos rfl] at hp'
      rcases hp' with ⟨-, hns⟩ | hF
      · exact (hns (C.refl_i w)).elim
      · exact hF
    · have hstar_p : (splitVariant C p w).force
          (.inr ⟨w, C.refl_i w, C.refl_i w⟩) (.prop p) := by
        show (Sum.inr ⟨w, C.refl_i w, C.refl_i w⟩ : (splitModel C w).W) ∈
          (if p = p then splitSet C w else (splitModel C w).V p)
        rw [if_pos rfl]
        exact True.intro
      exact hnp (.inr ⟨w, C.refl_i w, C.refl_i w⟩) (C.refl_i w) hstar_p

/-! ## Iterated splits do not reach the levelled row

The natural unification hope — that splitting a split (at any points,
with any redecorations) also subsumes the levelled construction
`lobVariant` — is REFUTED.  The invariant: splits keep constraint
arrows inside Rᵢ-clusters, and cluster-internal constraints force
`◯A ⊃ A` everywhere; so no split-tower variant of the one-world model
ever refutes `◯(◯p ⊃ p)`, while the value `∀p.◯(◯p⊃p) = ◯⊥`
(`semAll_box_lob`) demands such a refutation at `oneW`'s (◯⊥-free)
world.  The levelled construction's sideways constraint step 1 → 2 is
precisely an `Rₘ`-arrow leaving its cluster — the one thing splits
never create. -/

/-- Constraint arrows stay inside Rᵢ-clusters: with `sub_mi`, every
`Rₘ`-successor is a cluster-mate of its source. -/
def RmClusterInternal (C : ConstraintModel) : Prop :=
  ∀ {a b : C.W}, C.Rm a b → C.Ri b a

/-- Cluster-internal constraints force `◯A ⊃ A` everywhere: the
constraint witness is a cluster-mate, and forcing crosses clusters in
both directions. -/
theorem boxA_imp_A_of_rmClusterInternal {C : ConstraintModel}
    (h : RmClusterInternal C) (A : PLLFormula) (w : C.W) :
    C.force w (A.somehow.ifThen A) := by
  intro v hv hbox
  obtain ⟨u, hu, hA⟩ := hbox v (C.refl_i v)
  exact C.force_hered (h hu) hA

/-- The split preserves cluster-internality: internal copy arrows
mirror cluster arrows, and an escaping arrow from a copy would have a
cluster-internal source arrow contradicting its own strictness. -/
theorem rmClusterInternal_splitModel {C : ConstraintModel} {z : C.W}
    (h : RmClusterInternal C) : RmClusterInternal (splitModel C z) := by
  intro a b hab
  rcases a with x | u <;> rcases b with y | t
  · exact h hab
  · exact hab.elim
  · exact absurd (C.trans_i (h hab.1) u.2.1) hab.2
  · exact True.intro

/-- Redecoration never touches the frame. -/
theorem rmClusterInternal_redecorate {M : ConstraintModel} (p : String)
    (S : Set M.W) (hh : ∀ {w v}, M.Ri w v → w ∈ S → v ∈ S)
    (hf : ∀ {w}, w ∈ M.F → w ∈ S) (h : RmClusterInternal M) :
    RmClusterInternal (redecorate M p S hh hf) := h

theorem rmClusterInternal_splitVariant {C : ConstraintModel} (p : String)
    (z : C.W) (h : RmClusterInternal C) :
    RmClusterInternal (splitVariant C p z) :=
  rmClusterInternal_splitModel h

/-- "Iterated splits": the closure of a model under split variants (at
any world, any atom) and arbitrary redecorations. -/
inductive SplitTower (C : ConstraintModel) : ConstraintModel → Prop
  | base : SplitTower C C
  | split {D : ConstraintModel} (p : String) (z : D.W) :
      SplitTower C D → SplitTower C (splitVariant D p z)
  | redec {D : ConstraintModel} (p : String) (S : Set D.W)
      (hh : ∀ {w v}, D.Ri w v → w ∈ S → v ∈ S)
      (hf : ∀ {w}, w ∈ D.F → w ∈ S) :
      SplitTower C D → SplitTower C (redecorate D p S hh hf)

theorem SplitTower.rmClusterInternal {C D : ConstraintModel}
    (h : RmClusterInternal C) (t : SplitTower C D) :
    RmClusterInternal D := by
  induction t with
  | base => exact h
  | split p z _ ih => exact rmClusterInternal_splitVariant p z ih
  | redec p S hh hf _ ih => exact rmClusterInternal_redecorate p S hh hf ih

/-- **Iterated splits do not reach the levelled row**: every member of
the split tower over the one-world model forces `◯(◯p ⊃ p)` at every
world — no such variant can refute it, while the upper half of
`semAll_box_lob` demands a refuting p-variant at `oneW`'s world.  The
transform basis genuinely needs the levelled construction (or a common
generalisation that creates sideways constraint arrows). -/
theorem splitTower_oneW_forces_lob (p : String) {D : ConstraintModel}
    (t : SplitTower oneW D) (w : D.W) :
    D.force w ((PLLFormula.prop p).somehow.ifThen (.prop p)).somehow := by
  have hD : RmClusterInternal D := t.rmClusterInternal (fun _ => trivial)
  intro v hv
  exact ⟨v, D.refl_m v, boxA_imp_A_of_rmClusterInternal hD (.prop p) v⟩

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.semAll_frontier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms semAll_frontier

/--
info: 'PLLND.SemUI.poolAll_not_derives_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms poolAll_not_derives_value

/-- info: 'PLLND.SemUI.splitTower_oneW_forces_lob' does not depend on any axioms -/
#guard_msgs in
#print axioms splitTower_oneW_forces_lob

end SemUI
end PLLND
