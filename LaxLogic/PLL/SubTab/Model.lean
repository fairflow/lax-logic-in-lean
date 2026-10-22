import LaxLogic.PLL.SubTab.Dich

/-!
# The subframe tableau: an open tree is a countermodel (truth lemma)

2026-10-15.  A `Good` tree is a finite decidable subframe model:
worlds are the paths into the tree, ordered by prefix; the S-points are the
nodes marked S; a world's valuation is the atoms true at its node.  Its
root refutes every sequent the tree covers (`root_refutes`), by the truth
lemma (`truth`): what a node holds true is forced there, what it holds
false is not.
-/

open PLLFormula

namespace PLLND
namespace SubTab

open SubframeModel.CF

namespace OTree

/-- The node at a path, if the path is in the tree. -/
def node? : OTree → List Nat → Option OTree
  | t, [] => some t
  | t, i :: p => match t.kids[i]? with
    | some k => k.node? p
    | none => none

mutual
/-- Every path in the tree. -/
def paths : OTree → List (List Nat)
  | node _ _ _ ks => [] :: pathsL 0 ks
def pathsL : Nat → List OTree → List (List Nat)
  | _, [] => []
  | i, k :: ks => (paths k).map (i :: ·) ++ pathsL (i + 1) ks
end

theorem mem_pathsL : ∀ (ks : List OTree) (j i : Nat) (k : OTree) (q : List Nat),
    ks[i]? = some k → q ∈ k.paths → (j + i) :: q ∈ pathsL j ks
  | [], _, _, _, _, h, _ => by simp at h
  | k' :: ks, j, 0, k, q, h, hq => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [pathsL, Nat.add_zero]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
  | k' :: ks, j, i + 1, k, q, h, hq => by
      simp only [List.getElem?_cons_succ] at h
      simp only [pathsL]
      have := mem_pathsL ks (j + 1) i k q h hq
      rw [show j + (i + 1) = j + 1 + i by omega]
      exact List.mem_append_right _ this

theorem mem_paths : ∀ (t : OTree) (p : List Nat) (n : OTree), t.node? p = some n → p ∈ t.paths
  | node _ _ _ ks, [], _, _ => by simp [paths]
  | node b Γ Δ ks, i :: p, n, h => by
      simp only [node?, kids] at h
      cases hk : ks[i]? with
      | none => rw [hk] at h; cases h
      | some k =>
        rw [hk] at h
        have := mem_pathsL ks 0 i k p hk (mem_paths k p n h)
        simp only [Nat.zero_add] at this
        exact List.mem_cons_of_mem _ this

theorem node?_append : ∀ (t : OTree) (p q : List Nat),
    t.node? (p ++ q) = (t.node? p).bind (·.node? q)
  | t, [], q => rfl
  | t, i :: p, q => by
      simp only [List.cons_append, node?]
      cases t.kids[i]? with
      | none => rfl
      | some k => exact node?_append k p q

end OTree

/-- The fields of a good node. -/
theorem Good.fields {n : OTree} (h : Good n) :
    PLLFormula.falsePLL ∉ n.ant ∧ (∀ A ∈ n.ant, A ∉ n.suc) ∧ Saturated n.isS n.ant n.suc ∧
    Demanded n.isS n.ant n.suc n.kids ∧ (∀ k ∈ n.kids, n.ant ⊆ k.ant) ∧
    (∀ k ∈ n.kids, Good k) := by
  cases h with
  | mk noBot disj sat dem sub good => exact ⟨noBot, disj, sat, dem, sub, good⟩

theorem good_node? : ∀ {t : OTree} (p : List Nat) {n : OTree}, Good t → t.node? p = some n →
    Good n
  | t, [], n, hg, h => by cases h; exact hg
  | t, i :: p, n, hg, h => by
      simp only [OTree.node?] at h
      cases hk : t.kids[i]? with
      | none => rw [hk] at h; cases h
      | some k =>
        rw [hk] at h
        exact good_node? p (hg.fields.2.2.2.2.2 k (List.mem_of_getElem? hk)) h

theorem ant_mono : ∀ {n : OTree} (q : List Nat) {n' : OTree}, Good n → n.node? q = some n' →
    n.ant ⊆ n'.ant
  | n, [], n', _, h => by cases h; exact fun _ h => h
  | n, i :: q, n', hg, h => by
      simp only [OTree.node?] at h
      cases hk : n.kids[i]? with
      | none => rw [hk] at h; cases h
      | some k =>
        rw [hk] at h
        have hmem := List.mem_of_getElem? hk
        exact fun _ hx => ant_mono q (hg.fields.2.2.2.2.2 k hmem) h
          (hg.fields.2.2.2.2.1 k hmem hx)

section Model
variable (t : OTree) (hg : Good t)

/-- The node of a world. -/
def nodeAt (a : {p : List Nat // (t.node? p).isSome = true}) : OTree := (t.node? a.1).get a.2

theorem node?_eq (a : {p : List Nat // (t.node? p).isSome = true}) :
    t.node? a.1 = some (nodeAt t a) := (Option.some_get a.2).symm

/-- **The model of an open tree.** -/
abbrev model : SubframeModel where
  W := {p : List Nat // (t.node? p).isSome = true}
  le a b := a.1.isPrefixOf b.1 = true
  S := {a | (nodeAt t a).isS = true}
  V x := {a | PLLFormula.prop x ∈ (nodeAt t a).ant}
  refl a := List.isPrefixOf_iff_prefix.mpr (List.prefix_refl _)
  trans h₁ h₂ := List.isPrefixOf_iff_prefix.mpr
    ((List.isPrefixOf_iff_prefix.mp h₁).trans (List.isPrefixOf_iff_prefix.mp h₂))
  hered {x u v} h hu := by
    obtain ⟨q, hq⟩ := List.isPrefixOf_iff_prefix.mp h
    have hv := node?_eq t v
    rw [← hq, OTree.node?_append, node?_eq t u] at hv
    exact ant_mono q (good_node? u.1 hg (node?_eq t u)) hv hu

instance : FinDec (model t hg) where
  elems := t.paths.filterMap fun p =>
    if h : (t.node? p).isSome = true then some ⟨p, h⟩ else none
  complete a := List.mem_filterMap.mpr
    ⟨a.1, OTree.mem_paths t a.1 _ (node?_eq t a), by simp [a.2]⟩
  decLe a b := inferInstanceAs (Decidable (a.1.isPrefixOf b.1 = true))
  decS a := inferInstanceAs (Decidable ((nodeAt t a).isS = true))
  decV x a := inferInstanceAs (Decidable (PLLFormula.prop x ∈ (nodeAt t a).ant))

/-- The good tree below a world. -/
theorem good_at (a : (model t hg).W) : Good (nodeAt t a) := good_node? a.1 hg (node?_eq t a)

/-- What holds at a world holds above it. -/
theorem ant_le {a b : (model t hg).W} (h : (model t hg).le a b) :
    (nodeAt t a).ant ⊆ (nodeAt t b).ant := by
  obtain ⟨q, hq⟩ := List.isPrefixOf_iff_prefix.mp h
  have hv := node?_eq t b
  rw [← hq, OTree.node?_append, node?_eq t a] at hv
  exact ant_mono q (good_at t hg a) hv

/-- A child of a world's node is the node of a world above it. -/
theorem kid_world (a : (model t hg).W) {k : OTree} (hk : k ∈ (nodeAt t a).kids) :
    ∃ b : (model t hg).W, (model t hg).le a b ∧ nodeAt t b = k := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
  have hb : t.node? (a.1 ++ [i]) = some k := by
    rw [OTree.node?_append, node?_eq t a]
    simp only [Option.bind_some, OTree.node?, hi]
  refine ⟨⟨a.1 ++ [i], by rw [hb]; rfl⟩, ?_, ?_⟩
  · exact List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _)
  · show (t.node? (a.1 ++ [i])).get _ = k
    simp only [hb, Option.get_some]

/-- **The truth lemma.** -/
theorem truth : ∀ (A : PLLFormula) (a : (model t hg).W),
    (A ∈ (nodeAt t a).ant → (model t hg).force a A) ∧
    (A ∈ (nodeAt t a).suc → ¬ (model t hg).force a A)
  | .prop x, a => ⟨fun h => h, fun h hx => (good_at t hg a).fields.2.1 _ hx h⟩
  | .falsePLL, a => ⟨fun h => (good_at t hg a).fields.1 h, fun _ h => h⟩
  | .and A B, a => by
      have F := (good_at t hg a).fields
      refine ⟨fun h => ?_, fun h hf => ?_⟩
      · obtain ⟨hA, hB⟩ := F.2.2.1.andL A B h
        exact ⟨(truth A a).1 hA, (truth B a).1 hB⟩
      · rcases F.2.2.1.andR A B h with hA | hB
        · exact (truth A a).2 hA hf.1
        · exact (truth B a).2 hB hf.2
  | .or A B, a => by
      have F := (good_at t hg a).fields
      refine ⟨fun h => ?_, fun h hf => ?_⟩
      · rcases F.2.2.1.orL A B h with hA | hB
        · exact .inl ((truth A a).1 hA)
        · exact .inr ((truth B a).1 hB)
      · obtain ⟨hA, hB⟩ := F.2.2.1.orR A B h
        rcases hf with hf | hf
        · exact (truth A a).2 hA hf
        · exact (truth B a).2 hB hf
  | .ifThen A B, a => by
      have F := (good_at t hg a).fields
      refine ⟨fun h b hab hA => ?_, fun h hf => ?_⟩
      · have hb := ant_le t hg hab h
        rcases (good_at t hg b).fields.2.2.1.impL A B hb with hA' | hB'
        · exact absurd hA ((truth A b).2 hA')
        · exact (truth B b).1 hB'
      · rcases Decidable.em (A ∈ (nodeAt t a).ant) with hA | hA
        · have hB := F.2.2.1.impLoc A B h hA
          exact (truth B a).2 hB (hf a ((model t hg).refl a) ((truth A a).1 hA))
        · obtain ⟨k, hk, _, hAk, hBk⟩ := F.2.2.2.1.impR A B h hA
          obtain ⟨b, hab, rfl⟩ := kid_world t hg a hk
          exact (truth B b).2 hBk (hf b hab ((truth A b).1 hAk))
  | .somehow A, a => by
      have F := (good_at t hg a).fields
      refine ⟨fun h b hab hbS => ?_, fun h hf => ?_⟩
      · have hb := ant_le t hg hab h
        exact (truth A b).1 ((good_at t hg b).fields.2.2.1.boxL A hbS hb)
      · cases hS : (nodeAt t a).isS with
        | true =>
          have hA := F.2.2.1.boxLoc A hS h
          exact (truth A a).2 hA (hf a ((model t hg).refl a) hS)
        | false =>
          obtain ⟨k, hk, hkS, hAk⟩ := F.2.2.2.1.boxR A hS h
          obtain ⟨b, hab, rfl⟩ := kid_world t hg a hk
          exact (truth A b).2 hAk (hf b hab hkS)

/-- The root world. -/
def rootW : (model t hg).W := ⟨[], rfl⟩

theorem nodeAt_root : nodeAt t (rootW t hg) = t := rfl

/-- **The root of an open tree refutes every sequent the tree covers.** -/
theorem root_refutes {s : SSeq} (hc : Covers t s) : Refutes (model t hg) (rootW t hg) s :=
  ⟨fun h => by show (nodeAt t (rootW t hg)).isS = true; rw [nodeAt_root, hc.1]; exact h,
   fun γ hγ => (truth t hg γ (rootW t hg)).1 (hc.2.1 hγ),
   fun δ hδ => (truth t hg δ (rootW t hg)).2 (hc.2.2 hδ)⟩

end Model

end SubTab
end PLLND

#axioms_within PLLND.SubTab.truth [propext, Quot.sound]
#axioms_within PLLND.SubTab.root_refutes [propext, Quot.sound]
