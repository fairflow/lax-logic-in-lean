/-
# Completeness of FRJ(G) — Section 6

The direct route (Lemma `minMod`, Theorem `minMod`), which the paper
records in a footnote as the completeness proof of the TABLEAUX 2017
version.  We prove the EXISTENCE half of Lemma 6.4: the rank bounds (i)
and (iii) serve minimality, which is out of scope, and dropping them
costs nothing in the construction.

Setting: `K` a countermodel for `G`, `α` a world, and

* `α ⊩* H` iff `α ⊩ H` and either `H ∈ PV`, or `H = A ⊃ B` and `α ⊮ A`;
* `Λ_α  = {A ∈ Sf^L(G) | α ⊩ A}`;
* `Λ*_α = {A ∈ Sf^L(G) | α ⊩* A}`;
* `Ω_α  = {C ∈ Sf^R(G) | α ⊮ C}`.

Note that `Λ*_α ⊆ Ĝ` by construction — its members are variables or
implications — which is what lets it appear on the left of a sequent.

**Constructive metatheory.**  The paper is classical, and forms `Λ*_α`
by classical comprehension.  We do not need to: `Kripke` carries a world
enumeration together with decidable order and valuation, so forcing is
DECIDABLE (`decForce`), `Λ*_α` is an ordinary `List.filter`, and the
height of a world is a `List.countP`.  Nothing here depends on
`Classical.choice`, and the construction computes.
-/
import FRJ.Sound

namespace FRJ

open Form

namespace Kripke

variable (K : Kripke)

/-- `α ⊩* H`: "`α ⊩ H` and either `H ∈ PV` or `H = A ⊃ B` and `α ⊮ A`".
For every other shape of `H` this is false, so the formulas satisfying it
are variables and implications only. -/
def forceStar (a : K.W) : Form → Prop
  | .atom p => K.V a p
  | .imp A B => K.force a (.imp A B) ∧ ¬ K.force a A
  | .circ A => K.force a (.circ A) ∧ ¬ K.force a A
  | _ => False

theorem forceStar_force {a : K.W} : ∀ {H : Form}, K.forceStar a H → K.force a H := by
  intro H h
  cases H with
  | atom p => exact h
  | bot => exact h.elim
  | and A B => exact h.elim
  | or A B => exact h.elim
  | imp A B => exact h.1
  | circ A => exact h.1

/-- A formula satisfying `⊩*` is a variable, an implication, or (W4) a
`◯`-formula — the three determining shapes, i.e. the three zones of
`Ĝ`. -/
theorem forceStar_shape {a : K.W} : ∀ {H : Form},
    K.forceStar a H → H.isPV ∨ H.isImp ∨ H.isCirc := by
  intro H h
  cases H with
  | atom p => exact Or.inl rfl
  | bot => exact h.elim
  | and A B => exact h.elim
  | or A B => exact h.elim
  | imp A B => exact Or.inr (Or.inl rfl)
  | circ A => exact Or.inr (Or.inr rfl)

/-- `⊩*` is decidable, because `⊩` is. -/
instance decForceStar (K : Kripke) (a : K.W) :
    ∀ H : Form, Decidable (K.forceStar a H)
  | .atom p => K.decV a p
  | .bot => inferInstanceAs (Decidable False)
  | .and _ _ => inferInstanceAs (Decidable False)
  | .or _ _ => inferInstanceAs (Decidable False)
  | .imp A B =>
      inferInstanceAs (Decidable (K.force a (.imp A B) ∧ ¬ K.force a A))
  | .circ A =>
      inferInstanceAs (Decidable (K.force a (.circ A) ∧ ¬ K.force a A))

end Kripke

/-- `Λ*_α`.  A filter, not a classical comprehension. -/
def lamStar (K : Kripke) (a : K.W) (G : Form) : List Form :=
  (sfL G).filter (fun H => decide (K.forceStar a H))

theorem mem_lamStar {K : Kripke} {a : K.W} {G H : Form} :
    H ∈ lamStar K a G ↔ (H ∈ sfL G ∧ K.forceStar a H) := by
  simp [lamStar, List.mem_filter]

/-- `Λ*_α ⊆ Ĝ`: this is what lets it stand on the left of a sequent. -/
theorem lamStar_subset_gHat {K : Kripke} {a : K.W} {G : Form} :
    lamStar K a G ⊆ gHat G := by
  intro H hH
  obtain ⟨hsf, hst⟩ := mem_lamStar.mp hH
  rcases K.forceStar_shape hst with h | h | h
  · exact List.mem_append_left _
      (List.mem_append_left _ (List.mem_filter.mpr ⟨hsf, h⟩))
  · exact List.mem_append_left _
      (List.mem_append_right _ (List.mem_filter.mpr ⟨hsf, h⟩))
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hsf, h⟩)

/-- `Λ*` carries no modal formula (its members are variables and
implications), so the stable zones of the completeness construction have
empty modal parts — which is what the barren joins' side condition
needs. -/
theorem circPart_lamStar_nil {K : Kripke} {a : K.W} {G : Form}
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    {l : List Form} (hsub : l ⊆ lamStar K a G) : circPart l = [] := by
  refine eq_nil_of_forall_not_mem (fun X hX => ?_)
  have hsf := (mem_lamStar.mp (hsub (circPart_subset hX))).1
  have hc := (List.mem_filter.mp hX).2
  rw [hcf X (List.mem_append_right _ hsf)] at hc
  exact Bool.noConfusion hc

theorem unionAll_circPart_nil {K : Kripke} {a : K.W} {G : Form} {n : Nat}
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    {stab : Fin (n + 1) → List Form} (hsub : ∀ j, stab j ⊆ lamStar K a G) :
    unionAll (fun j => circPart (stab j)) = [] := by
  refine eq_nil_of_forall_not_mem (fun X hX => ?_)
  obtain ⟨j, hj⟩ := mem_unionAll.mp hX
  rw [circPart_lamStar_nil hcf (hsub j)] at hj
  exact List.not_mem_nil hj

/-- For a `◯`-free goal, a member of `Λ*` cannot be a `◯`-formula.
(W4: no longer unconditional — `Λ*` now carries the modal zone.) -/
theorem lamStar_not_circ {K : Kripke} {a : K.W} {G : Form} {X : Form}
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (hX : X ∈ lamStar K a G) (hc : X.isCirc = true) : False := by
  rw [hcf X (List.mem_append_right _ (mem_lamStar.mp hX).1)] at hc
  exact Bool.noConfusion hc

/-- **At a `≤`-maximal world the modal part of `Λ*` is empty** — with no
world strictly above, `Rm`-successors collapse to the world itself
(`sub_mi` + maximality), so a forced `◯Y` forces `Y` and the `⊩*`-clause
excludes it.  This is what terminates W4's pledge recursion: at maximal
anchors the barren joins suffice and the tag is `barren` for free
(`docs/frj-w4.md` §3). -/
theorem circPart_lamStar_nil_of_maximal {K : Kripke} {a : K.W} {G : Form}
    (hmax : ∀ b, K.le a b → b = a) :
    circPart (lamStar K a G) = [] := by
  refine eq_nil_of_forall_not_mem (fun X hX => ?_)
  have hmem := circPart_subset hX
  have hc := (List.mem_filter.mp hX).2
  match X, hc with
  | .circ Y, _ =>
      obtain ⟨-, hfY, hnY⟩ : (Form.circ Y ∈ sfL G) ∧ K.force a (.circ Y) ∧
          ¬ K.force a Y := by
        obtain ⟨h1, h2⟩ := mem_lamStar.mp hmem
        exact ⟨h1, h2.1, h2.2⟩
      obtain ⟨u, hru, huY⟩ := hfY a (K.le_refl a)
      exact hnY ((hmax u (K.sub_mi hru)) ▸ huY)

/-- Everything in `Λ*_α` is forced at `α`. -/
theorem forces_lamStar {K : Kripke} {a : K.W} {G : Form} :
    K.forces a (lamStar K a G) :=
  fun _ hH => K.forceStar_force (mem_lamStar.mp hH).2

/-- Hence everything in `Cl(Λ*_α)` is forced at `α` — one half of the
paper's Lemma 6.5, and the half that holds for arbitrary formulas. -/
theorem forces_clo_lamStar {K : Kripke} {a : K.W} {G X : Form}
    (h : Clo (lamStar K a G) X) : K.force a X :=
  clo_forces forces_lamStar h

/-- **Lemma 6.5, the direction the construction uses**: a left subformula
forced at `α` lies in `Cl(Λ*_α)`.

DIVERGENCE (recorded in `docs/frj-fidelity.md`): the paper states this as
the set equality `Λ_α = Cl(Λ_α) = Cl(Λ*_α)`.  Taken literally the first
equality is false — `Cl` is generated by a grammar in which `A` ranges
over ALL formulas, so `Cl(Λ_α)` contains `Z ⊃ C` for arbitrary `Z`,
which need not lie in `Sf^L(G)` and so not in `Λ_α`.  Its proof also has
a step ("`α ⊩ A ∧ B`, hence `A ∧ B ∈ Λ_α`") that silently needs
`A ∧ B ∈ Sf^L(G)`.  What the rest of the paper actually uses are the two
directions proved here and in `forces_clo_lamStar`, and both are true.

**W4.**  The W1 side condition (`Sf^L(G)` `◯`-free) is GONE: `Λ*` now
carries the modal zone through the `⊩*`-clause for `◯`, and the `◯`-case
below is the exact analogue of the `⊃`-case — body forced: recurse and
close under `Clo.circ`; body unforced: `◯X` is determining data and sits
in `Λ*` literally.  Lemma 6.5 holds for every goal of the modal
signature; only infallibility remains, for `⊥`. -/
theorem mem_clo_lamStar {K : Kripke} {a : K.W} {G : Form}
    (hinf : K.Infallible) :
    ∀ {A : Form}, A ∈ sfL G → K.force a A → Clo (lamStar K a G) A := by
  intro A
  induction A with
  | atom p =>
      intro hsf hf
      exact .base (mem_lamStar.mpr ⟨hsf, hf⟩)
  | bot =>
      -- W3: at a FALLIBLE world `⊥` is forced and `Cl(Λ*)` cannot reach it
      -- (`Λ*` carries variables and implications only), so this direction
      -- of Lemma 6.5 — and with it the completeness construction — is a
      -- statement about infallible models.
      intro _ hf
      exact absurd ((K.force_bot a).mp hf) (hinf a)
  | and A B ihA ihB =>
      intro hsf hf
      obtain ⟨hA, hB⟩ := sfL_and hsf
      exact .and (ihA hA hf.1) (ihB hB hf.2)
  | or A B ihA ihB =>
      intro hsf hf
      obtain ⟨hA, hB⟩ := sfL_or hsf
      rcases hf with hf | hf
      · exact .orL (ihA hA hf)
      · exact .orR (ihB hB hf)
  | imp A B ihA ihB =>
      intro hsf hf
      obtain ⟨hA, hB⟩ := sfL_imp hsf
      by_cases hfa : K.force a A
      · exact .imp (ihB hB (hf a (K.le_refl a) hfa))
      · exact .base (mem_lamStar.mpr ⟨hsf, ⟨hf, hfa⟩⟩)
  | circ A ihA =>
      intro hsf hf
      by_cases hfa : K.force a A
      · exact .circ (ihA (sfL_circ hsf) hfa)
      · exact .base (mem_lamStar.mpr ⟨hsf, ⟨hf, hfa⟩⟩)

/-- `Λ*` grows along `≤`, modulo closure: if `α ≤ β` then everything in
`Λ*_α` lies in `Cl(Λ*_β)`.  (Used where the construction moves to a
world above.) -/
theorem lamStar_mono {K : Kripke} {a b : K.W} {G : Form}
    (hinf : K.Infallible) (hab : K.le a b) :
    ∀ X ∈ lamStar K a G, Clo (lamStar K b G) X := by
  intro X hX
  obtain ⟨hsf, hst⟩ := mem_lamStar.mp hX
  exact mem_clo_lamStar hinf hsf (K.force_mono hab (K.forceStar_force hst))

/-! ## Deleting the fallible worlds

For a `◯`-free goal, a fallible countermodel can be replaced by an
infallible one: the infallible worlds form a down-set, `◯`-free forcing
never looks at `Rm`, and the failure witnesses of `⊃` are never fallible
(a fallible world forces every consequent).  This is what connects the
soundness theorem — whose extracted model may use declared fallible
worlds — back to the completeness construction, which consumes an
infallible countermodel. -/

/-- `K` restricted to its infallible worlds.  Needs the root infallible,
which every countermodel's root is (`fal_force`). -/
def Kripke.infPart (K : Kripke) (hr : ¬ K.Fal K.root) : Kripke where
  W := {w : K.W // ¬ K.Fal w}
  elems := (K.elems.filter (fun w => decide (¬ K.Fal w))).attachWith _
    (fun w hw => of_decide_eq_true (List.mem_filter.mp hw).2)
  complete := by
    rintro ⟨w, hw⟩
    rw [List.mem_attachWith]
    exact List.mem_filter.mpr ⟨K.complete w, decide_eq_true hw⟩
  decEq := fun a b =>
    have : DecidableEq K.W := K.decEq
    decidable_of_iff (a.1 = b.1) Subtype.ext_iff.symm
  le a b := K.le a.1 b.1
  le_refl a := K.le_refl a.1
  le_trans := K.le_trans
  le_antisymm h h' := Subtype.ext (K.le_antisymm h h')
  root := ⟨K.root, hr⟩
  root_le a := K.root_le a.1
  V a p := K.V a.1 p
  V_mono h p hp := K.V_mono h p hp
  Rm a b := K.Rm a.1 b.1
  rm_refl a := K.rm_refl a.1
  rm_trans := K.rm_trans
  sub_mi := K.sub_mi
  Fal _ := False
  fal_mono _ h := h
  fal_V h := h.elim
  decLe a b := K.decLe a.1 b.1
  decV a p := K.decV a.1 p
  decRm a b := K.decRm a.1 b.1
  decFal _ := isFalse (fun h => h)

/-- **`◯`-free forcing is preserved by the restriction.**  The one
interesting case is `⊃` right-to-left: a failure witness `v ⊩ A`, `v ⊮ B`
in `K` cannot be fallible (it would force `B`), so it survives. -/
theorem infPart_force {K : Kripke} (hr : ¬ K.Fal K.root) :
    ∀ (A : Form), (∀ X ∈ sf A, X.isCirc = false) →
    ∀ (w : K.W) (hw : ¬ K.Fal w),
      ((K.infPart hr).force ⟨w, hw⟩ A ↔ K.force w A) := by
  intro A
  induction A with
  | atom p => exact fun _ _ _ => Iff.rfl
  | bot =>
      intro _ w hw
      exact ⟨fun h => h.elim, fun h => absurd h hw⟩
  | and A B ihA ihB =>
      intro hsf w hw
      have hA := ihA (fun X hX => hsf X (by simp only [sf, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hX))) w hw
      have hB := ihB (fun X hX => hsf X (by simp only [sf, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hX))) w hw
      simp only [Kripke.force_and, hA, hB]
  | or A B ihA ihB =>
      intro hsf w hw
      have hA := ihA (fun X hX => hsf X (by simp only [sf, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hX))) w hw
      have hB := ihB (fun X hX => hsf X (by simp only [sf, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hX))) w hw
      simp only [Kripke.force_or, hA, hB]
  | imp A B ihA ihB =>
      intro hsf w hw
      have hsfA : ∀ X ∈ sf A, X.isCirc = false :=
        fun X hX => hsf X (by simp only [sf, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hX))
      have hsfB : ∀ X ∈ sf B, X.isCirc = false :=
        fun X hX => hsf X (by simp only [sf, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hX))
      simp only [Kripke.force_imp]
      constructor
      · intro hf v hwv hvA
        by_cases hfv : K.Fal v
        · exact K.fal_force B hfv
        · exact (ihB hsfB v hfv).mp
            (hf ⟨v, hfv⟩ hwv ((ihA hsfA v hfv).mpr hvA))
      · intro hf v hwv hvA
        exact (ihB hsfB v.1 v.2).mpr (hf v.1 hwv ((ihA hsfA v.1 v.2).mp hvA))
  | circ A _ =>
      intro hsf
      have := hsf (.circ A) (self_mem_sf (.circ A))
      simp [Form.isCirc] at this

/-- Every subformula of `G` is a left or a right subformula. -/
theorem mem_sfRL_of_sf {G : Form} :
    ∀ {A : Form}, (A ∈ sfR G ∨ A ∈ sfL G) → ∀ {X : Form}, X ∈ sf A →
      (X ∈ sfR G ∨ X ∈ sfL G) := by
  intro A
  induction A with
  | atom p =>
      intro hA X hX
      simp only [sf, List.mem_singleton] at hX
      exact hX ▸ hA
  | bot =>
      intro hA X hX
      simp only [sf, List.mem_singleton] at hX
      exact hX ▸ hA
  | and A B ihA ihB =>
      intro hA X hX
      simp only [sf, List.mem_cons, List.mem_append] at hX
      rcases hX with rfl | hX | hX
      · exact hA
      · exact ihA (hA.elim (fun h => Or.inl (sfR_and h).1)
          (fun h => Or.inr (sfL_and h).1)) hX
      · exact ihB (hA.elim (fun h => Or.inl (sfR_and h).2)
          (fun h => Or.inr (sfL_and h).2)) hX
  | or A B ihA ihB =>
      intro hA X hX
      simp only [sf, List.mem_cons, List.mem_append] at hX
      rcases hX with rfl | hX | hX
      · exact hA
      · exact ihA (hA.elim (fun h => Or.inl (sfR_or h).1)
          (fun h => Or.inr (sfL_or h).1)) hX
      · exact ihB (hA.elim (fun h => Or.inl (sfR_or h).2)
          (fun h => Or.inr (sfL_or h).2)) hX
  | imp A B ihA ihB =>
      intro hA X hX
      simp only [sf, List.mem_cons, List.mem_append] at hX
      rcases hX with rfl | hX | hX
      · exact hA
      · exact ihA (hA.elim (fun h => Or.inr (sfR_imp h).1)
          (fun h => Or.inl (sfL_imp h).1)) hX
      · exact ihB (hA.elim (fun h => Or.inl (sfR_imp h).2)
          (fun h => Or.inr (sfL_imp h).2)) hX
  | circ A ihA =>
      intro hA X hX
      simp only [sf, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact hA
      · exact ihA (hA.elim (fun h => Or.inl (sfR_circ h))
          (fun h => Or.inr (sfL_circ h))) hX

/-- The `hcf` hypothesis extends from the two polarity sets to ALL
subformulas of `G`. -/
theorem sf_circFree_of_hcf {G : Form}
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false) :
    ∀ X ∈ sf G, X.isCirc = false := by
  intro X hX
  rcases mem_sfRL_of_sf (Or.inl (sfR_self G)) hX with h | h
  · exact hcf X (List.mem_append_left _ h)
  · exact hcf X (List.mem_append_right _ h)

/-- **A fallible countermodel of a `◯`-free goal yields an infallible
one.**  W3's open item (4), closed. -/
theorem infallible_countermodel {K : Kripke} {G : Form}
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (hK : ¬ K.valid G) :
    ∃ K' : Kripke, K'.Infallible ∧ ¬ K'.valid G := by
  have hr : ¬ K.Fal K.root := fun hf => hK (K.fal_force G hf)
  refine ⟨K.infPart hr, fun _ h => h, fun hv => hK ?_⟩
  exact (infPart_force hr G (sf_circFree_of_hcf hcf) K.root hr).mp hv

/-! ## The height of a world

The paper's main induction is on `h(α)`, the length of the longest chain
above `α`, which decreases as one moves up.  On a finite poset the
cardinality of the strict up-set does the same job and is easier to
handle. -/

/-- `h(α)`, realised as the number of worlds strictly above `α`, counted
over the model's own enumeration.  (`Finset.card` would need `Fintype`,
and `Fintype.ofFinite` costs `Classical.choice`.) -/
def ht (K : Kripke) (a : K.W) : Nat :=
  K.elems.countP (fun b => decide (K.le a b ∧ b ≠ a))

/-- Moving strictly up strictly decreases the height. -/
theorem ht_lt {K : Kripke} {a b : K.W} (hab : K.le a b) (hne : b ≠ a) :
    ht K b < ht K a := by
  refine countP_lt_countP ?_ (K.complete b) ?_ ?_
  · intro c _ hc
    simp only [decide_eq_true_eq] at hc ⊢
    refine ⟨K.le_trans hab hc.1, ?_⟩
    intro hca
    exact hne (K.le_antisymm (hca ▸ hc.1) hab)
  · simp only [decide_eq_true_eq]
    exact ⟨hab, hne⟩
  · simp

/-! ## The minimal `η`

The paper's "without loss of generality" choice of a world `η ≥ α` with
`η ⊩ A`, `η ⊮ B` and no world strictly between forcing `A`.  This has to
be DATA: the derivation the completeness construction builds from it must
compute, and extracting a witness from an existence proof is choice. -/

/-- The candidate worlds. -/
def etaCand (K : Kripke) (a : K.W) (A B : Form) : List K.W :=
  K.elems.filter (fun x => decide (K.le a x ∧ K.force x A ∧ ¬ K.force x B))

theorem mem_etaCand {K : Kripke} {a : K.W} {A B : Form} {e : K.W} :
    e ∈ etaCand K a A B ↔ (K.le a e ∧ K.force e A ∧ ¬ K.force e B) := by
  simp [etaCand, List.mem_filter, K.complete e]

/-- `α ⊮ A ⊃ B` means there is a candidate.  Constructive, because
forcing is decidable. -/
theorem etaCand_ne_nil {K : Kripke} {a : K.W} {A B : Form}
    (h : ¬ K.force a (.imp A B)) : etaCand K a A B ≠ [] := by
  intro hn
  refine h ?_
  rw [Kripke.force_imp]
  intro b hab hbA
  by_cases hbB : K.force b B
  · exact hbB
  · exact absurd (mem_etaCand.mpr ⟨hab, hbA, hbB⟩) (by rw [hn]; exact List.not_mem_nil)

/-- The paper's minimal `η`, as data. -/
structure MinEta (K : Kripke) (a : K.W) (A B : Form) : Type where
  e : K.W
  le : K.le a e
  fA : K.force e A
  nfB : ¬ K.force e B
  min : ∀ d : K.W, K.le a d → K.le d e → d ≠ e → ¬ K.force d A

/-- Take a candidate of maximal height: no candidate lies strictly below
it, which is the minimality the paper asks for.  `maxOn` rather than
`List.argmax`, whose specification lemmas carry `Classical.choice`. -/
def minEta {K : Kripke} {a : K.W} {A B : Form}
    (h : ¬ K.force a (.imp A B)) : MinEta K a A B :=
  match hc : etaCand K a A B with
  | [] => absurd hc (etaCand_ne_nil h)
  | c :: cs =>
      let e := maxOn (fun x => ht K x) c cs
      have hspec := mem_etaCand.mp (hc ▸ maxOn_mem (fun x => ht K x) c cs)
      { e := e
        le := hspec.1
        fA := hspec.2.1
        nfB := hspec.2.2
        min := by
          intro d had hde hdne hdA
          have hdB : ¬ K.force d B := fun hcc => hspec.2.2 (K.force_mono hde hcc)
          have hdmem : d ∈ c :: cs := hc ▸ mem_etaCand.mpr ⟨had, hdA, hdB⟩
          exact absurd (le_maxOn (fun x => ht K x) c cs d hdmem)
            (Nat.not_le.mpr (ht_lt hde hdne.symm)) }


end FRJ
