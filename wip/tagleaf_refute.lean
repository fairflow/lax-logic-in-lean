/-
# `TagLeafV` is UNINHABITED — the lift's interface cannot be proved away

`wip/minmodv_liftmain.lean` reduces `hloc` to the interface `TagLeafV`,
and the campaign's open item 1 asked whether reached instances are
always constructible.  They are not: this file exhibits an infallible
countermodel `(K₂, G)` for which `TagLeafV K₂ G` is EMPTY, so no proof
of `∀ K G, TagLeafV K G` exists and `completenessV_lift` cannot be
completed by inhabiting its hypothesis.

The obstruction is soundness of the tag, not a search budget:

**Lemma (`not_clo_of_tagged`).**  For `d : FRJVr G t Γ C` whose tag
satisfies the `◯∈`/`◯∉` side condition at `C`, both `Clo Γ C` and
`Clo Γ (◯C)` are impossible.  `lemma39R` forces the whole of `Γ` at the
root of `Mod(d)` and refutes `C` there; `tag_cone` refutes `C` on the
rest of the root's modal cone; so the root can force neither `C` nor
`◯C`.

**The cell.**  `K₂` is the 2-chain `⊥ ≤ ⊤` with `Rm = ≤`, `p` true at
`⊤` only, no fallible world; `G = ◯p ⊃ p` (the co-unit — PLL-invalid,
and refuted at the root of `K₂`).  At the root:

    Λ*_⊥ = [◯p]      (⊥ ⊩ ◯p, ⊥ ⊮ p)          — circ-carrying
    Λ*_⊤ = [p]       (⊤ ⊩ p)

and `C = p` is refuted at `⊥`, forced at the proper `Rm`-successor `⊤`,
`⊥` is a sole refuter, and no world above carries a `Λ*` inside the
`Ax^R` context `Ĝ_at \ {p} = []`.  So every hypothesis of `TagLeafV`
holds — the round-3 hypotheses `hsole` and `hax` included — while its
conclusion `RegWitV K₂ G ⊥ p` would need a tagged row whose context
contains `◯p` (anchor `⊥`) or `p` (anchor `⊤`).  Both are refuted by
the lemma.

**What this does and does not say.**  It does NOT refute (LIFT) — the
V-engine derives `◯p ⊃ p` outright, from `Λ*_⊥ = {◯p}`, with a BLOCKED
tag (a fallible join), and the completeness recursion reaches that cell
at the FREE grade where the blocked tag is accepted.  It says the
TAGGED demand is strictly stronger than provability, so the route
forward is to weaken what the `◯∉` consumer asks of its premise row,
not to inhabit `TagLeafV`.  Per the V5 licence rule
(`docs/refat-plan.md`) this is a kernel-checked separating cell.
-/
import wip.minmodv_liftmain
import FRJ.SoundV

namespace FRJ.V

/-- **A tagged row retains neither its goal nor the goal's `◯`.** -/
theorem not_clo_of_tagged {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJVr G t Γ C)
    (ht : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C) :
    ¬ Clo Γ C ∧ ¬ Clo Γ (.circ C) := by
  obtain ⟨ha, hb⟩ := lemma39R d
  have hroot : ∀ X ∈ Γ, (modR d).force (modR d).root X := fun X hX =>
    ha (preR d).root X ((preR_root_lbl d X).mpr hX)
  refine ⟨fun hc => hb (clo_forces hroot hc), fun hc => ?_⟩
  refine Kripke.not_force_circ (modR d) ?_ (clo_forces hroot hc)
  intro u hu hf
  by_cases hru : u = (modR d).root
  · exact hb (hru ▸ hf)
  · exact tag_cone d C ht u hu hru hf

/-- The two corollaries the cell uses: a tagged row's context contains
neither `C` nor `◯C`. -/
theorem not_mem_of_tagged {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJVr G t Γ C)
    (ht : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C) :
    C ∉ Γ ∧ Form.circ C ∉ Γ :=
  ⟨fun h => (not_clo_of_tagged d ht).1 (.base h),
   fun h => (not_clo_of_tagged d ht).2 (.base h)⟩

end FRJ.V

namespace FRJ.TagLeafRefute

open Form

/-- The 2-chain `false ≤ true`, `Rm = ≤`, `p` at the top, infallible. -/
def K2 : Kripke where
  W := Bool
  elems := [false, true]
  complete := by decide
  decEq := inferInstance
  le := fun a b => a = true → b = true
  le_refl := fun _ h => h
  le_trans := fun hab hbc h => hbc (hab h)
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all
  root := false
  root_le := by intro a h; exact absurd h (by simp)
  V := fun w s => w = true ∧ s = "p"
  V_mono := fun hab _ hV => ⟨hab hV.1, hV.2⟩
  Rm := fun a b => a = true → b = true
  rm_refl := fun _ h => h
  rm_trans := fun hab hbc h => hbc (hab h)
  sub_mi := fun h => h
  Fal := fun _ => False
  fal_mono := fun _ h => h
  fal_V := fun h => h.elim
  decLe := fun a b => inferInstanceAs (Decidable (a = true → b = true))
  decV := fun w s => inferInstanceAs (Decidable (w = true ∧ s = "p"))
  decRm := fun a b => inferInstanceAs (Decidable (a = true → b = true))
  decFal := fun _ => isFalse (fun h => h)

theorem K2_infallible : K2.Infallible := fun _ h => h

/-- `p`, and the co-unit goal `◯p ⊃ p`. -/
def pv : Form := .atom "p"
def GC : Form := .imp (.circ pv) pv

/-- `true ⊩ p`. -/
theorem force_top_p : K2.force true pv := ⟨rfl, rfl⟩

/-- `false ⊮ p`. -/
theorem not_force_bot_p : ¬ K2.force false pv := fun h => Bool.noConfusion h.1

/-- `false ⊩ ◯p`: every world sees `true`, which forces `p`. -/
theorem force_bot_circ_p : K2.force false (.circ pv) :=
  fun _ _ => ⟨true, fun _ => rfl, force_top_p⟩

/-- The root refutes `G`: the antecedent `◯p` holds there while `p` fails. -/
theorem not_valid_GC : ¬ K2.valid GC := fun h =>
  not_force_bot_p (h false (fun h => h) force_bot_circ_p)

/-! ## The two `Λ*` facts, by evaluation -/

theorem circ_mem_lamStar_bot : Form.circ pv ∈ lamStar K2 false GC := by
  refine mem_lamStar.mpr ⟨by decide, ?_⟩
  exact ⟨force_bot_circ_p, not_force_bot_p⟩

theorem p_mem_lamStar_top : pv ∈ lamStar K2 true GC := by
  refine mem_lamStar.mpr ⟨by decide, ?_⟩
  exact ⟨rfl, rfl⟩

theorem hcirc_bot : circPart (lamStar K2 false GC) ≠ [] := by
  intro h
  have : Form.circ pv ∈ circPart (lamStar K2 false GC) :=
    List.mem_filter.mpr ⟨circ_mem_lamStar_bot, rfl⟩
  rw [h] at this
  exact absurd this List.not_mem_nil

/-! ## Every `TagLeafV` hypothesis holds at `(false, p)` -/

theorem hC : pv ∈ sfR GC := by decide

theorem hsucc : ∃ c, K2.Rm false c ∧ c ≠ false ∧ K2.force c pv :=
  ⟨true, fun _ => rfl, by simp, force_top_p⟩

theorem hsole : ∀ u, K2.le false u → u ≠ false → K2.force u pv := by
  intro u _ hne
  match u, hne with
  | true, _ => exact force_top_p
  | false, hne => exact absurd rfl hne

/-- `Ĝ_at \ {p} = []`, so no world's `Λ*` fits the `Ax^R` context: the
root's holds `◯p`, the top's holds `p`. -/
theorem hax : pv.isPrime = true → ∀ v, K2.le false v →
    ¬ (lamStar K2 v GC ⊆ rm (gAt GC) pv) := by
  intro _ v _ hsub
  have hnil : rm (gAt GC) pv = [] := by decide
  match v with
  | false =>
      have := hsub circ_mem_lamStar_bot
      rw [hnil] at this
      exact absurd this List.not_mem_nil
  | true =>
      have := hsub p_mem_lamStar_top
      rw [hnil] at this
      exact absurd this List.not_mem_nil

/-! ## The refutation -/

/-- **`TagLeafV K₂ GC` is empty.**  Its conclusion at `(false, p)` would
be a tagged row deriving `p` whose context contains `◯p` (if anchored at
`false`) or `p` (if anchored at `true`); `not_mem_of_tagged` refutes
both. -/
theorem tagLeafV_K2_GC_uninhabited : TagLeafV K2 GC → False := by
  intro tl
  have w := tl false pv hC not_force_bot_p (Or.inl rfl) hcirc_bot hsucc hsole hax
  obtain ⟨hnC, hnOC⟩ := V.not_mem_of_tagged w.der w.tOK
  have hcov : lamStar K2 w.wld GC ⊆ w.ctx := w.cov
  cases hw : w.wld with
  | false => rw [hw] at hcov; exact hnOC (hcov circ_mem_lamStar_bot)
  | true => rw [hw] at hcov; exact hnC (hcov p_mem_lamStar_top)

/-- **The campaign statement: the lift's interface is not provable.**
There is an infallible countermodel whose `TagLeafV` is empty, so
`completenessV_lift` can never be discharged by inhabiting it. -/
theorem no_universal_tagLeafV :
    ¬ (∀ (K : Kripke) (G : Form), K.Infallible → ¬ K.valid G →
        Nonempty (TagLeafV K G)) := by
  intro h
  obtain ⟨tl⟩ := h K2 GC K2_infallible not_valid_GC
  exact tagLeafV_K2_GC_uninhabited tl

/-! ## The general criterion: a STUCK ATOM empties the interface

The `K₂` cell is not special.  Call `(w, p)` a **stuck atom** for `G`
when `p` is a variable with `p ∈ Sf^R(G)`, `p ∈ Sf^L(G)`, `◯p ∈ Sf^L(G)`,
and

    w ⊮ p,    w ⊩ ◯p,    ∀ u > w, u ⊩ p.

Then `◯p ∈ Λ*_w` (so `w` is circ-carrying and has a proper `Rm`-successor
forcing `p`), and `p ∈ Λ*_v` for every `v > w` (an atom's `⊩*` is its
valuation).  So EVERY anchor a `RegWitV` could pick is poisoned: at `w`
it must swallow `◯p`, above `w` it must swallow `p` — and
`not_mem_of_tagged` forbids both.  No enumeration is involved: the
hypotheses are read off the two `Λ*` computations. -/

theorem tagLeafV_empty_of_stuckAtom {K : Kripke} {G : Form} {w : K.W}
    {x : String}
    (hCR : Form.atom x ∈ sfR G) (hCL : Form.atom x ∈ sfL G)
    (hOCL : Form.circ (Form.atom x) ∈ sfL G)
    (hnf : ¬ K.force w (.atom x)) (hOC : K.force w (.circ (.atom x)))
    (hsole : ∀ u, K.le w u → u ≠ w → K.force u (.atom x)) :
    TagLeafV K G → False := by
  intro tl
  have hOCmem : Form.circ (Form.atom x) ∈ lamStar K w G :=
    mem_lamStar.mpr ⟨hOCL, ⟨hOC, hnf⟩⟩
  have hcirc : circPart (lamStar K w G) ≠ [] := by
    intro h
    have hm : Form.circ (Form.atom x) ∈ circPart (lamStar K w G) :=
      List.mem_filter.mpr ⟨hOCmem, rfl⟩
    rw [h] at hm
    exact absurd hm List.not_mem_nil
  have hsucc : ∃ c, K.Rm w c ∧ c ≠ w ∧ K.force c (.atom x) := by
    obtain ⟨c, hrc, hcC⟩ := hOC w (K.le_refl w)
    exact ⟨c, hrc, fun h => hnf (h ▸ hcC), hcC⟩
  -- above `w` the atom itself sits in `Λ*`; at `w` the `◯` does
  have hmem : ∀ v, K.le w v → v ≠ w → Form.atom x ∈ lamStar K v G :=
    fun v hwv hvw => mem_lamStar.mpr ⟨hCL, hsole v hwv hvw⟩
  have hax : (Form.atom x).isPrime = true → ∀ v, K.le w v →
      ¬ (lamStar K v G ⊆ rm (gAt G) (.atom x)) := by
    intro _ v hwv hsub
    by_cases hvw : v = w
    · subst hvw
      have hin := rm_subset (hsub hOCmem)
      exact Bool.noConfusion (List.mem_filter.mp hin).2
    · exact (mem_rm.mp (hsub (hmem v hwv hvw))).1 rfl
  have wit := tl w (.atom x) hCR hnf (Or.inl rfl) hcirc hsucc hsole hax
  obtain ⟨hnC, hnOC⟩ := V.not_mem_of_tagged wit.der wit.tOK
  have hcov : lamStar K wit.wld G ⊆ wit.ctx := wit.cov
  by_cases hvw : wit.wld = w
  · rw [hvw] at hcov
    exact hnOC (hcov hOCmem)
  · exact hnC (hcov (hmem wit.wld wit.wle hvw))

/-- The `K₂` cell is the criterion at `x = "p"`, `w = ⊥` — a consistency
control on the two proofs. -/
theorem tagLeafV_K2_GC_uninhabited' : TagLeafV K2 GC → False :=
  tagLeafV_empty_of_stuckAtom (x := "p") (by decide) (by decide) (by decide)
    not_force_bot_p force_bot_circ_p hsole

/-- info: 'FRJ.TagLeafRefute.tagLeafV_empty_of_stuckAtom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tagLeafV_empty_of_stuckAtom

/-! ## The control: the SAME cell IS provable

`K₂` is cone-grounded (`Rm = ≤`), hence endpoint-seeing, so the peer
campaign's two-tier recursion already proves `ProvableV GC`.  The
interface is therefore strictly stronger than the theorem it was meant
to serve: at `(K₂, GC)` the calculus derives the goal while
`TagLeafV K₂ GC` is empty.  (The V-engine exhibits the derivation
concretely — `Λ*_⊥ = {◯p} ⇒ ◯p ⊃ p` with a BLOCKED tag, i.e. through a
fallible join, which the FREE grade of `minModL` accepts and the TAGGED
grade cannot.) -/

theorem K2_coneGrounded : K2.ConeGrounded := by
  intro a hct u hu
  cases a with
  | false => exact Bool.noConfusion (hct true (fun _ => rfl))
  | true => exact hu rfl

theorem provableV_GC : ProvableV GC :=
  completenessV_of_endpoints K2 (endpoints_of_coneGrounded K2_coneGrounded)
    not_valid_GC

/-- info: 'FRJ.TagLeafRefute.provableV_GC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_GC

/-- info: 'FRJ.V.not_clo_of_tagged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FRJ.V.not_clo_of_tagged

/-- info: 'FRJ.TagLeafRefute.tagLeafV_K2_GC_uninhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tagLeafV_K2_GC_uninhabited

/-- info: 'FRJ.TagLeafRefute.no_universal_tagLeafV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_universal_tagLeafV

end FRJ.TagLeafRefute
