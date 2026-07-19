import LaxLogic.PLLSemUICtx

/-!
# The one-world residue obstruction: the general fails-half, PROVED

Route doc §0(m) certified, per instance, that frame-relative
constraint-commutation fails on chain3 and the fork — each time by the
SAME one-world countermodel.  This file proves the general lemma the
instances were pointing at.

**The residue model** `residue n₀`: one world, infallible, both
relations total, and exactly one atom `n₀` true.  At its point the
◯-clause trivialises, and — for a constraint `C` that is *named with a
residue pair* (`ResiduePair n₀ bad C`: some pair `(α_{n₀}, ⋁ covers)`
with covers named in `bad`, every other pair named in `bad`, and
`n₀ ∉ bad`) — the constraint application collapses to the identity
(`residue_applyC`), so the whole translation `subC C` evaluates as if
`◯` were erased.  Such a `C` is exactly what Lemma 7's recipe produces
from a finite model with a NON-FALLIBLE Rₘ-stable world named `n₀`
(the covers and the other stable worlds carry the other names).

**The obstruction** (`residue_obstruction`, engine form): if a p-free
IPL formula θ derives `X` and holds at the residue point, then any
`IsIPCAll`-value `A` of `X` also holds there (spec + soundness), so
`A :: Θ` cannot derive any formula the residue point refutes, for any
frame theory Θ true at the point.

**Headlines**: with θ := the diagram `n₀ ∧ ⋀_{a ∈ bad} ¬a`,

* `fails_half_boxp_imp_p` — row `∀p.(◯p⊃p) = ⊥`: any IPC ∀p-value `A`
  of `(◯p⊃p)^C` is CONSISTENT with every `n₀`-avoiding frame theory of
  negated atoms: `A :: Θ ⊬ ⊥`.  Since the translated PLL value is
  `⊥^C = ⊥`, frame-relative commutation fails.
* `fails_half_box_lob` — row `∀p.◯(◯p⊃p) = ◯⊥`: likewise
  `A :: Θ ⊬ (◯⊥)^C`.

Both are fully general in the constraint (only the `ResiduePair` shape
is used) and in the frame theory.  Together with the sandwich
(`PLLSemUICtx.lean`) this closes the circle: the constraint route
computes the substitution fragment exactly, and no frame theory over
the same names can bridge the `lowT`/`sideT` gap — the constraint POOL
itself must grow.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open Ctx

/-! ## The residue model -/

/-- One infallible world, total relations, exactly the atom `n₀` true. -/
def residue (n₀ : String) : ConstraintModel where
  W := PUnit
  Ri := fun _ _ => True
  Rm := fun _ _ => True
  F := ∅
  V := fun a => {_u : PUnit | a = n₀}
  refl_i := fun _ => trivial
  trans_i := fun _ _ => trivial
  refl_m := fun _ => trivial
  trans_m := fun _ _ => trivial
  sub_mi := fun _ => trivial
  hered_F := fun _ h => h.elim
  hered_V := fun _ h => h
  full_F := fun h => h.elim

theorem residue_force_prop {n₀ a : String} {u : PUnit} :
    (residue n₀).force u (.prop a) ↔ a = n₀ := Iff.rfl

theorem residue_force_bot {n₀ : String} {u : PUnit} :
    ¬ (residue n₀).force u .falsePLL := fun h => h

theorem residue_force_ifThen {n₀ : String} {A B : PLLFormula} {u : PUnit} :
    (residue n₀).force u (A.ifThen B) ↔
      ((residue n₀).force u A → (residue n₀).force u B) := by
  constructor
  · intro h ha
    exact h u trivial ha
  · intro h v _ ha
    cases v; cases u
    exact h ha

/-! ## Named constraints with a residue pair -/

/-- The shape Lemma 7's recipe gives a constraint at a model with a
non-fallible Rₘ-stable world named `n₀`: that world's pair is present
with its covers named in `bad`, every other pair is named in `bad`,
and `n₀ ∉ bad`. -/
structure ResiduePair (n₀ : String) (bad : List String) (C : StdCtx) : Prop where
  pair : ∃ Ls, ((PLLFormula.prop n₀, Ctx.bigOr Ls) ∈ C ∧
    ∀ x ∈ Ls, ∃ a ∈ bad, x = PLLFormula.prop a)
  named : ∀ kl ∈ C, kl.1 = PLLFormula.prop n₀ ∨ ∃ a ∈ bad, kl.1 = PLLFormula.prop a
  fresh : n₀ ∉ bad

/-- **The collapse**: at the residue point, applying a residue-paired
constraint is the identity — `C[x]` is forced iff `x` is. -/
theorem residue_applyC {n₀ : String} {bad : List String} {C : StdCtx}
    (h : ResiduePair n₀ bad C) (x : PLLFormula) (u : PUnit) :
    (residue n₀).force u (applyC C x) ↔ (residue n₀).force u x := by
  constructor
  · intro hf
    obtain ⟨Ls, hmem, hLs⟩ := h.pair
    have hb := (force_applyC_iff (residue n₀) C x u).mp hf _ hmem
    have hxl := residue_force_ifThen.mp hb rfl
    rcases hxl with hx | hLor
    · exact hx
    · rcases (force_bigOr_iff (residue n₀) Ls u).mp hLor with ⟨q, hq, hqf⟩ | hF
      · obtain ⟨a, ha, rfl⟩ := hLs q hq
        exact absurd (residue_force_prop.mp hqf ▸ ha) h.fresh
      · exact hF.elim
  · intro hx
    refine (force_applyC_iff (residue n₀) C x u).mpr ?_
    rintro ⟨K, L⟩ hKL
    refine residue_force_ifThen.mpr fun hK => ?_
    exact Or.inl hx

/-- The translated `◯⊥` fails at the residue point. -/
theorem residue_not_subC_boxBot {n₀ : String} {bad : List String}
    {C : StdCtx} (h : ResiduePair n₀ bad C) {u : PUnit} :
    ¬ (residue n₀).force u (subC C PLLFormula.falsePLL.somehow) :=
  fun hf => residue_force_bot ((residue_applyC h _ u).mp hf)

/-! ## The diagram -/

/-- `¬a` as a formula. -/
def negA (a : String) : PLLFormula := (PLLFormula.prop a).ifThen .falsePLL

/-- The diagram of the residue point over the alphabet `n₀ :: bad`:
`⋀_{a ∈ bad} ¬a ∧ n₀`. -/
def diag (n₀ : String) (bad : List String) : PLLFormula :=
  bad.foldr (fun a acc => (negA a).and acc) (.prop n₀)

theorem diag_force_iff {n₀ : String} {bad : List String}
    (D : ConstraintModel) (w : D.W) :
    D.force w (diag n₀ bad) ↔
      (D.force w (.prop n₀) ∧ ∀ a ∈ bad, D.force w (negA a)) := by
  induction bad with
  | nil =>
      constructor
      · intro h
        exact ⟨h, fun a ha => absurd ha (List.not_mem_nil)⟩
      · intro h
        exact h.1
  | cons b bs ih =>
      constructor
      · rintro ⟨hb, hrest⟩
        obtain ⟨h₀, hall⟩ := ih.mp hrest
        refine ⟨h₀, fun a ha => ?_⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hb
        · exact hall a ha
      · rintro ⟨h₀, hall⟩
        exact ⟨hall b (List.mem_cons_self ..),
          ih.mpr ⟨h₀, fun a ha => hall a (List.mem_cons_of_mem _ ha)⟩⟩

theorem diag_pfree {p n₀ : String} {bad : List String}
    (hpn : p ≠ n₀) (hpb : p ∉ bad) : p ∉ (diag n₀ bad).atoms := by
  induction bad with
  | nil =>
      intro h
      exact hpn (by simpa [diag] using h)
  | cons b bs ih =>
      intro h
      have hb : p ≠ b := fun hpb' => hpb (hpb' ▸ List.mem_cons_self ..)
      have hbs : p ∉ bs := fun h' => hpb (List.mem_cons_of_mem _ h')
      rcases (by simpa [diag, negA] using h :
          p ∈ (PLLFormula.prop b).atoms ∨ p ∈ (diag n₀ bs).atoms) with h' | h'
      · exact hb (by simpa using h')
      · exact ih hbs h'

theorem diag_isIPL {n₀ : String} {bad : List String} :
    isIPL (diag n₀ bad) := by
  induction bad with
  | nil => trivial
  | cons b bs ih => exact ⟨⟨trivial, trivial⟩, ih⟩

/-- The residue point forces its own diagram. -/
theorem residue_diag {n₀ : String} {bad : List String} (hfr : n₀ ∉ bad) :
    (residue n₀).force PUnit.unit (diag n₀ bad) := by
  refine (diag_force_iff _ _).mpr ⟨rfl, fun a ha => ?_⟩
  refine residue_force_ifThen.mpr fun hpa => ?_
  exact absurd (residue_force_prop.mp hpa ▸ ha) hfr

/-! ## The diagram derives the translated rows (over ALL models) -/

/-- Core semantic step, row `◯p ⊃ p`: at any world of any model where
`n₀` holds and every `bad` atom is refuted, the translation
`(◯p⊃p)^C = C[p] ⊃ p` holds — a `C[p]`-world sees `p ∨ covers`; the
covers are `bad`-named, so forcing one makes the world fallible, and
fallible worlds force `p` anyway. -/
theorem sem_row1 {p n₀ : String} {bad : List String} {C : StdCtx}
    (h : ResiduePair n₀ bad C) (D : ConstraintModel) {w : D.W}
    (h₀ : D.force w (.prop n₀)) (hbad : ∀ a ∈ bad, D.force w (negA a)) :
    D.force w ((applyC C (.prop p)).ifThen (.prop p)) := by
  intro v hwv hv
  obtain ⟨Ls, hmem, hLs⟩ := h.pair
  have hb := (force_applyC_iff D C (.prop p) v).mp hv _ hmem
  have hpl := hb v (D.refl_i v) (D.force_hered hwv h₀)
  rcases hpl with hp | hLor
  · exact hp
  · rcases (force_bigOr_iff D Ls v).mp hLor with ⟨q, hq, hqf⟩ | hF
    · obtain ⟨a, ha, rfl⟩ := hLs q hq
      have hfall : D.force v .falsePLL :=
        D.force_hered hwv (hbad a ha) v (D.refl_i v) hqf
      exact D.force_of_fallible hfall
    · exact D.force_of_fallible hF

/-- The diagram derives `(◯p⊃p)^C`. -/
theorem diag_row1 {p n₀ : String} {bad : List String} {C : StdCtx}
    (h : ResiduePair n₀ bad C) :
    Nonempty (LaxND [diag n₀ bad]
      (subC C ((PLLFormula.prop p).somehow.ifThen (.prop p)))) := by
  refine completeness ?_
  intro D w hw
  have hd := (diag_force_iff D w).mp (hw _ (List.mem_singleton.mpr rfl))
  show D.force w ((applyC C (.prop p)).ifThen (.prop p))
  exact sem_row1 h D hd.1 hd.2

/-- The diagram derives `(◯(◯p⊃p))^C = C[(◯p⊃p)^C]`: the `n₀`-pairs
land in `sem_row1` one world up; the `bad`-named pairs are vacuous or
fallible. -/
theorem diag_row2 {p n₀ : String} {bad : List String} {C : StdCtx}
    (h : ResiduePair n₀ bad C) :
    Nonempty (LaxND [diag n₀ bad]
      (subC C ((PLLFormula.prop p).somehow.ifThen (.prop p)).somehow)) := by
  refine completeness ?_
  intro D w hw
  have hd := (diag_force_iff D w).mp (hw _ (List.mem_singleton.mpr rfl))
  show D.force w (applyC C ((applyC C (.prop p)).ifThen (.prop p)))
  refine (force_applyC_iff D C _ w).mpr ?_
  rintro ⟨K, L⟩ hKL
  intro v hwv hK
  rcases h.named _ hKL with hKn | ⟨a, ha, hKa⟩
  · refine Or.inl ?_
    exact sem_row1 h D (D.force_hered hwv hd.1)
      (fun a ha => D.force_hered hwv (hd.2 a ha))
  · have hKa' : K = PLLFormula.prop a := hKa
    subst hKa'
    have hfall : D.force v .falsePLL :=
      D.force_hered hwv (hd.2 a ha) v (D.refl_i v) hK
    exact D.force_of_fallible hfall

/-! ## The obstruction -/

/-- **Engine**: a p-free IPL premise θ that derives `X` and holds at
the residue point transports any `IsIPCAll`-value of `X` to the point
(spec + soundness); the point then blocks every derivation from
`A :: Θ` of anything it refutes. -/
theorem residue_obstruction {p n₀ : String} {X A ξ θ : PLLFormula}
    {Θ : List PLLFormula}
    (hA : IsIPCAll p isIPL X A)
    (hθp : p ∉ θ.atoms) (hθipl : isIPL θ)
    (hθX : Nonempty (LaxND [θ] X))
    (hθR : (residue n₀).force PUnit.unit θ)
    (hΘR : ∀ ψ ∈ Θ, (residue n₀).force PUnit.unit ψ)
    (hξR : ¬ (residue n₀).force PUnit.unit ξ) :
    ¬ Nonempty (LaxND (A :: Θ) ξ) := by
  rintro ⟨d⟩
  obtain ⟨dA⟩ := hA.greatest θ hθipl hθp hθX
  have hAR : (residue n₀).force PUnit.unit A :=
    soundness dA (residue n₀) PUnit.unit (fun ψ hψ => by
      rcases List.mem_singleton.mp hψ with rfl
      exact hθR)
  refine hξR (soundness d (residue n₀) PUnit.unit ?_)
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hAR
  · exact hΘR ψ hψ

/-- Frame theories of `n₀`-avoiding negated atoms hold at the point. -/
theorem residue_theta {n₀ : String} {Θ : List PLLFormula}
    (hΘ : ∀ ψ ∈ Θ, ∃ a, a ≠ n₀ ∧ ψ = negA a) :
    ∀ ψ ∈ Θ, (residue n₀).force PUnit.unit ψ := by
  intro ψ hψ
  obtain ⟨a, hne, rfl⟩ := hΘ ψ hψ
  exact residue_force_ifThen.mpr fun hpa =>
    absurd (residue_force_prop.mp hpa) hne

/-! ## The headlines: the general fails-half -/

/-- **General fails-half, row `∀p.(◯p⊃p) = ⊥`.**  For ANY constraint
`C` carrying a residue pair at `n₀` (the Lemma-7 shape at a
non-fallible Rₘ-stable world), ANY `IsIPCAll`-value `A` of the
translation `(◯p⊃p)^C`, and ANY frame theory `Θ` of `n₀`-avoiding
negated atoms (in particular the fallibility axioms):
`A :: Θ` is CONSISTENT.  The translated PLL value is
`(∀p.(◯p⊃p))^C = ⊥^C = ⊥`, so `A` is not `Θ`-equivalent to it —
frame-relative constraint-commutation FAILS, provably, at every such
constraint. -/
theorem fails_half_boxp_imp_p {p n₀ : String} {bad : List String}
    {C : StdCtx} {A : PLLFormula} {Θ : List PLLFormula}
    (h : ResiduePair n₀ bad C) (hpn : p ≠ n₀) (hpb : p ∉ bad)
    (hA : IsIPCAll p isIPL
      (subC C ((PLLFormula.prop p).somehow.ifThen (.prop p))) A)
    (hΘ : ∀ ψ ∈ Θ, ∃ a, a ≠ n₀ ∧ ψ = negA a) :
    ¬ Nonempty (LaxND (A :: Θ) .falsePLL) :=
  residue_obstruction hA (diag_pfree hpn hpb) diag_isIPL (diag_row1 h)
    (residue_diag h.fresh) (residue_theta hΘ) residue_force_bot

/-- **General fails-half, row `∀p.◯(◯p⊃p) = ◯⊥`** (the Löb/sideways
row): likewise `A :: Θ ⊬ (◯⊥)^C`. -/
theorem fails_half_box_lob {p n₀ : String} {bad : List String}
    {C : StdCtx} {A : PLLFormula} {Θ : List PLLFormula}
    (h : ResiduePair n₀ bad C) (hpn : p ≠ n₀) (hpb : p ∉ bad)
    (hA : IsIPCAll p isIPL
      (subC C ((PLLFormula.prop p).somehow.ifThen (.prop p)).somehow) A)
    (hΘ : ∀ ψ ∈ Θ, ∃ a, a ≠ n₀ ∧ ψ = negA a) :
    ¬ Nonempty (LaxND (A :: Θ) (subC C PLLFormula.falsePLL.somehow)) :=
  residue_obstruction hA (diag_pfree hpn hpb) diag_isIPL (diag_row2 h)
    (residue_diag h.fresh) (residue_theta hΘ) (residue_not_subC_boxBot h)

/-! ## The certified instance, re-derived from the general lemma

chain3's Lemma-7 constraint `C = [(a0, a1 ∨ ⊥), (a2, ⊥)]` with frame
theory `Θ = [¬a2]` — the §0(m) instance, now a corollary. -/

/-- chain3's constraint. -/
def chain3C : StdCtx :=
  [(PLLFormula.prop "a0", Ctx.bigOr [PLLFormula.prop "a1"]),
   (PLLFormula.prop "a2", Ctx.bigOr [])]

theorem chain3C_residue : ResiduePair "a0" ["a1", "a2"] chain3C where
  pair := ⟨[PLLFormula.prop "a1"], List.mem_cons_self ..,
    fun x hx => ⟨"a1", List.mem_cons_self .., by
      simpa using List.mem_singleton.mp hx⟩⟩
  named := by
    intro kl hkl
    rcases List.mem_cons.mp hkl with rfl | hkl
    · exact Or.inl rfl
    · rcases List.mem_cons.mp hkl with rfl | hkl
      · exact Or.inr ⟨"a2", by simp, rfl⟩
      · exact absurd hkl (List.not_mem_nil)
  fresh := by simp

/-- The §0(m) chain3 certificate, generalised: EVERY IPC ∀p-value of
`(◯p⊃p)^{chain3C}` is consistent with the fallibility axiom `¬a2`. -/
theorem chain3_fails_half {A : PLLFormula}
    (hA : IsIPCAll "p" isIPL
      (subC chain3C ((PLLFormula.prop "p").somehow.ifThen (.prop "p"))) A) :
    ¬ Nonempty (LaxND [A, negA "a2"] .falsePLL) :=
  fails_half_boxp_imp_p chain3C_residue (by simp) (by simp) hA
    (fun ψ hψ => ⟨"a2", by simp, List.mem_singleton.mp hψ ▸ rfl⟩)

end SemUI
end PLLND
