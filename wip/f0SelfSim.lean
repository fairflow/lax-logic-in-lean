import wip.f0T6
import Meta.Audit

/-!
# Self-similarity of F0: `⊥ ↦ t3` is a faithful embedding

`subBot a φ` substitutes the closed formula `a` for `⊥` in `φ` (atoms fixed);
`σ = subBot t3` with `t3 = ◯⊥ ∨ ¬◯⊥`.  On variable-free formulas `σ` is the
`rel` of `wip/f0T6.lean` (`rel_eq_sig`), and on the ladder
`σ (t n) ⊣⊢ rel (rn n)` (`sig_ladder`, through `σ(◯⊥) = ◯t3 ⊣⊢ ◯¬◯⊥`).

## 1. Preservation (Friedman's A-translation)

With `φᵃ` the A-translation (`aTr`: atoms `p ↦ p ∨ a`, `⊥ ↦ a`, connectives
and `◯` homomorphic), for every closed or open `a`:

    Γ ⊢ φ  ⟹  Γᵃ ⊢ φᵃ          (aTr_deriv)
    a ⊢ φᵃ                      (aTr_top)

On variable-free formulas `φᵃ = subBot a φ` (`subBot_eq_aTr`), so

    atomFree Γ, φ:   Γ ⊢ φ  ⟹  Γ[a/⊥] ⊢ φ[a/⊥]      (subBot_deriv)
    atomFree φ:      a ⊢ φ[a/⊥]                       (subBot_top)

**Correction to the brief.**  "`a ⊢ subBot a φ` for all `φ`" fails at atoms:
`[⊥] ⊢ p`, but `[t3] ⊬ p` (`cell_corr`).  The atom clause `p ↦ p ∨ a` is what
makes the induction go through for derivations with atoms.

## 2. Conjecture S: PROVED, for every formula

    ⊢ σ χ  ⟹  ⊢ χ          (sig_reflects; no atomFree hypothesis needed)
    σ φ ⊢ σ ψ  ⟹  φ ⊢ ψ    (sig_reflects_ctx)

Refutation stage first (designed cells, countermodels from the subframe
tableau, kernel-checked): `⊬ σ χ` for `χ ∈ {◯⊥, t3, t5, g1, c1 ∨ g1}`
(`cellS_e`, `cellS_t3`, `cellS_t5`, `cellS_g1`, `cellS_c1g1`).

**Proof.**  The subframe tableau decides PLL (`SubTab.complete`, choice-free):
`χ` has a closed tableau, or a finite subframe countermodel `M, r ⊮ χ`.  In the
second case extend `M` by two maximal worlds above every old world (`ext`):
`nT ∈ S` (so `◯⊥` fails there and `¬◯⊥` holds) and `eT ∉ S` (so `◯⊥` holds),
every atom true at both.  Then `t3 = σ⊥` fails at every old world and holds at
both tops, every `σ ψ` holds at both tops (`top_sig`), and at old worlds
(`orig_sig`)

    ext M, x ⊨ σ ψ   ⟺   M, x ⊨ ψ,

by induction on `ψ`: the tops satisfy every `σ`-formula, as a fallible world
satisfies everything.  So `ext M, r ⊮ σ χ`, against soundness.  The
construction needs no fallible worlds (subframe models have none); `cmU` of
`wip/f0T6.lean` is the case `M` = the RN ladder, read as a constraint model.

## 3. Corollaries (`sigN n = σⁿ`)

    ⊢ σⁿ χ ⟹ ⊢ χ;     atomFree φ, ψ:  φ ⊢ ψ ⟺ σⁿ φ ⊢ σⁿ ψ        (sigN_reflects, sigN_faithful)
    σ t3 = c1 ∨ (c1 ↠ t3) = c1 ∨ g1                                (sig_t3, by rfl)
    σⁿ ⊥ ⊢ σⁿ⁺¹ ⊥,   σⁿ⁺¹ ⊥ ⊬ σⁿ ⊥                                 (sigN_bot_strict)
    atomFree φ:  σⁿ ⊥ ⊢ σⁿ φ                                        (sigN_bot_le)
    ¬ ∃ φ, atomFree φ ∧ σⁿ⁺¹ φ ⊣⊢ σⁿ ⊥                             (copies_strict)

So `σⁿ` embeds F0 faithfully into `[σⁿ⊥, ⊤]`; the copies `σⁿ(F0)` are nested
(`σⁿ⁺¹ φ = σⁿ (σ φ)`, by definition) and strictly decreasing: an infinite
descending sequence of faithful copies of F0.

## The base: `◯a ≠ a` is necessary (negative control)

If `◯a ⊣⊢ a`, then `subBot a (◯⊥) = ◯a ⊣⊢ a = subBot a ⊥` while `◯⊥ ⊬ ⊥`, so
`subBot a` is not one-to-one (`box_fixed_not_injective`); for `a = ◯⊥`,
`◯◯⊥ ⊣⊢ ◯⊥` (`control_oBot`).  Which bases `a` work is not characterised here.

Pins `[propext, Quot.sound]` throughout.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace Sig

open SemUI RNEmbed
open PLLND.LaxInfinite (atomFree)

/-! ## The translations -/

/-- **Friedman's A-translation**: atoms `p ↦ p ∨ a`, `⊥ ↦ a`. -/
def aTr (a : PLLFormula) : PLLFormula → PLLFormula
  | .prop q => .or (.prop q) a
  | .falsePLL => a
  | .and A B => .and (aTr a A) (aTr a B)
  | .or A B => .or (aTr a A) (aTr a B)
  | .ifThen A B => .ifThen (aTr a A) (aTr a B)
  | .somehow A => .somehow (aTr a A)

/-- **`⊥ ↦ a`**, structurally (atoms fixed). -/
def subBot (a : PLLFormula) : PLLFormula → PLLFormula
  | .prop q => .prop q
  | .falsePLL => a
  | .and A B => .and (subBot a A) (subBot a B)
  | .or A B => .or (subBot a A) (subBot a B)
  | .ifThen A B => .ifThen (subBot a A) (subBot a B)
  | .somehow A => .somehow (subBot a A)

/-- `σ = subBot t3`. -/
def sig : PLLFormula → PLLFormula := subBot t3

/-- `σⁿ`. -/
def sigN : Nat → PLLFormula → PLLFormula
  | 0, φ => φ
  | n + 1, φ => sigN n (sig φ)

/-! ## 1. Preservation -/

theorem aTr_top (a : PLLFormula) : ∀ φ : PLLFormula, Deriv [a] (aTr a φ)
  | .prop _ => Deriv.orIntro2 (Deriv.iden (.head _))
  | .falsePLL => Deriv.iden (.head _)
  | .and A B => Deriv.andIntro (aTr_top a A) (aTr_top a B)
  | .or A _ => Deriv.orIntro1 (aTr_top a A)
  | .ifThen _ B => Deriv.impIntro (Deriv.rename (fun _ hx => .tail _ hx) (aTr_top a B))
  | .somehow A => (aTr_top a A).elim fun d => ⟨.laxIntro d⟩

/-- **The A-translation preserves derivability.** -/
theorem aTr_deriv (a : PLLFormula) {Γ : List PLLFormula} {φ : PLLFormula}
    (p : LaxND Γ φ) : Deriv (Γ.map (aTr a)) (aTr a φ) := by
  induction p with
  | iden h => exact Deriv.iden (List.mem_map.mpr ⟨_, h, rfl⟩)
  | falsoElim φ _ ih => exact Deriv.cutHead ih (aTr_top a φ)
  | impIntro _ ih => exact Deriv.impIntro ih
  | impElim _ _ ih₁ ih₂ => exact Deriv.impElim ih₁ ih₂
  | andIntro _ _ ih₁ ih₂ => exact Deriv.andIntro ih₁ ih₂
  | andElim1 _ ih => exact Deriv.andElim1 ih
  | andElim2 _ ih => exact Deriv.andElim2 ih
  | orIntro1 _ ih => exact Deriv.orIntro1 ih
  | orIntro2 _ ih => exact Deriv.orIntro2 ih
  | orElim _ _ _ ih₀ ih₁ ih₂ => exact Deriv.orElim ih₀ ih₁ ih₂
  | laxIntro _ ih => exact ih.elim fun d => ⟨.laxIntro d⟩
  | laxElim _ _ ih₁ ih₂ =>
      obtain ⟨d₁⟩ := ih₁
      obtain ⟨d₂⟩ := ih₂
      exact ⟨.laxElim d₁ d₂⟩

theorem subBot_eq_aTr (a : PLLFormula) :
    ∀ φ : PLLFormula, atomFree φ = true → subBot a φ = aTr a φ
  | .prop _, h => nomatch h
  | .falsePLL, _ => rfl
  | .and A B, h => by
      have h' : (atomFree A && atomFree B) = true := h
      show (subBot a A).and (subBot a B) = (aTr a A).and (aTr a B)
      rw [subBot_eq_aTr a A (band_true h').1, subBot_eq_aTr a B (band_true h').2]
  | .or A B, h => by
      have h' : (atomFree A && atomFree B) = true := h
      show (subBot a A).or (subBot a B) = (aTr a A).or (aTr a B)
      rw [subBot_eq_aTr a A (band_true h').1, subBot_eq_aTr a B (band_true h').2]
  | .ifThen A B, h => by
      have h' : (atomFree A && atomFree B) = true := h
      show (subBot a A).ifThen (subBot a B) = (aTr a A).ifThen (aTr a B)
      rw [subBot_eq_aTr a A (band_true h').1, subBot_eq_aTr a B (band_true h').2]
  | .somehow A, h => by
      show (subBot a A).somehow = (aTr a A).somehow
      rw [subBot_eq_aTr a A h]

/-- **`⊥ ↦ a` preserves derivability between variable-free formulas.** -/
theorem subBot_deriv (a : PLLFormula) {Γ : List PLLFormula} {φ : PLLFormula}
    (hΓ : ∀ ψ ∈ Γ, atomFree ψ = true) (hφ : atomFree φ = true) (h : Deriv Γ φ) :
    Deriv (Γ.map (subBot a)) (subBot a φ) := by
  obtain ⟨d⟩ := h
  have h1 := aTr_deriv a d
  rw [subBot_eq_aTr a φ hφ]
  refine Deriv.rename (fun x hx => ?_) h1
  obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨ψ, hψ, subBot_eq_aTr a ψ (hΓ ψ hψ)⟩

/-- **`a ⊢ φ[a/⊥]`** for variable-free `φ`. -/
theorem subBot_top (a : PLLFormula) {φ : PLLFormula} (hφ : atomFree φ = true) :
    Deriv [a] (subBot a φ) := by
  rw [subBot_eq_aTr a φ hφ]
  exact aTr_top a φ

theorem subBot_vf {a : PLLFormula} (ha : atomFree a = true) :
    ∀ φ : PLLFormula, atomFree φ = true → atomFree (subBot a φ) = true
  | .prop _, h => nomatch h
  | .falsePLL, _ => ha
  | .and A B, h => by
      have h' : (atomFree A && atomFree B) = true := h
      show (atomFree (subBot a A) && atomFree (subBot a B)) = true
      rw [subBot_vf ha A (band_true h').1, subBot_vf ha B (band_true h').2]
      rfl
  | .or A B, h => by
      have h' : (atomFree A && atomFree B) = true := h
      show (atomFree (subBot a A) && atomFree (subBot a B)) = true
      rw [subBot_vf ha A (band_true h').1, subBot_vf ha B (band_true h').2]
      rfl
  | .ifThen A B, h => by
      have h' : (atomFree A && atomFree B) = true := h
      show (atomFree (subBot a A) && atomFree (subBot a B)) = true
      rw [subBot_vf ha A (band_true h').1, subBot_vf ha B (band_true h').2]
      rfl
  | .somehow A, h => subBot_vf ha A h

theorem sig_vf {φ : PLLFormula} (h : atomFree φ = true) : atomFree (sig φ) = true :=
  subBot_vf rfl φ h

theorem sig_mono {φ ψ : PLLFormula} (hφ : atomFree φ = true) (hψ : atomFree ψ = true)
    (h : Deriv [φ] ψ) : Deriv [sig φ] (sig ψ) :=
  subBot_deriv t3 (fun χ hχ => by rw [List.mem_singleton.mp hχ]; exact hφ) hψ h

/-! ## Agreement with `rel` (round 4) -/

theorem rel_eq_sig : ∀ φ : PLLFormula, atomFree φ = true → T6.rel φ = sig φ
  | .prop _, h => nomatch h
  | .falsePLL, _ => rfl
  | .and A B, h => by
      have h' : (atomFree A && atomFree B) = true := h
      show (T6.rel A).and (T6.rel B) = (sig A).and (sig B)
      rw [rel_eq_sig A (band_true h').1, rel_eq_sig B (band_true h').2]
  | .or A B, h => by
      have h' : (atomFree A && atomFree B) = true := h
      show (T6.rel A).or (T6.rel B) = (sig A).or (sig B)
      rw [rel_eq_sig A (band_true h').1, rel_eq_sig B (band_true h').2]
  | .ifThen A B, h => by
      have h' : (atomFree A && atomFree B) = true := h
      show (T6.rel A).ifThen (T6.rel B) = (sig A).ifThen (sig B)
      rw [rel_eq_sig A (band_true h').1, rel_eq_sig B (band_true h').2]
  | .somehow A, h => by
      show (T6.rel A).somehow = (sig A).somehow
      rw [rel_eq_sig A h]

/-- `σ(◯⊥) = ◯t3 ⊣⊢ ◯¬◯⊥ = u`. -/
theorem sig_e_interd_u : Interd (sig e) T6.uF := by
  refine ⟨?_, ?_⟩
  · obtain ⟨d⟩ := (Deriv.toHead T6.t3_le_u : Deriv [t3, sig e] T6.uF)
    exact ⟨.laxElim (.iden (.head _)) d⟩
  · exact Deriv.somehowMono (Deriv.orIntro2 (Deriv.iden (.head _)))

/-- **On the ladder, `σ (t n) ⊣⊢ rel (rn n)`.** -/
theorem sig_ladder : ∀ k : Nat,
    Interd (sig (embed (rnP k).1)) (T6.rel (rnP k).1) ∧
      Interd (sig (embed (rnP k).2)) (T6.rel (rnP k).2)
  | 0 => ⟨sig_e_interd_u, Interd.imp_congr sig_e_interd_u (Interd.refl _)⟩
  | k + 1 =>
      let ih := sig_ladder k
      ⟨Interd.or_congr ih.1 ih.2, Interd.imp_congr (Interd.or_congr ih.1 ih.2) ih.1⟩

/-- `σ t3 = c1 ∨ (c1 ↠ t3) = c1 ∨ g1`. -/
theorem sig_t3 : sig t3 = (chainF 1).or (gap 1) := rfl

/-! ## The negative control: `◯a ⊣⊢ a` breaks injectivity -/

theorem box_fixed_not_injective {a : PLLFormula} (h : Interd (.somehow a) a) :
    Interd (subBot a e) (subBot a .falsePLL) ∧ ¬ Interd e .falsePLL :=
  ⟨h, fun hi => nd_e_bot hi.1⟩

/-- For `a = ◯⊥`: `◯◯⊥ ⊣⊢ ◯⊥`. -/
theorem control_oBot : Interd (subBot e e) (subBot e .falsePLL) :=
  ⟨⟨.laxElim (.iden (.head _)) (.iden (.head _))⟩, ⟨.laxIntro (.iden (.head _))⟩⟩

/-! ## Designed cells: the refutation stage, and the correction

Countermodels produced by the subframe tableau (`_out/gen7.lean`, untrusted),
checked here by `refutes` in the kernel. -/

-- e: countermodel, 3 worlds, refutes = true
def M_e : SubTab.SubCM :=
  ⟨3, 0, [[true, true, true], [false, true, true], [false, false, true]],
    [false, true, false],
    [[], [], []]⟩

-- t3: countermodel, 6 worlds, refutes = true
def M_t3 : SubTab.SubCM :=
  ⟨6, 0, [[true, true, true, true, true, true],
 [false, true, true, false, false, false],
 [false, false, true, false, false, false],
 [false, false, false, true, true, true],
 [false, false, false, false, true, false],
 [false, false, false, false, false, true]],
    [false, true, false, false, true, false],
    [[], [], [], [], [], []]⟩

-- t5: countermodel, 9 worlds, refutes = true
def M_t5 : SubTab.SubCM :=
  ⟨9, 0, [[true, true, true, true, true, true, true, true, true],
 [false, true, true, false, false, false, false, false, false],
 [false, false, true, false, false, false, false, false, false],
 [false, false, false, true, true, true, false, false, false],
 [false, false, false, false, true, false, false, false, false],
 [false, false, false, false, false, true, false, false, false],
 [false, false, false, false, false, false, true, true, true],
 [false, false, false, false, false, false, false, true, true],
 [false, false, false, false, false, false, false, false, true]],
    [false, true, false, false, true, false, false, true, false],
    [[], [], [], [], [], [], [], [], []]⟩

-- g1: countermodel, 7 worlds, refutes = true
def M_g1 : SubTab.SubCM :=
  ⟨7, 0, [[true, true, true, true, true, true, true],
 [false, true, true, true, true, true, true],
 [false, false, true, true, false, false, false],
 [false, false, false, true, false, false, false],
 [false, false, false, false, true, true, true],
 [false, false, false, false, false, true, false],
 [false, false, false, false, false, false, true]],
    [false, false, true, false, false, true, false],
    [[], [], [], [], [], [], []]⟩

-- c1g1: countermodel, 12 worlds, refutes = true
def M_c1g1 : SubTab.SubCM :=
  ⟨12, 0, [[true, true, true, true, true, true, true, true, true, true, true, true],
 [false, true, true, true, true, true, false, false, false, false, false, false],
 [false, false, true, false, false, false, false, false, false, false, false, false],
 [false, false, false, true, true, true, false, false, false, false, false, false],
 [false, false, false, false, true, false, false, false, false, false, false, false],
 [false, false, false, false, false, true, false, false, false, false, false, false],
 [false, false, false, false, false, false, true, true, true, true, true, true],
 [false, false, false, false, false, false, false, true, true, false, false, false],
 [false, false, false, false, false, false, false, false, true, false, false, false],
 [false, false, false, false, false, false, false, false, false, true, true, true],
 [false, false, false, false, false, false, false, false, false, false, true, false],
 [false, false, false, false, false, false, false, false, false, false, false, true]],
    [false, true, false, false, true, false, false, true, false, false, true, false],
    [[], [], [], [], [], [], [], [], [], [], [], []]⟩

-- corr: countermodel, 2 worlds, refutes = true
def M_corr : SubTab.SubCM :=
  ⟨2, 0, [[true, true], [false, true]],
    [false, false],
    [[], []]⟩


theorem cellS_e : ¬ Deriv [] (sig e) := fun h =>
  SubTab.SubCM.refutes_sound (m := M_e) (by decide +kernel) h
theorem cellS_t3 : ¬ Deriv [] (sig t3) := fun h =>
  SubTab.SubCM.refutes_sound (m := M_t3) (by decide +kernel) h
theorem cellS_t5 : ¬ Deriv [] (sig t5) := fun h =>
  SubTab.SubCM.refutes_sound (m := M_t5) (by decide +kernel) h
theorem cellS_g1 : ¬ Deriv [] (sig (gap 1)) := fun h =>
  SubTab.SubCM.refutes_sound (m := M_g1) (by decide +kernel) h
theorem cellS_c1g1 : ¬ Deriv [] (sig ((chainF 1).or (gap 1))) := fun h =>
  SubTab.SubCM.refutes_sound (m := M_c1g1) (by decide +kernel) h

/-- **The correction**: `[⊥] ⊢ p`, but `[t3] ⊬ p = subBot t3 p`. -/
theorem cell_corr : Deriv [.falsePLL] (.prop "p") ∧
    ¬ Deriv [subBot t3 .falsePLL] (subBot t3 (.prop "p")) :=
  ⟨Deriv.falsoElim _ (Deriv.iden (.head _)), fun h =>
    SubTab.SubCM.refutes_sound (m := M_corr) (by decide +kernel) (Deriv.impIntro h)⟩

/-! ## 2. Conjecture S -/

/-- Worlds of the extension: the old worlds and two tops. -/
inductive XW (W : Type) where
  | orig (x : W)
  | nT
  | eT

variable (M : SubframeModel)

def leX : XW M.W → XW M.W → Prop
  | .orig x, .orig y => M.le x y
  | .orig _, .nT => True
  | .orig _, .eT => True
  | .nT, .nT => True
  | .eT, .eT => True
  | _, _ => False

def inSX : XW M.W → Prop
  | .orig x => x ∈ M.S
  | .nT => True
  | .eT => False

def inVX (a : String) : XW M.W → Prop
  | .orig x => x ∈ M.V a
  | _ => True

theorem leX_refl : ∀ w : XW M.W, leX M w w
  | .orig x => M.refl x
  | .nT => trivial
  | .eT => trivial

theorem leX_trans {u v w : XW M.W} (h1 : leX M u v) (h2 : leX M v w) : leX M u w := by
  cases u <;> cases v <;> cases w <;>
    first
    | exact trivial
    | exact M.trans h1 h2
    | exact False.elim h1
    | exact False.elim h2

theorem inVX_hered {a : String} {u v : XW M.W} (h : leX M u v) (hu : inVX M a u) :
    inVX M a v := by
  cases u <;> cases v <;>
    first
    | exact trivial
    | exact M.hered h hu
    | exact False.elim h

/-- **The extension**: `nT ∈ S` and `eT ∉ S` above every old world. -/
def ext : SubframeModel where
  W := XW M.W
  le := leX M
  S := {w | inSX M w}
  V a := {w | inVX M a w}
  refl := leX_refl M
  trans := leX_trans M
  hered := fun h hu => inVX_hered M h hu

def isTopX : XW M.W → Prop
  | .orig _ => False
  | _ => True

theorem topX_up {u v : XW M.W} (hu : isTopX M u) (h : leX M u v) : isTopX M v := by
  cases u <;> cases v <;> first | exact trivial | exact False.elim hu | exact False.elim h

theorem not_e_nT : ¬ (ext M).force XW.nT e := fun h => h XW.nT trivial trivial

theorem e_eT : (ext M).force XW.eT e := by
  show ∀ v, leX M XW.eT v → inSX M v → False
  intro v hv hS
  cases v with
  | orig _ => exact False.elim hv
  | nT => exact False.elim hv
  | eT => exact hS

theorem t3_top {w : XW M.W} (hw : isTopX M w) : (ext M).force w t3 := by
  cases w with
  | orig _ => exact False.elim hw
  | nT =>
      refine Or.inr ?_
      show ∀ v, leX M XW.nT v → (ext M).force v e → (ext M).force v .falsePLL
      intro v hv hve
      cases v with
      | orig _ => exact False.elim hv
      | nT => exact not_e_nT M hve
      | eT => exact False.elim hv
  | eT => exact Or.inl (e_eT M)

theorem t3_orig (x : M.W) : ¬ (ext M).force (XW.orig x) t3 := by
  intro h
  rcases (h : (ext M).force (XW.orig x) e ∨ (ext M).force (XW.orig x) ne) with h | h
  · exact h XW.nT trivial trivial
  · exact h XW.eT trivial (e_eT M)

/-- **The tops satisfy every `σ`-formula.** -/
theorem top_sig : ∀ (ψ : PLLFormula) (w : XW M.W), isTopX M w → (ext M).force w (sig ψ)
  | .prop _, w, hw => by
      cases w with
      | orig _ => exact False.elim hw
      | nT => exact trivial
      | eT => exact trivial
  | .falsePLL, _, hw => t3_top M hw
  | .and A B, w, hw => ⟨top_sig A w hw, top_sig B w hw⟩
  | .or A _, w, hw => Or.inl (top_sig A w hw)
  | .ifThen _ B, w, hw => fun v hv _ => top_sig B v (topX_up M hw hv)
  | .somehow A, w, hw => fun v hv _ => top_sig A v (topX_up M hw hv)

/-- **At old worlds, `σ ψ` holds exactly where `ψ` holds in `M`.** -/
theorem orig_sig : ∀ (ψ : PLLFormula) (x : M.W),
    (ext M).force (XW.orig x) (sig ψ) ↔ M.force x ψ
  | .prop _, _ => Iff.rfl
  | .falsePLL, x => ⟨fun h => t3_orig M x h, False.elim⟩
  | .and A B, x => and_congr (orig_sig A x) (orig_sig B x)
  | .or A B, x => or_congr (orig_sig A x) (orig_sig B x)
  | .ifThen A B, x =>
      ⟨fun h y hxy hA => (orig_sig B y).mp (h (XW.orig y) hxy ((orig_sig A y).mpr hA)),
       fun h v hv hA => by
        cases v with
        | orig y => exact (orig_sig B y).mpr (h y hv ((orig_sig A y).mp hA))
        | nT => exact top_sig M B XW.nT trivial
        | eT => exact top_sig M B XW.eT trivial⟩
  | .somehow A, x =>
      ⟨fun h y hxy hS => (orig_sig A y).mp (h (XW.orig y) hxy hS),
       fun h v hv hS => by
        cases v with
        | orig y => exact (orig_sig A y).mpr (h y hv hS)
        | nT => exact top_sig M A XW.nT trivial
        | eT => exact False.elim hS⟩

/-- **Conjecture S, PROVED: `σ` reflects derivability** (every formula). -/
theorem sig_reflects (χ : PLLFormula) (h : Deriv [] (sig χ)) : Deriv [] χ := by
  rcases SubTab.complete χ with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact SubTab.holds_of_check hc
  · exfalso
    have hm0 : m.refutes χ = true := hm
    simp only [SubTab.SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm0
    have hr := (SubTab.SubCM.ok_parts hm0.1).1
    obtain ⟨d⟩ := h
    have hs := SubframeModel.CF.soundness d (ext (m.toModel hm0.1)) (XW.orig ⟨m.root, hr⟩)
      (fun _ hψ => nomatch hψ)
    have hf := (orig_sig (m.toModel hm0.1) χ ⟨m.root, hr⟩).mp hs
    have hb := (SubTab.SubCM.forceB_iff hm0.1 χ ⟨m.root, hr⟩).mpr hf
    rw [hm0.2] at hb
    exact Bool.false_ne_true hb

theorem sig_reflects_ctx {φ ψ : PLLFormula} (h : Deriv [sig φ] (sig ψ)) : Deriv [φ] ψ := by
  have h1 : Deriv [] (sig (φ.ifThen ψ)) := Deriv.impIntro h
  have h2 := sig_reflects _ h1
  exact Deriv.impElim (Deriv.rename (fun _ hx => by cases hx) h2) (Deriv.iden (.head _))

/-! ## 3. Corollaries -/

theorem sigN_imp : ∀ (n : Nat) (φ ψ : PLLFormula),
    sigN n (φ.ifThen ψ) = (sigN n φ).ifThen (sigN n ψ)
  | 0, _, _ => rfl
  | n + 1, φ, ψ => sigN_imp n (sig φ) (sig ψ)

theorem sigN_reflects : ∀ (n : Nat) (χ : PLLFormula), Deriv [] (sigN n χ) → Deriv [] χ
  | 0, _, h => h
  | n + 1, χ, h => sig_reflects χ (sigN_reflects n (sig χ) h)

theorem sigN_reflects_ctx (n : Nat) {φ ψ : PLLFormula}
    (h : Deriv [sigN n φ] (sigN n ψ)) : Deriv [φ] ψ := by
  have h1 : Deriv [] (sigN n (φ.ifThen ψ)) := by
    rw [sigN_imp]
    exact Deriv.impIntro h
  have h2 := sigN_reflects n _ h1
  exact Deriv.impElim (Deriv.rename (fun _ hx => by cases hx) h2) (Deriv.iden (.head _))

theorem sigN_vf : ∀ (n : Nat) {φ : PLLFormula}, atomFree φ = true → atomFree (sigN n φ) = true
  | 0, _, h => h
  | n + 1, _, h => sigN_vf n (sig_vf h)

theorem sigN_mono : ∀ (n : Nat) {φ ψ : PLLFormula}, atomFree φ = true → atomFree ψ = true →
    Deriv [φ] ψ → Deriv [sigN n φ] (sigN n ψ)
  | 0, _, _, _, _, h => h
  | n + 1, _, _, hφ, hψ, h => sigN_mono n (sig_vf hφ) (sig_vf hψ) (sig_mono hφ hψ h)

/-- **`σⁿ` is an order embedding of F0.** -/
theorem sigN_faithful (n : Nat) {φ ψ : PLLFormula} (hφ : atomFree φ = true)
    (hψ : atomFree ψ = true) : Deriv [φ] ψ ↔ Deriv [sigN n φ] (sigN n ψ) :=
  ⟨sigN_mono n hφ hψ, sigN_reflects_ctx n⟩

/-- **The copy `σⁿ(F0)` lies in `[σⁿ⊥, ⊤]`.** -/
theorem sigN_bot_le : ∀ (n : Nat) (φ : PLLFormula), atomFree φ = true →
    Deriv [sigN n .falsePLL] (sigN n φ)
  | 0, _, _ => Deriv.falsoElim _ (Deriv.iden (.head _))
  | n + 1, φ, hφ => sigN_mono n (φ := t3) (ψ := sig φ) rfl (sig_vf hφ) (subBot_top t3 hφ)

/-- **`σⁿ⊥` is strictly increasing.** -/
theorem sigN_bot_strict (n : Nat) :
    Deriv [sigN n .falsePLL] (sigN (n + 1) .falsePLL) ∧
      ([sigN (n + 1) .falsePLL] ⊬ sigN n .falsePLL) :=
  ⟨sigN_bot_le n t3 rfl, fun h => nd_t3_bot (sigN_reflects_ctx n (φ := t3) h)⟩

/-- **The copies are strictly nested**: `σⁿ⊥` is not in `σⁿ⁺¹(F0)`. -/
theorem copies_strict (n : Nat) :
    ¬ ∃ φ : PLLFormula, atomFree φ = true ∧ Interd (sigN (n + 1) φ) (sigN n .falsePLL) := by
  rintro ⟨φ, hφ, hi⟩
  exact (sigN_bot_strict n).2 (Deriv.cutHead (sigN_bot_le (n + 1) φ hφ) hi.1)

end Sig
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.Sig.aTr_top [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.aTr_deriv [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.subBot_eq_aTr [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.subBot_deriv [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.subBot_top [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.rel_eq_sig [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.sig_e_interd_u [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.sig_ladder [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.box_fixed_not_injective [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.control_oBot [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.cellS_e [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.cellS_t3 [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.cellS_t5 [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.cellS_g1 [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.cellS_c1g1 [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.cell_corr [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.orig_sig [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.sig_reflects [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.sig_reflects_ctx [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.sigN_reflects [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.sigN_faithful [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.sigN_bot_le [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.sigN_bot_strict [propext, Quot.sound]
#axioms_within PLLND.F0.Sig.copies_strict [propext, Quot.sound]
