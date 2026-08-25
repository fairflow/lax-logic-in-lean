/-
# FRJ(◯) is incomplete: witness #80

The formula

    G80  =  (((¬¬◯⊥ ⊃ ◯⊥) ⊃ ◯¬◯⊥) ⊃ (◯¬◯⊥ ∨ ¬¬◯⊥))

is refuted by a 5-world Kripke model (so `¬ PLL G80`), yet the calculus
FRJ(◯) cannot derive the regular sequent `⇒ G80` either: the calculus
is incomplete as a countermodel constructor for PLL.

The underivability argument is a case analysis on the last rules of a
putative derivation:

  * the goal is an implication, so the last regular rule is `⊃∈`
    (axioms and joins conclude in prime, `∨`- or `◯`-formulas);
  * the premise concludes the disjunction `◯¬◯⊥ ∨ ¬¬◯⊥`, so its last
    rule is one of the `⋈^∨` joins, each of which requires an IRREGULAR
    premise with right formula `◯¬◯⊥`;
  * no irregular sequent with right formula `◯¬◯⊥` is derivable
    (`no_irregular_sigma`): `Ax^I` needs a prime right formula; `Ax^I◯`
    needs `classForce ats ¬◯⊥ = false` for a valuation `ats` drawn from
    the (empty) atom list of `G80`, but `classForce [] ¬◯⊥ = true`; and
    a `◯∉` inference would need a regular premise `Γ ⇒ ¬◯⊥`, whose last
    rule `⊃∈` puts `◯⊥ ∈ Cl(Γ)` above a premise `Γ ⇒ ⊥`.  By Lemma 3.9
    the extracted model's root then forces `Γ`, hence forces `◯⊥` (or
    `⊥` outright), while refuting `⊥`; so some world `c ≠ root` of the
    root's modal cone is fallible.  A fallible world forces `¬◯⊥`
    (fallibility is upward closed, so the consequent `⊥` holds above
    it), contradicting the pledge (`tag_cone`) that the whole cone
    refutes `¬◯⊥`.

Everything semantic is imported: `lemma39R`, `tag_cone`,
`preR_root_lbl` (FRJ/Sound.lean, FRJ/Extract.lean); the countermodel is
pinned as a `Search.Tab` table and checked by `decide`.
-/
import FRJ.Sound
import FRJ.Search.Pin
import Certified.Register

namespace FRJ80

open FRJ

/-! ## The formulas -/

def β : Form := .circ .bot            -- ◯⊥
def ν : Form := .imp β .bot           -- ¬◯⊥
def σ : Form := .circ ν               -- ◯¬◯⊥
def δ : Form := .imp ν .bot           -- ¬¬◯⊥
def ι : Form := .imp δ β              -- ¬¬◯⊥ ⊃ ◯⊥
def ρ12 : Form := .imp ι σ
def ρ9 : Form := .or σ δ
def G80 : Form := .imp ρ12 ρ9

/-! ## No irregular sequent has right formula `◯¬◯⊥` -/

/-- **The σ-kill.**  No irregular sequent `Σ ; Θ → ◯¬◯⊥` is derivable in
FRJ(G80).  Case analysis on the last rule; the essential case is `◯∉`,
killed semantically through Lemma 3.9 and the pledge (`tag_cone`). -/
theorem no_irregular_sigma : ∀ {St Th : List Form}, FRJi G80 St Th σ → False := by
  intro St Th e
  cases e
  case axI =>
      -- `Ax^I` needs a prime right formula; `◯¬◯⊥` is no prime.
      rename_i hF hg hTh
      exact absurd hF (by decide)
  case axIC =>
      -- `Ax^I◯` would need `classForce ats ¬◯⊥ = false` for some
      -- `ats ⊆ Ĝ_at`; `G80` has no atoms, so `ats = []`, and
      -- `classForce [] ¬◯⊥ = true`.
      rename_i ats hats hTh hFf hg
      have hgat : gAt G80 = [] := rfl
      have hnil : ats = [] := eq_nil_of_forall_not_mem
        (fun x hx => List.not_mem_nil (hgat ▸ hats hx))
      subst hnil
      exact Bool.noConfusion ((rfl : classForce [] ν = true).symm.trans hFf)
  case circNotIn =>
      -- `◯∉` with a regular premise `d : Γ' ⇒ ¬◯⊥` at tag `t'`.
      rename_i t' Γ' hTh2 d htag hg
      -- Invert the last rule of `d`: only `⊃∈` can conclude `¬◯⊥`
      -- (the joins and `Ax^R` need a prime or `∨`/`◯` right formula).
      cases d
      case axR => rename_i hF hg2 hΓ; exact absurd hF (by decide)
      case joinAt => rename_i hF hFnot hg2 hΓ; exact absurd hF (by decide)
      case joinAtP => rename_i hF hFnot hg2 hΓ; exact absurd hF (by decide)
      case joinAtF => rename_i hF hFnot hg2 hΓ; exact absurd hF (by decide)
      case impIn =>
          rename_i hA d₃ hg2
          -- `d₃ : Γ' ⇒ ⊥`, `hA : ◯⊥ ∈ Cl(Γ')`.  Lemma 3.9 on `d₃`:
          -- every world of the extracted model forces its own label,
          -- and the root refutes `⊥`.
          obtain ⟨hall, href⟩ := lemma39R d₃
          have hroot : ∀ X ∈ Γ', (modR d₃).force (modR d₃).root X := fun X hX =>
            hall (preR d₃).root X ((preR_root_lbl d₃ X).mpr hX)
          -- Closure inversion: `◯⊥ ∈ Cl(Γ')` means `◯⊥ ∈ Γ'` or `⊥ ∈ Γ'`.
          cases hA
          case circ hbot =>
              cases hbot
              case base hmem => exact href (hroot .bot hmem)
          case base hmem =>
              -- `◯⊥ ∈ Γ'`: the root forces `◯⊥`; instantiating its
              -- `∀`-clause at the root itself yields a fallible world
              -- `c` in the root's modal cone.
              have hβ := hroot β hmem
              obtain ⟨c, hrc, hcfal⟩ :=
                ((modR d₃).force_circ _ .bot).mp hβ (modR d₃).root
                  ((modR d₃).le_refl _)
              by_cases hc : c = (modR d₃).root
              · exact href (hc ▸ hcfal)
              · -- `c ≠ root`: the pledge says `c` refutes `¬◯⊥`, but a
                -- fallible world forces `¬◯⊥` — its consequent `⊥`
                -- holds everywhere above `c` by upward closure of
                -- fallibility.
                exact tag_cone d₃ ν htag c hrc hc
                  (((modR d₃).force_imp c β .bot).mpr
                    (fun b hb _ => (modR d₃).fal_mono hb hcfal))

/-! ## Underivability of the regular sequent -/

/-- FRJ(◯) does not derive `⇒ G80` in any context, at any tag.  The last
rule of a putative derivation must be `⊃∈`; its premise's last rule must
be a `⋈^∨` join; every such join has an irregular premise with right
formula `◯¬◯⊥`, which `no_irregular_sigma` refutes. -/
theorem not_provable_G80 : ¬ Provable G80 := by
  rintro ⟨t, Γ, ⟨d⟩⟩
  cases d
  case axR => rename_i hF hg hΓ; exact absurd hF (by decide)
  case joinAt => rename_i hF hFnot hg hΓ; exact absurd hF (by decide)
  case joinAtP => rename_i hF hFnot hg hΓ; exact absurd hF (by decide)
  case joinAtF => rename_i hF hFnot hg hΓ; exact absurd hF (by decide)
  case impIn =>
      rename_i hA d' hg
      -- `d' : Γ ⇒ ◯¬◯⊥ ∨ ¬¬◯⊥`
      cases d'
      case axR => rename_i hF hg2 hΓ; exact absurd hF (by decide)
      case joinAt => rename_i hF hFnot hg2 hΓ; exact absurd hF (by decide)
      case joinAtP => rename_i hF hFnot hg2 hΓ; exact absurd hF (by decide)
      case joinAtF => rename_i hF hFnot hg2 hΓ; exact absurd hF (by decide)
      case joinOr =>
          rename_i prem hJ1 hJ2 hcirc hΓ hC hg2
          obtain ⟨j, -, hj⟩ := List.mem_map.mp hC.1
          exact no_irregular_sigma (hj ▸ prem j)
      case joinOrP =>
          rename_i prem dps hJ1 hJ2 hJ5 hJ7 htag hΓ hC hg2
          obtain ⟨j, -, hj⟩ := List.mem_map.mp hC.1
          exact no_irregular_sigma (hj ▸ prem j)
      case joinOrF =>
          rename_i prem hJ1 hJ2 hΓ hC hg2
          obtain ⟨j, -, hj⟩ := List.mem_map.mp hC.1
          exact no_irregular_sigma (hj ▸ prem j)

/-! ## The countermodel: `G80` is not PLL-valid

The frame of `RNDB.sepM`: order edges 0<1, 0<2, 0<3, 0<4, 1<2, 1<3,
2<3 plus reflexivity; modal relation = reflexivity plus 2 R 3; world 3
fallible; empty valuation. -/

def sepT : FRJ.Search.Tab where
  n := 5
  root := 0
  leT := [[true,  true,  true,  true,  true],
          [false, true,  true,  true,  false],
          [false, false, true,  true,  false],
          [false, false, false, true,  false],
          [false, false, false, false, true]]
  rmT := [[true,  false, false, false, false],
          [false, true,  false, false, false],
          [false, false, true,  true,  false],
          [false, false, false, true,  false],
          [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

/-- The table denotes a Kripke model (frame conditions by `decide`). -/
def sepK : Kripke := sepT.toKripke (by decide) (by decide)

/-- The model refutes `G80` at its root: kernel-checked. -/
theorem sepK_refutes : ¬ sepK.force sepK.root G80 := by decide

theorem not_PLL_G80 : ¬ PLL G80 := fun h => sepK_refutes (h sepK)

/-! ## The incompleteness theorem -/

/-- **FRJ(◯) incompleteness, witness #80.**  `G80` is not PLL-valid, and
FRJ(◯) does not derive `⇒ G80`: the calculus settles the formula in
neither direction. -/
theorem frj_incompleteness_80 : ¬ PLL G80 ∧ ¬ Provable G80 :=
  ⟨not_PLL_G80, not_provable_G80⟩

/-! ## The completeness statement is REFUTED

`Certified.CompletenessFRJ` — until now OPEN, and never before
attackable because no `FinCM → FRJ.Kripke` transfer existed — falls to
the witness: the countermodel was rebuilt natively as `sepK`, so no
transfer is needed. -/

theorem not_CompletenessFRJ : ¬ Certified.CompletenessFRJ :=
  fun h => not_provable_G80 (h G80 not_PLL_G80)

/-! ## Axiom pins -/

/-- info: 'FRJ80.no_irregular_sigma' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_irregular_sigma

/-- info: 'FRJ80.not_provable_G80' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_provable_G80

/-- info: 'FRJ80.not_PLL_G80' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_PLL_G80

/-- info: 'FRJ80.frj_incompleteness_80' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frj_incompleteness_80

/-- info: 'FRJ80.not_CompletenessFRJ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_CompletenessFRJ

end FRJ80
