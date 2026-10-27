import wip.f0SigOnto
import wip.f0Normal
import Meta.Audit

/-!
# Does `[t3, ⊤]` contain the free Heyting algebra on countably many generators?

F0 is the Lindenbaum algebra of the variable-free PLL formulas; `t3 = ◯⊥ ∨ ¬◯⊥`,
and `[t3, ⊤]` is a Heyting algebra with bottom `t3`, the `∧`, `∨`, `↠` of F0 and
the relative negation `x ↦ x ↠ t3` (`[t3, ⊤]` is closed under them since
`b ≤ a ↠ b`).

## The statement (Matthew, 2026-10-27)

For a generator assignment `x : String → PLLFormula` (the propositional
variables are the strings; `x a` is the variable-free formula substituted for
the variable `a`), the relativisation is

    h A := A[a := x a, ⊥ := t3]                       (`relG x`)

and the statement is

    FreeIPLInAboveT3 :=
      ∃ x, (∀ a, atomFree (x a)) ∧ (∀ a, t3 ≤ x a) ∧
        ∀ A B ◯-free,  [A] ⊢ B  ⟺  [h A] ⊢ h B.

The left side is IPC derivability (`LaxND` on ◯-free formulas, by
conservativity).  The brief's candidate generators were the odd gaps
`oddGap i = g(2i+1)` (`gap`, `wip/gapWidth.lean`), independent in F0
(`indep`, `wip/f0Indep.lean`).

## Results

**REFUTED** (`not_FreeIPLInAboveT3`), for EVERY choice of generators, already
with two: for all variable-free `x₀`, `x₁` some signed conjunction lies below
`t3` (`noFreeHA2`),

    ∃ ε : Bool × Bool,  ⊢ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3,        x^true = x,  x^false = x ↠ t3,

while `¬(p^ε₁ ∧ q^ε₂)` is no theorem of IPC (`ipc_negConj`, the one-world model
with valuation `ε`).  So `A = ⊤`, `B = ¬(p^ε₁ ∧ q^ε₂)` has `[A] ⊬ B` and
`[h A] ⊢ h B` (`not_faithful`).

**The reason.**  In a subframe model let `R = {t3 fails}` and `G = {t3 holds}`.
`G = Gₑ ⊔ Gₙ`, `Gₑ = {◯⊥ holds}`, `Gₙ = {¬◯⊥ holds}`, both upward closed, and
every variable-free formula is CONSTANT on each (`force_e_iff_Te`,
`force_ne_iff_Tn`): on `Gₑ` it takes its classical value with `◯A ↦ ⊤`, on `Gₙ`
with `◯A ↦ A`.  A world of `R` maximal in `R` therefore has a theory determined
by two bits, whether an `R`-world above it is in `S` and whether a `Gₙ`-world
lies above it (`rmax_force`), and `(false, false)` is impossible
(`rmax_inS_or_hasN`).  Three types of maximal world, four sign patterns: one
pattern is missing, and its signed conjunction fails at every `R`-world of
every finite subframe model (an `R`-maximal world lies above it,
`exists_rmax`), so its relative negation is a theorem (`SubTab.complete`).  The
same count with `⊥` for `t3` has two types (the two kinds of maximal world),
which is why F0 itself has no free pair either; the relativisation to `t3`
adds exactly one type.

**The designed cells** (kernel-checked, certificates from the subframe
tableau): for the odd gaps, `g3 ↠ t3 ⊣⊢ t3` (`cell_g3_dneg`: `h(¬¬q) = ⊤`
for `q ↦ g3`, since `t7 = t5 ∨ t6` holds at every `R`-maximal world),
`(g1 ↠ t3) ↠ t3 ⊬` and `g1 ∨ (g1 ↠ t3) ⊬` (`g1` survives the one-variable
cells); for the pair `(u, t4)`, `u ∧ t4 ≤ t3` (`cell_u_t4`, the missing
pattern `(true, true)`).  The type patterns `(Tmax s n x₀, Tmax s n x₁)` are
`oddGap_patterns` and `u_t4_patterns`.

**PROVED** (`freeIPL1`): one generator works, `h₁ A = σ(A[p := ◯⊥])`, i.e.
`p ↦ ◯t3 = σ(◯⊥)`, `⊥ ↦ t3`: `[t3, ⊤]` contains the Rieger–Nishimura lattice
with bottom `t3`,

    [t3] ⊢ h₁ p   and   ∀ A B ◯-free over p,  [A] ⊢ B  ⟺  [h₁ A] ⊢ h₁ B.

Preservation is `deriv_substP` then `sig_mono`; reflection is
`sig_reflects_ctx` then the faithfulness of `p ↦ ◯⊥` on one-variable IPC
formulas (`not_deriv_of_sep`, `wip/rnEmbed.lean`) on a subframe countermodel
of `A ↠ B` read as a one-variable Kripke skeleton (`toSkel`).

Pins `[propext, Quot.sound]` throughout; no `Classical.choice` (the route is
`SubTab.complete` and the `FinDec` semantics of `LaxLogic/PLL/SubTab/Semantics.lean`).
Status note: `wip/f0FreeIPL-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace FreeIPL

open SemUI RNEmbed Sig
open PLLND.LaxInfinite (atomFree)

/-! ## The relativisation and the statement -/

/-- **The relativisation** `h A = A[a := x a, ⊥ := t3]` for a generator
assignment `x`; homomorphic in the connectives (and in `◯`, which never occurs
in the ◯-free formulas the statement is about). -/
def relG (x : String → PLLFormula) : PLLFormula → PLLFormula
  | .prop a => x a
  | .falsePLL => t3
  | .and A B => .and (relG x A) (relG x B)
  | .or A B => .or (relG x A) (relG x B)
  | .ifThen A B => .ifThen (relG x A) (relG x B)
  | .somehow A => .somehow (relG x A)

/-- The relative negation in `[t3, ⊤]`: `x ↦ x ↠ t3`. -/
def Rneg (φ : PLLFormula) : PLLFormula := .ifThen φ t3

/-- **The statement**: `[t3, ⊤]` contains a copy of the free Heyting algebra on
the countably many generators `x a`, as the relativisation `h = relG x`:

    ∃ x, (∀ a, atomFree (x a)) ∧ (∀ a, [t3] ⊢ x a) ∧
      ∀ A B, boxFree A → boxFree B → ([A] ⊢ B ↔ [h A] ⊢ h B). -/
def FreeIPLInAboveT3 : Prop :=
  ∃ x : String → PLLFormula,
    (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [t3] (x a)) ∧
    ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
      (Deriv [A] B ↔ Deriv [relG x A] (relG x B))

/-! ## The candidate generators -/

/-- The brief's candidate: the odd gaps `g(2i+1) = ◯t(4i+3) ↠ t(4i+3)`. -/
def oddGap (i : Nat) : PLLFormula := gap (2 * i + 1)

/-- A two-generator assignment: `p ↦ x₀`, `q ↦ x₁`, every other variable `↦ t3`. -/
def gen2 (x₀ x₁ : PLLFormula) (a : String) : PLLFormula :=
  if a = "p" then x₀ else if a = "q" then x₁ else t3

/-- The odd gaps as a generator assignment on the two variables `p`, `q`:
`p ↦ g1`, `q ↦ g3`. -/
def oddGapGen2 : String → PLLFormula := gen2 (oddGap 0) (oddGap 1)

/-! ## The two-generator question, and the one-generator one -/

/-- `x` or its relative negation `x ↠ t3`, by a sign. -/
def sgn : Bool → PLLFormula → PLLFormula
  | true, x => x
  | false, x => Rneg x

/-- **The two-generator statement for a fixed pair**: no signed conjunction of
two variable-free `x₀`, `x₁` collapses to the relative bottom,

    ∀ ε : Bool × Bool,  ⊬ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3,        x^true = x, x^false = x ↠ t3.

In the free Heyting algebra on `p, q` with bottom `⊥`, none of `¬(p ∧ q)`,
`¬(p ∧ ¬q)`, `¬(¬p ∧ q)`, `¬(¬p ∧ ¬q)` is a theorem; so this is a necessary
condition for `h` to be faithful on the two generators `x₀`, `x₁`. -/
def TwoGenFaithful (x₀ x₁ : PLLFormula) : Prop :=
  ∀ ε : Bool × Bool, ¬ Deriv [] (Rneg ((sgn ε.1 x₀).and (sgn ε.2 x₁)))

/-- The one-variable relativisation `p ↦ ◯t3 = σ(◯⊥)`, `⊥ ↦ t3`:
`h₁ A = σ (A[p := ◯⊥])`. -/
def h1 (A : PLLFormula) : PLLFormula := sig (embed A)

/-- Every atom of the formula is the distinguished variable `p`. -/
def onlyP : PLLFormula → Bool
  | .prop a => decide (a = pv)
  | .falsePLL => true
  | .and A B => onlyP A && onlyP B
  | .or A B => onlyP A && onlyP B
  | .ifThen A B => onlyP A && onlyP B
  | .somehow A => onlyP A

/-- **The one-generator statement**: `[t3, ⊤]` contains the free Heyting
algebra on one generator (the Rieger–Nishimura lattice), as `h₁`:

    [t3] ⊢ h₁ p  ∧  ∀ A B ◯-free over p,  [A] ⊢ B  ⟺  [h₁ A] ⊢ h₁ B. -/
def FreeIPL1InAboveT3 : Prop :=
  Deriv [t3] (h1 (.prop pv)) ∧
  ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
    onlyP A = true → onlyP B = true → (Deriv [A] B ↔ Deriv [h1 A] (h1 B))

/-! ## Designed cells: the odd gaps are refuted (kernel-checked)

Certificates produced by the subframe tableau (`refbench fact`, untrusted) and
checked here by the kernel (`Certifier.verdict`, `decide +kernel`). -/

set_option maxRecDepth 100000

/-- **`h(¬¬q) = ⊤` for `q ↦ g3`**: `(g3 ↠ t3) ↠ t3` is a theorem of PLL, but
`¬¬q` is no theorem of IPC (`ipc_dneg`).  The odd gap `g3` is REFUTED as a
generator: its relative negation is the relative bottom, `g3 ↠ t3 ⊣⊢ t3`. -/
theorem cell_g3_dneg : Deriv [] (Rneg (Rneg (oddGap 1))) :=
  SubTab.yes.verdict (Rneg (Rneg (oddGap 1)))
    (.impR (((((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))).somehow).ifThen ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.impL ((((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))).somehow).ifThen ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))))) ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.orR (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.impR (((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))).somehow) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))) (.impL ((((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))).somehow).ifThen ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))))) ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.impLoc (((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))).somehow) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))) (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.orR ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.orR (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.impR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))) ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.impL ((((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))).somehow).ifThen ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))))) ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.orL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.orL (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.impLoc (((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))).somehow) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))) (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.ax (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)))))) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.impLoc (((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))).somehow) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))) (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.ax (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)))))) .bot)) (.impL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (PLLFormula.falsePLL.somehow) (.orR (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.impLoc (((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))).somehow) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))) (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.ax (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))))))) (.impLoc (((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))).somehow) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).or ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))) (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.ax (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)))))))) (.orL (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.orL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)))) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.orL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.impL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (PLLFormula.falsePLL.somehow) (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.ax (PLLFormula.falsePLL.somehow)))) .bot)))))))) (.orL (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.orR ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))))) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.orR (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))) ((((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).or (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))).ifThen ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.orR ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))))) .bot))))) (.orL (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.ax ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))) .bot))))

/-- The same cell for `g1`: `(g1 ↠ t3) ↠ t3` is NOT a theorem (countermodel,
3 worlds); `g1` survives the double-negation cell. -/
theorem cell_g1_dneg : ¬ Deriv [] (Rneg (Rneg (oddGap 0))) :=
  SubTab.no.verdict (Rneg (Rneg (oddGap 0)))
    { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]], S := [false, true, false], val := [[], [], []] }

/-- `h(p ∨ ¬p) ≠ ⊤` for `p ↦ g1`: `g1 ∨ (g1 ↠ t3)` is not a theorem
(countermodel, 6 worlds). -/
theorem cell_g1_lem : ¬ Deriv [] ((oddGap 0).or (Rneg (oddGap 0))) :=
  SubTab.no.verdict ((oddGap 0).or (Rneg (oddGap 0)))
    { n := 6, root := 0, le := [[true, true, true, true, true, true], [false, true, true, true, false, false], [false, false, true, false, false, false], [false, false, false, true, false, false], [false, false, false, false, true, true], [false, false, false, false, false, true]], S := [false, false, true, false, true, false], val := [[], [], [], [], [], []] }

/-- The missing pattern for the pair `(u, t4)`, `u = ◯¬◯⊥`, `t4 = t3 ↠ ◯⊥`:
`u ∧ t4 ≤ t3`, so `h(¬(p ∧ q)) = ⊤` for `p ↦ u`, `q ↦ t4`. -/
theorem cell_u_t4 : Deriv [] (Rneg (T6.uF.and t4)) :=
  SubTab.yes.verdict (Rneg (T6.uF.and t4))
    (.impR ((((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL).somehow).and (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow))) ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (.andL (((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL).somehow) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.impL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (PLLFormula.falsePLL.somehow) (.orR (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.boxR PLLFormula.falsePLL (.boxL ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.impL (PLLFormula.falsePLL.somehow) PLLFormula.falsePLL (.impL ((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)) (PLLFormula.falsePLL.somehow) (.andL (((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL).somehow) (((PLLFormula.falsePLL.somehow).or ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL)).ifThen (PLLFormula.falsePLL.somehow)) (.orR (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.boxLoc PLLFormula.falsePLL (.ax ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL))))) (.boxL PLLFormula.falsePLL .bot)) .bot)))) (.orR (PLLFormula.falsePLL.somehow) ((PLLFormula.falsePLL.somehow).ifThen PLLFormula.falsePLL) (.ax (PLLFormula.falsePLL.somehow))))))

/-! ## The IPC side: one-world Kripke models -/

/-- The one-world Kripke model with the valuation `v`. -/
def pt (v : String → Bool) : SubframeModel where
  W := Unit
  le _ _ := True
  S := fun _ => False
  V a := fun _ => v a = true
  refl _ := trivial
  trans _ _ := trivial
  hered _ h := h

/-- `φ` or `φ → ⊥`, by a sign (the IPC side of `sgn`). -/
def sgnP : Bool → PLLFormula → PLLFormula
  | true, φ => φ
  | false, φ => .ifThen φ .falsePLL

/-- `⊤ = ⊥ → ⊥`. -/
def topF : PLLFormula := .ifThen .falsePLL .falsePLL

/-- `¬(p^ε₁ ∧ q^ε₂)`, no theorem of IPC for any `ε`. -/
def negConj (ε : Bool × Bool) : PLLFormula :=
  .ifThen (.and (sgnP ε.1 (.prop "p")) (sgnP ε.2 (.prop "q"))) .falsePLL

theorem pt_sgnP (v : String → Bool) (a : String) (b : Bool) (h : v a = b) :
    (pt v).force () (sgnP b (.prop a)) := by
  cases b
  · intro u _ hu
    have hu' : v a = true := hu
    rw [h] at hu'
    exact Bool.noConfusion hu'
  · exact h

/-- The valuation `p ↦ b₀`, `q ↦ b₁`, everything else false. -/
def val2 (b₀ b₁ : Bool) (a : String) : Bool :=
  if a = "p" then b₀ else if a = "q" then b₁ else false

theorem val2_p (b₀ b₁ : Bool) : val2 b₀ b₁ "p" = b₀ := if_pos rfl

theorem val2_q (b₀ b₁ : Bool) : val2 b₀ b₁ "q" = b₁ := by
  show (if "q" = "p" then b₀ else if "q" = "q" then b₁ else false) = b₁
  rw [if_neg (by decide), if_pos rfl]

/-- **IPC**: `[⊤] ⊬ ¬(p^ε₁ ∧ q^ε₂)`, by the one-world model with valuation `ε`. -/
theorem ipc_negConj (ε : Bool × Bool) : ¬ Deriv [topF] (negConj ε) := fun ⟨d⟩ =>
  SubframeModel.CF.soundness d (pt (val2 ε.1 ε.2)) ()
    (fun χ hχ => by rw [List.mem_singleton.mp hχ]; exact fun _ _ h => h)
    () trivial ⟨pt_sgnP _ "p" ε.1 (val2_p _ _), pt_sgnP _ "q" ε.2 (val2_q _ _)⟩

/-- **IPC**: `⊬ ¬¬q`. -/
theorem ipc_dneg : ¬ Deriv [] (.ifThen (.ifThen (.prop "q") .falsePLL) .falsePLL) := fun ⟨d⟩ =>
  SubframeModel.CF.soundness d (pt fun _ => false) () (fun _ hχ => absurd hχ List.not_mem_nil)
    () trivial (fun _ _ hq => by
      have hq' : false = true := hq
      exact Bool.noConfusion hq')

/-- The odd gaps as generators: `[⊤] ⊬ ¬¬q` in IPC, but `[h ⊤] ⊢ h(¬¬q)` for
`q ↦ g3`.  REFUTED. -/
theorem oddGaps_refuted :
    ¬ Deriv [topF] (.ifThen (.ifThen (.prop "q") .falsePLL) .falsePLL) ∧
    Deriv [relG oddGapGen2 topF]
      (relG oddGapGen2 (.ifThen (.ifThen (.prop "q") .falsePLL) .falsePLL)) :=
  ⟨fun h => ipc_dneg (Deriv.cutHead (Deriv.impIntro (Deriv.iden (.head _))) h),
   (cell_g3_dneg.rename fun _ h => absurd h List.not_mem_nil)⟩

/-! ## The general refutation: every pair of generators fails

Semantics in a finite subframe model `M` (`SubTab.complete`, choice-free).
Write `G = {t3 holds}`, `R = {t3 fails}`.  `G = Gₑ ⊔ Gₙ` with `Gₑ = {◯⊥ holds}`
and `Gₙ = {¬◯⊥ holds}`, both upward closed, and every variable-free formula is
CONSTANT on each: on `Gₑ` it has the classical value with `◯A ↦ ⊤` (`Te`), on
`Gₙ` the classical value with `◯A ↦ A` (`Tn`).  A world `m` of `R` maximal in
`R` (`RMax`) therefore has a theory determined by two bits, whether some world
of `R` above it lies in `S` (`InS`) and whether some `Gₙ`-world lies above it
(`HasN`); the pair `(false, false)` is impossible (then `◯⊥` would hold at
`m`).  So there are THREE types of `R`-maximal world (`Tmax s n`), hence at most
three of the four sign patterns `(x₀ at m, x₁ at m)`.  For a missing pattern
`ε`, `(x₀^ε₁ ∧ x₁^ε₂) ↠ t3` holds at every world of every finite subframe
model, and is a theorem by completeness. -/

/-- Classical evaluation with `◯A ↦ ⊤`: the theory of the worlds forcing `◯⊥`. -/
def Te : PLLFormula → Bool
  | .prop _ => false
  | .falsePLL => false
  | .and A B => Te A && Te B
  | .or A B => Te A || Te B
  | .ifThen A B => !Te A || Te B
  | .somehow _ => true

/-- Classical evaluation with `◯A ↦ A`: the theory of the worlds forcing `¬◯⊥`. -/
def Tn : PLLFormula → Bool
  | .prop _ => false
  | .falsePLL => false
  | .and A B => Tn A && Tn B
  | .or A B => Tn A || Tn B
  | .ifThen A B => !Tn A || Tn B
  | .somehow A => Tn A

theorem imp_bool {a b : Bool} : (!a || b) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

section Model

open SubframeModel.CF

variable (M : SubframeModel)

/-- **On `Gₑ` every variable-free formula has the value `Te`.** -/
theorem force_e_iff_Te : ∀ (φ : PLLFormula) (w : M.W), atomFree φ = true → M.force w e →
    (M.force w φ ↔ Te φ = true)
  | .prop _, _, h, _ => nomatch h
  | .falsePLL, _, _, _ => ⟨False.elim, fun h => Bool.noConfusion h⟩
  | .and A B, w, h, hw => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (M.force w A ∧ M.force w B) ↔ (Te A && Te B) = true
      rw [Bool.and_eq_true]
      exact and_congr (force_e_iff_Te A w h'.1 hw) (force_e_iff_Te B w h'.2 hw)
  | .or A B, w, h, hw => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (M.force w A ∨ M.force w B) ↔ (Te A || Te B) = true
      rw [Bool.or_eq_true]
      exact or_congr (force_e_iff_Te A w h'.1 hw) (force_e_iff_Te B w h'.2 hw)
  | .ifThen A B, w, h, hw => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (∀ v, M.le w v → M.force v A → M.force v B) ↔ (!Te A || Te B) = true
      rw [imp_bool]
      constructor
      · intro hf hA
        exact (force_e_iff_Te B w h'.2 hw).mp (hf w (M.refl w) ((force_e_iff_Te A w h'.1 hw).mpr hA))
      · intro hT v hv hvA
        have hve := SubframeModel.force_mono M e hv hw
        exact (force_e_iff_Te B v h'.2 hve).mpr (hT ((force_e_iff_Te A v h'.1 hve).mp hvA))
  | .somehow A, w, _, hw => by
      show (∀ v, M.le w v → v ∈ M.S → M.force v A) ↔ true = true
      exact ⟨fun _ => rfl, fun _ v hv hvS => False.elim (hw v hv hvS)⟩

/-- **On `Gₙ` every variable-free formula has the value `Tn`.** -/
theorem force_ne_iff_Tn [FinDec M] : ∀ (φ : PLLFormula) (w : M.W), atomFree φ = true →
    M.force w ne → (M.force w φ ↔ Tn φ = true)
  | .prop _, _, h, _ => nomatch h
  | .falsePLL, _, _, _ => ⟨False.elim, fun h => Bool.noConfusion h⟩
  | .and A B, w, h, hw => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (M.force w A ∧ M.force w B) ↔ (Tn A && Tn B) = true
      rw [Bool.and_eq_true]
      exact and_congr (force_ne_iff_Tn A w h'.1 hw) (force_ne_iff_Tn B w h'.2 hw)
  | .or A B, w, h, hw => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (M.force w A ∨ M.force w B) ↔ (Tn A || Tn B) = true
      rw [Bool.or_eq_true]
      exact or_congr (force_ne_iff_Tn A w h'.1 hw) (force_ne_iff_Tn B w h'.2 hw)
  | .ifThen A B, w, h, hw => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (∀ v, M.le w v → M.force v A → M.force v B) ↔ (!Tn A || Tn B) = true
      rw [imp_bool]
      constructor
      · intro hf hA
        exact (force_ne_iff_Tn B w h'.2 hw).mp (hf w (M.refl w) ((force_ne_iff_Tn A w h'.1 hw).mpr hA))
      · intro hT v hv hvA
        have hvn := SubframeModel.force_mono M ne hv hw
        exact (force_ne_iff_Tn B v h'.2 hvn).mpr (hT ((force_ne_iff_Tn A v h'.1 hvn).mp hvA))
  | .somehow A, w, h, hw => by
      show (∀ v, M.le w v → v ∈ M.S → M.force v A) ↔ Tn A = true
      constructor
      · intro hf
        obtain ⟨s, hs, hsS, _⟩ := exists_of_not_force_box (M := M) (k := w) (ξ := .falsePLL)
          (fun h' => hw w (M.refl w) h')
        exact (force_ne_iff_Tn A s h (SubframeModel.force_mono M ne hs hw)).mp (hf s hs hsS)
      · intro hT v hv _
        exact (force_ne_iff_Tn A v h (SubframeModel.force_mono M ne hv hw)).mpr hT

/-- A world refuting `t3` with no proper successor refuting `t3`. -/
def RMax (w : M.W) : Prop := ¬ M.force w t3 ∧ ∀ v, M.le w v → ¬ M.force v t3 → M.le v w

/-- Some world above `w` refuting `t3` lies in `S`. -/
def InS (w : M.W) : Prop := ∃ v, M.le w v ∧ ¬ M.force v t3 ∧ v ∈ M.S

/-- Some world above `w` forces `¬◯⊥`. -/
def HasN (w : M.W) : Prop := ∃ v, M.le w v ∧ M.force v ne

instance [FinDec M] (w : M.W) : Decidable (InS M w) :=
  decidable_of_iff (∃ v ∈ FinDec.elems (M := M), M.le w v ∧ ¬ M.force v t3 ∧ v ∈ M.S)
    ⟨fun ⟨v, _, h⟩ => ⟨v, h⟩, fun ⟨v, h⟩ => ⟨v, FinDec.complete v, h⟩⟩

instance [FinDec M] (w : M.W) : Decidable (HasN M w) :=
  decidable_of_iff (∃ v ∈ FinDec.elems (M := M), M.le w v ∧ M.force v ne)
    ⟨fun ⟨v, _, h⟩ => ⟨v, h⟩, fun ⟨v, h⟩ => ⟨v, FinDec.complete v, h⟩⟩

/-- **The theory of an `R`-maximal world** of type `(s, n)`: `s` = some
`R`-world above it is in `S`, `n` = some `Gₙ`-world lies above it. -/
def Tmax (s n : Bool) : PLLFormula → Bool
  | .prop _ => false
  | .falsePLL => false
  | .and A B => Tmax s n A && Tmax s n B
  | .or A B => Tmax s n A || Tmax s n B
  | .ifThen A B => (!Tmax s n A || Tmax s n B) && (!Te A || Te B) && (!n || (!Tn A || Tn B))
  | .somehow A => (!s || Tmax s n A) && (!n || Tn A)

/-- Every world refuting `t3` has a `Gₑ`-world above it. -/
theorem exists_e_above [FinDec M] {w : M.W} (hw : ¬ M.force w t3) :
    ∃ v, M.le w v ∧ M.force v e := by
  have hn : ¬ M.force w (e ↠ .falsePLL) := fun h => hw (Or.inr h)
  obtain ⟨v, hv, hve, _⟩ := exists_of_not_force_imp hn
  exact ⟨v, hv, hve⟩

/-- **At an `R`-maximal world every variable-free formula has the value
`Tmax s n`**, `s`, `n` the two bits of its type. -/
theorem rmax_force [FinDec M] {w : M.W} (hw : RMax M w) {s n : Bool}
    (hs : s = true ↔ InS M w) (hn : n = true ↔ HasN M w) :
    ∀ φ : PLLFormula, atomFree φ = true → (M.force w φ ↔ Tmax s n φ = true)
  | .prop _, h => nomatch h
  | .falsePLL, _ => ⟨False.elim, fun h => Bool.noConfusion h⟩
  | .and A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (M.force w A ∧ M.force w B) ↔ (Tmax s n A && Tmax s n B) = true
      rw [Bool.and_eq_true]
      exact and_congr (rmax_force hw hs hn A h'.1) (rmax_force hw hs hn B h'.2)
  | .or A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      show (M.force w A ∨ M.force w B) ↔ (Tmax s n A || Tmax s n B) = true
      rw [Bool.or_eq_true]
      exact or_congr (rmax_force hw hs hn A h'.1) (rmax_force hw hs hn B h'.2)
  | .ifThen A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (atomFree A && atomFree B) = true)
      have ihA := rmax_force hw hs hn A h'.1
      have ihB := rmax_force hw hs hn B h'.2
      show (∀ v, M.le w v → M.force v A → M.force v B) ↔
        ((!Tmax s n A || Tmax s n B) && (!Te A || Te B) && (!n || (!Tn A || Tn B))) = true
      simp only [Bool.and_eq_true, imp_bool]
      constructor
      · intro hf
        refine ⟨⟨fun hTA => ihB.mp (hf w (M.refl w) (ihA.mpr hTA)), fun hTe => ?_⟩,
          fun hn' hTn => ?_⟩
        · obtain ⟨v, hv, hve⟩ := exists_e_above M hw.1
          exact (force_e_iff_Te M B v h'.2 hve).mp
            (hf v hv ((force_e_iff_Te M A v h'.1 hve).mpr hTe))
        · obtain ⟨v, hv, hvn⟩ := hn.mp hn'
          exact (force_ne_iff_Tn M B v h'.2 hvn).mp
            (hf v hv ((force_ne_iff_Tn M A v h'.1 hvn).mpr hTn))
      · rintro ⟨⟨h1, h2⟩, h3⟩ v hv hvA
        rcases Decidable.em (M.force v t3) with ht | ht
        · have ht' : M.force v e ∨ M.force v ne := ht
          rcases ht' with hve | hvn
          · exact (force_e_iff_Te M B v h'.2 hve).mpr (h2 ((force_e_iff_Te M A v h'.1 hve).mp hvA))
          · exact (force_ne_iff_Tn M B v h'.2 hvn).mpr
              (h3 (hn.mpr ⟨v, hv, hvn⟩) ((force_ne_iff_Tn M A v h'.1 hvn).mp hvA))
        · have hvw := hw.2 v hv ht
          exact SubframeModel.force_mono M B hv
            (ihB.mpr (h1 (ihA.mp (SubframeModel.force_mono M A hvw hvA))))
  | .somehow A, h => by
      have ihA := rmax_force hw hs hn A h
      show (∀ v, M.le w v → v ∈ M.S → M.force v A) ↔ ((!s || Tmax s n A) && (!n || Tn A)) = true
      simp only [Bool.and_eq_true, imp_bool]
      constructor
      · intro hf
        refine ⟨fun hs' => ?_, fun hn' => ?_⟩
        · obtain ⟨v, hv, hvt, hvS⟩ := hs.mp hs'
          exact ihA.mp (SubframeModel.force_mono M A (hw.2 v hv hvt) (hf v hv hvS))
        · obtain ⟨v, hv, hvn⟩ := hn.mp hn'
          obtain ⟨u, hu, huS, _⟩ := exists_of_not_force_box (M := M) (k := v) (ξ := .falsePLL)
            (fun h' => hvn v (M.refl v) h')
          exact (force_ne_iff_Tn M A u h (SubframeModel.force_mono M ne hu hvn)).mp
            (hf u (M.trans hv hu) huS)
      · rintro ⟨h1, h2⟩ v hv hvS
        rcases Decidable.em (M.force v t3) with ht | ht
        · have ht' : M.force v e ∨ M.force v ne := ht
          rcases ht' with hve | hvn
          · exact False.elim (hve v (M.refl v) hvS)
          · exact (force_ne_iff_Tn M A v h hvn).mpr (h2 (hn.mpr ⟨v, hv, hvn⟩))
        · exact SubframeModel.force_mono M A hv (ihA.mpr (h1 (hs.mpr ⟨v, hv, ht, hvS⟩)))

/-- **Three types**: an `R`-maximal world is of type `(true, _)` or `(_, true)`;
with neither bit it would force `◯⊥`. -/
theorem rmax_inS_or_hasN [FinDec M] {w : M.W} (hw : RMax M w) : InS M w ∨ HasN M w := by
  rcases Decidable.em (InS M w) with hs | hs
  · exact Or.inl hs
  rcases Decidable.em (HasN M w) with hn | hn
  · exact Or.inr hn
  exfalso
  apply hw.1
  refine Or.inl ?_
  intro v hv hvS
  rcases Decidable.em (M.force v t3) with ht | ht
  · have ht' : M.force v e ∨ M.force v ne := ht
    rcases ht' with hve | hvn
    · exact hve v (M.refl v) hvS
    · exact hn ⟨v, hv, hvn⟩
  · exact hs ⟨v, hv, ht, hvS⟩

/-- Above every world refuting `t3` there is an `R`-maximal one (descent on the
number of proper successors, `nProper` of `wip/f0Normal.lean`). -/
theorem exists_rmax_aux [FinDec M] :
    ∀ (n : Nat) (w : M.W), Normal.nProper M w ≤ n → ¬ M.force w t3 →
      ∃ m, M.le w m ∧ RMax M m := by
  intro n
  induction n with
  | zero =>
      intro w hn hw
      refine ⟨w, M.refl w, hw, fun v hv hvt => ?_⟩
      exact Decidable.byContradiction fun hvw =>
        absurd (Nat.lt_of_lt_of_le (Normal.nProper_lt M hv hvw) hn) (Nat.not_lt_zero _)
  | succ k ih =>
      intro w hn hw
      rcases Decidable.em (∃ v ∈ FinDec.elems (M := M), M.le w v ∧ ¬ M.force v t3 ∧ ¬ M.le v w)
        with hex | hno
      · obtain ⟨v, _, hv, hvt, hvw⟩ := hex
        obtain ⟨m, hvm, hm⟩ :=
          ih v (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Normal.nProper_lt M hv hvw) hn)) hvt
        exact ⟨m, M.trans hv hvm, hm⟩
      · exact ⟨w, M.refl w, hw, fun v hv hvt => Decidable.byContradiction fun hvw =>
          hno ⟨v, FinDec.complete v, hv, hvt, hvw⟩⟩

theorem exists_rmax [FinDec M] {w : M.W} (hw : ¬ M.force w t3) : ∃ m, M.le w m ∧ RMax M m :=
  exists_rmax_aux M _ w (Nat.le_refl _) hw

/-- The sign pattern of a pair at an `R`-maximal world of type `(s, n)`. -/
def pattern (s n : Bool) (x₀ x₁ : PLLFormula) : Bool × Bool := (Tmax s n x₀, Tmax s n x₁)

/-- **The pattern of a signed conjunction forced at an `R`-maximal world is
its sign.** -/
theorem pattern_of_force [FinDec M] {w : M.W} (hw : RMax M w) {x₀ x₁ : PLLFormula}
    (h₀ : atomFree x₀ = true) (h₁ : atomFree x₁ = true) (ε₀ ε₁ : Bool)
    (hf : M.force w ((sgn ε₀ x₀).and (sgn ε₁ x₁))) :
    pattern (decide (InS M w)) (decide (HasN M w)) x₀ x₁ = (ε₀, ε₁) := by
  have key := rmax_force M hw (s := decide (InS M w)) (n := decide (HasN M w))
    decide_eq_true_iff decide_eq_true_iff
  have e₀ : Tmax (decide (InS M w)) (decide (HasN M w)) x₀ = ε₀ := by
    cases ε₀
    · cases hT : Tmax (decide (InS M w)) (decide (HasN M w)) x₀
      · rfl
      · exact absurd (hf.1 w (M.refl w) ((key x₀ h₀).mpr hT)) hw.1
    · exact (key x₀ h₀).mp hf.1
  have e₁ : Tmax (decide (InS M w)) (decide (HasN M w)) x₁ = ε₁ := by
    cases ε₁
    · cases hT : Tmax (decide (InS M w)) (decide (HasN M w)) x₁
      · rfl
      · exact absurd (hf.2 w (M.refl w) ((key x₁ h₁).mpr hT)) hw.1
    · exact (key x₁ h₁).mp hf.2
  show (Tmax _ _ x₀, Tmax _ _ x₁) = (ε₀, ε₁)
  rw [e₀, e₁]

/-- The pattern at an `R`-maximal world is one of the three type patterns. -/
theorem pattern_mem [FinDec M] {w : M.W} (hw : RMax M w) (x₀ x₁ : PLLFormula) :
    pattern (decide (InS M w)) (decide (HasN M w)) x₀ x₁ ∈
      [pattern true true x₀ x₁, pattern true false x₀ x₁, pattern false true x₀ x₁] := by
  rcases rmax_inS_or_hasN M hw with hs | hn
  · rw [decide_eq_true hs]
    cases decide (HasN M w)
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_self ..
  · rw [decide_eq_true hn]
    cases decide (InS M w)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact List.mem_cons_self ..

end Model

/-- A pair of Booleans absent from a list of three. -/
def missing (l : List (Bool × Bool)) : Bool × Bool :=
  if (true, true) ∈ l then
    (if (true, false) ∈ l then (if (false, true) ∈ l then (false, false) else (false, true))
     else (true, false))
  else (true, true)

theorem missing_not_mem (a b c : Bool × Bool) : missing [a, b, c] ∉ [a, b, c] := by
  rcases a with ⟨_ | _, _ | _⟩ <;> rcases b with ⟨_ | _, _ | _⟩ <;>
    rcases c with ⟨_ | _, _ | _⟩ <;> decide

/-- **No two variable-free formulas are free generators over `t3`**: for every
`x₀`, `x₁` some signed conjunction lies below `t3`,

    ∃ ε,  ⊢ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3. -/
theorem noFreeHA2 (x₀ x₁ : PLLFormula) (h₀ : atomFree x₀ = true) (h₁ : atomFree x₁ = true) :
    ∃ ε : Bool × Bool, Deriv [] (Rneg ((sgn ε.1 x₀).and (sgn ε.2 x₁))) := by
  refine ⟨missing [pattern true true x₀ x₁, pattern true false x₀ x₁, pattern false true x₀ x₁], ?_⟩
  have hεmem := missing_not_mem (pattern true true x₀ x₁) (pattern true false x₀ x₁)
    (pattern false true x₀ x₁)
  generalize missing [pattern true true x₀ x₁, pattern true false x₀ x₁, pattern false true x₀ x₁]
    = ε at hεmem ⊢
  obtain ⟨ε₀, ε₁⟩ := ε
  rcases SubTab.complete (Rneg ((sgn ε₀ x₀).and (sgn ε₁ x₁))) with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact SubTab.holds_of_check hc
  · exfalso
    have hm0 : m.refutes (Rneg ((sgn ε₀ x₀).and (sgn ε₁ x₁))) = true := hm
    simp only [SubTab.SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm0
    have hr := (SubTab.SubCM.ok_parts hm0.1).1
    have hnf : ¬ (m.toModel hm0.1).force ⟨m.root, hr⟩ (Rneg ((sgn ε₀ x₀).and (sgn ε₁ x₁))) :=
      fun hf => by
        have hb := (SubTab.SubCM.forceB_iff hm0.1 _ ⟨m.root, hr⟩).mpr hf
        rw [hm0.2] at hb
        exact Bool.false_ne_true hb
    obtain ⟨v, _, hvψ, hvt⟩ := SubframeModel.CF.exists_of_not_force_imp hnf
    obtain ⟨w, hvw, hw⟩ := exists_rmax (m.toModel hm0.1) hvt
    have hwψ := SubframeModel.force_mono (m.toModel hm0.1) _ hvw hvψ
    have hp := pattern_of_force (m.toModel hm0.1) hw h₀ h₁ ε₀ ε₁ hwψ
    have hmem := pattern_mem (m.toModel hm0.1) hw x₀ x₁
    rw [hp] at hmem
    exact hεmem hmem

/-- The two-generator condition fails for every pair. -/
theorem not_twoGenFaithful (x₀ x₁ : PLLFormula) (h₀ : atomFree x₀ = true)
    (h₁ : atomFree x₁ = true) : ¬ TwoGenFaithful x₀ x₁ := fun h =>
  let ⟨ε, hd⟩ := noFreeHA2 x₀ x₁ h₀ h₁
  h ε hd

/-- **The type patterns of the odd gaps `(g1, g3)`**, over the three types
`(S, N)`, `(S, ¬N)`, `(¬S, N)`: `g3` holds at every `R`-maximal world and `g1`
fails exactly at the type `(¬S, N)`; the pattern `(_, false)` is missing, which
is the cell `cell_g3_dneg`. -/
theorem oddGap_patterns :
    pattern true true (oddGap 0) (oddGap 1) = (true, true) ∧
    pattern true false (oddGap 0) (oddGap 1) = (true, true) ∧
    pattern false true (oddGap 0) (oddGap 1) = (false, true) := by
  decide

/-- **The type patterns of `(u, t4)`**: `u = ◯¬◯⊥` holds exactly at the type
`(¬S, N)`, `t4 = t3 ↠ ◯⊥` exactly at `(S, ¬N)`; the pattern `(true, true)` is
missing, which is the cell `cell_u_t4`. -/
theorem u_t4_patterns :
    pattern true true T6.uF t4 = (false, false) ∧
    pattern true false T6.uF t4 = (false, true) ∧
    pattern false true T6.uF t4 = (true, false) := by
  decide

theorem relG_sgnP (x : String → PLLFormula) (b : Bool) (φ : PLLFormula) :
    relG x (sgnP b φ) = sgn b (relG x φ) := by
  cases b <;> rfl

theorem relG_negConj (x : String → PLLFormula) (ε : Bool × Bool) :
    relG x (negConj ε) = Rneg ((sgn ε.1 (x "p")).and (sgn ε.2 (x "q"))) := by
  show PLLFormula.ifThen (.and (relG x (sgnP ε.1 (.prop "p"))) (relG x (sgnP ε.2 (.prop "q")))) t3 = _
  rw [relG_sgnP, relG_sgnP]
  rfl

theorem boxFree_sgnP (b : Bool) {φ : PLLFormula} (h : boxFree φ = true) :
    boxFree (sgnP b φ) = true := by
  cases b
  · show (boxFree φ && true) = true
    rw [h]
    rfl
  · exact h

theorem boxFree_negConj (ε : Bool × Bool) : boxFree (negConj ε) = true := by
  show ((boxFree (sgnP ε.1 (.prop "p")) && boxFree (sgnP ε.2 (.prop "q"))) && true) = true
  rw [boxFree_sgnP ε.1 rfl, boxFree_sgnP ε.2 rfl]
  rfl

/-- **Every generator assignment fails**: some ◯-free `[A] ⊬ B` has
`[h A] ⊢ h B`; here `A = ⊤` and `B = ¬(p^ε₁ ∧ q^ε₂)` for the missing sign
pattern `ε` of the pair `(x p, x q)`. -/
theorem not_faithful (x : String → PLLFormula) (hx : ∀ a, atomFree (x a) = true) :
    ∃ A B : PLLFormula, boxFree A = true ∧ boxFree B = true ∧
      ¬ Deriv [A] B ∧ Deriv [relG x A] (relG x B) := by
  obtain ⟨ε, hd⟩ := noFreeHA2 (x "p") (x "q") (hx "p") (hx "q")
  refine ⟨topF, negConj ε, rfl, boxFree_negConj ε, ipc_negConj ε, ?_⟩
  rw [relG_negConj]
  exact hd.rename fun _ h => absurd h List.not_mem_nil

/-- **REFUTED**: `[t3, ⊤]` does not contain the free Heyting algebra on
countably many generators; not even on two. -/
theorem not_FreeIPLInAboveT3 : ¬ FreeIPLInAboveT3 := by
  rintro ⟨x, hx, -, hfree⟩
  obtain ⟨A, B, hA, hB, hnd, hd⟩ := not_faithful x hx
  exact hnd ((hfree A B hA hB).mpr hd)

/-! ## One generator: PROVED

`h₁ A = σ(A[p := ◯⊥])`.  Preservation is substitution (`deriv_substP`) followed
by `σ` (`sig_mono`); reflection is `sig_reflects_ctx` followed by the
faithfulness of `p ↦ ◯⊥` on one-variable IPC formulas (`not_deriv_of_sep`,
`wip/rnEmbed.lean`, from a subframe countermodel of `A ↠ B` read as a
one-variable Kripke skeleton). -/

theorem onlyP_embed_vf : ∀ A : PLLFormula, onlyP A = true → atomFree (embed A) = true
  | .prop a, h => by
      have ha : a = pv := of_decide_eq_true h
      subst ha
      show atomFree (if pv = pv then oBot else .prop pv) = true
      rw [if_pos rfl]
      rfl
  | .falsePLL, _ => rfl
  | .and A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (onlyP A && onlyP B) = true)
      show (atomFree (embed A) && atomFree (embed B)) = true
      rw [onlyP_embed_vf A h'.1, onlyP_embed_vf B h'.2]
      rfl
  | .or A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (onlyP A && onlyP B) = true)
      show (atomFree (embed A) && atomFree (embed B)) = true
      rw [onlyP_embed_vf A h'.1, onlyP_embed_vf B h'.2]
      rfl
  | .ifThen A B, h => by
      have h' := Bool.and_eq_true_iff.mp (h : (onlyP A && onlyP B) = true)
      show (atomFree (embed A) && atomFree (embed B)) = true
      rw [onlyP_embed_vf A h'.1, onlyP_embed_vf B h'.2]
      rfl
  | .somehow A, h => onlyP_embed_vf A h

/-- A subframe model read as a one-variable Kripke skeleton, `U = V p`. -/
def toSkel (M : SubframeModel) : Skel where
  W := M.W
  le := M.le
  refl := M.refl
  trans := M.trans
  U := M.V pv
  upU := fun h hu => M.hered h hu

theorem toSkel_sat (M : SubframeModel) : ∀ A : PLLFormula, boxFree A = true → onlyP A = true →
    ∀ w : M.W, ((toSkel M).sat A w ↔ M.force w A)
  | .prop a, _, h, w => by
      have ha : a = pv := of_decide_eq_true h
      subst ha
      show (pv = pv ∧ w ∈ M.V pv) ↔ w ∈ M.V pv
      exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  | .falsePLL, _, _, _ => Iff.rfl
  | .and A B, hb, hp, w => by
      have hb' := Bool.and_eq_true_iff.mp (hb : (boxFree A && boxFree B) = true)
      have hp' := Bool.and_eq_true_iff.mp (hp : (onlyP A && onlyP B) = true)
      exact and_congr (toSkel_sat M A hb'.1 hp'.1 w) (toSkel_sat M B hb'.2 hp'.2 w)
  | .or A B, hb, hp, w => by
      have hb' := Bool.and_eq_true_iff.mp (hb : (boxFree A && boxFree B) = true)
      have hp' := Bool.and_eq_true_iff.mp (hp : (onlyP A && onlyP B) = true)
      exact or_congr (toSkel_sat M A hb'.1 hp'.1 w) (toSkel_sat M B hb'.2 hp'.2 w)
  | .ifThen A B, hb, hp, w => by
      have hb' := Bool.and_eq_true_iff.mp (hb : (boxFree A && boxFree B) = true)
      have hp' := Bool.and_eq_true_iff.mp (hp : (onlyP A && onlyP B) = true)
      show (∀ v, M.le w v → (toSkel M).sat A v → (toSkel M).sat B v) ↔
        (∀ v, M.le w v → M.force v A → M.force v B)
      exact forall_congr' fun v => imp_congr Iff.rfl
        (imp_congr (toSkel_sat M A hb'.1 hp'.1 v) (toSkel_sat M B hb'.2 hp'.2 v))
  | .somehow _, hb, _, _ => nomatch hb

/-- **`h₁` reflects derivability** on one-variable ◯-free formulas. -/
theorem h1_reflects {A B : PLLFormula} (hA : boxFree A = true) (hB : boxFree B = true)
    (pA : onlyP A = true) (pB : onlyP B = true) (hd : Deriv [h1 A] (h1 B)) : Deriv [A] B := by
  have hd' : Deriv [embed A] (embed B) := sig_reflects_ctx hd
  rcases SubTab.complete (A.ifThen B) with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact Deriv.impElim (Deriv.rename (fun _ hx => absurd hx List.not_mem_nil)
      (SubTab.holds_of_check hc)) (Deriv.iden (.head _))
  · exfalso
    have hm0 : m.refutes (A.ifThen B) = true := hm
    simp only [SubTab.SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm0
    have hr := (SubTab.SubCM.ok_parts hm0.1).1
    have hnf : ¬ (m.toModel hm0.1).force ⟨m.root, hr⟩ (A.ifThen B) := fun hf => by
      have hb := (SubTab.SubCM.forceB_iff hm0.1 _ ⟨m.root, hr⟩).mpr hf
      rw [hm0.2] at hb
      exact Bool.false_ne_true hb
    obtain ⟨v, _, hvA, hvB⟩ := SubframeModel.CF.exists_of_not_force_imp hnf
    exact not_deriv_of_sep (toSkel (m.toModel hm0.1)) hA hB
      ((toSkel_sat _ A hA pA v).mpr hvA) (fun h => hvB ((toSkel_sat _ B hB pB v).mp h)) hd'

theorem h1_prop : h1 (.prop pv) = .somehow t3 := rfl

theorem t3_le_h1_prop : Deriv [t3] (h1 (.prop pv)) := by
  rw [h1_prop]
  exact (Deriv.iden (.head _) : Deriv [t3] t3).elim fun d => ⟨.laxIntro d⟩

/-- **PROVED**: `[t3, ⊤]` contains the free Heyting algebra on one generator,
`h₁ p = ◯t3 = σ(◯⊥)`. -/
theorem freeIPL1 : FreeIPL1InAboveT3 :=
  ⟨t3_le_h1_prop, fun A B hA hB pA pB =>
    ⟨fun hd => sig_mono (onlyP_embed_vf A pA) (onlyP_embed_vf B pB) (deriv_substP hd),
     h1_reflects hA hB pA pB⟩⟩

end FreeIPL
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.FreeIPL.cell_g3_dneg [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.cell_g1_dneg [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.cell_g1_lem [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.cell_u_t4 [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.ipc_negConj [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.ipc_dneg [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.oddGaps_refuted [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.force_e_iff_Te [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.force_ne_iff_Tn [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.rmax_force [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.rmax_inS_or_hasN [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.exists_rmax [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.noFreeHA2 [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.not_twoGenFaithful [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.oddGap_patterns [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.u_t4_patterns [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.not_faithful [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.not_FreeIPLInAboveT3 [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.h1_reflects [propext, Quot.sound]
#axioms_within PLLND.F0.FreeIPL.freeIPL1 [propext, Quot.sound]
