import wip.f0FreePair
import Meta.Audit

/-!
# One generator family over `σ³⊥` for every finite number of generators

Follow-up to `wip/f0FreePair.lean` (2026-10-28).  There `x₀ = ◯σ²⊥` and
`x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3)` freely generate a copy of the free Heyting
algebra `H₂` inside `[σ²⊥, ⊤]` (`freePair`).  Here the same scheme is shifted
one level: base `σ³⊥ = base 3`, threshold `σ²⊥`, and ONE family of generators
`x3 (pvar i)` serves every `n`.

## The statement (committed before any proof, METHOD.md §1)

    σ³⊥ = ◯σ²⊥ ∨ (◯σ²⊥ ↠ σ²⊥)                                   (`base_three`)
    φ_k = relX (rn (2k+1))                (`phiK`; ZL.cell_force: bottom of ZL n ⊩ φ_k ⟺ n+2 ≤ k)
    c_r = φ_{r+1} ∨ (φ_{r+2} ↠ σ²⊥)                              (`sepC`)
    x₀  = ◯σ³⊥,     x_r = σ³⊥ ∨ ((c_r ↠ σ²⊥) ↠ σ²⊥)   (r ≥ 1)    (`gen`)
    x3 a = gen (utf8ByteSize a - 1),  so  x3 (pvar i) = gen i         (`x3`)

    Free3 :  ∀ n A B ◯-free with varsBelow n,
               [A] ⊢ B  ⟺  [relB σ³⊥ x3 A] ⊢ relB σ³⊥ x3 B

    FreeFamily3 :  ∃ x, (∀ a, x a variable-free) ∧ (∀ a, [σ³⊥] ⊢ x a) ∧
                      ∀ n A B ◯-free with varsBelow n,  [A] ⊢ B ⟺ [relB σ³⊥ x A] ⊢ relB σ³⊥ x B

Corollaries: `Free3 → FreeFamily3` (`freeFamily3_of_free3`),
`FreeFamily3 → ∀ n, FreeHAnAbove (σ³⊥) n` (`freeHAnAbove_of_family`),
`(∀ n, FreeHAnAbove (σ³⊥) n) → Conjecture` (`conjecture_of_base3`).

The direction `⟹` is substitution (`relB_preserves` of `f0FreePair`); the
content is `⟸`.

Fragment first (CLAUDE.md rule 8): as in `f0FreePair`, the ◯-free
variable-free fragment is `{⊥, ⊤}`, so the IPC instance of the question is the
definition of the free Heyting algebra: degenerate, recorded as such.

## The side cell (Matthew's lattice-first idea)

With `g1 = oddGap 0`, `g3 = oddGap 1` (`wip/f0FreeIPL.lean`):

    ⊢? (g1 ↠ g3) ∨ (g3 ↠ g1)                                      (`sideCell`)

If it is provable, the pair cannot generate a free Heyting algebra over any base.

## Results

**PROVED: `Free3`** (`free3`), hence `FreeFamily3` (`freeFamily3`),
`∀ n, FreeHAnAbove (σ³⊥) n` (`freeHAnAbove_base3`) and **`Conjecture`**
(`conjecture`, with `m = 3` for every `n`): the one family `x3 (pvar i)`
freely generates, for every `n`, a copy of the free Heyting algebra on `n`
generators inside `[σ³⊥, ⊤]`, closed under F0's `∧`, `∨`, `↠`, with bottom
`σ³⊥`.  Pins `[propext, Quot.sound]`; no `Classical.choice`, no `sorry`, no
`native_decide`.

* Stage 1: the designed cells `(p₁ → p₂) ∨ (p₂ → p₁)`, `¬¬p₂ → p₂`,
  `(p₀ → p₂) ∨ (p₂ → p₀)` all pass (`cell_Ca`, `cell_Cb`, `cell_Cc`, gadget
  tables, kernel-checked), with the base facts and the generator readings.
* The gadget `M(K, D)` (`Gad.MK`) over a finite Kripke model `K`: a copy of
  every cell `ZL r` (embedded as a generated submodel, `Gad.zforce`, by the
  p-morphism lemma `force_pmorph`), the non-`S` killer `kn` (the bottom of
  `ZL 0` taken out of `S`), and copies `w_k` of `K`, with `w_k ∈ S ⟺ D 0 k`
  and `w_k` below `ZL (r+1)` iff `D (r+1) k`.  The `S`-killer is the bottom
  of `ZL 0`, the reader of `x_r` the bottom of `ZL r`.  For `D r k ⟺ k ⊮ pvar r`
  the generators read the valuation (`Gad.w_read`), lemma (a) of
  `f0FreePair` (`relB_transfer`) gives `w_k ⊩ relB σ³⊥ x3 A ⟺ k ⊩ A`
  (`Gad.transfer`), and `⟸` follows (`free3_reflects`).
* Side cell: `⊬ (g1 ↠ g3) ∨ (g3 ↠ g1)` (`side_cell`).

Status note: `wip/f0FreeBase3-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace Base3

open SemUI RNEmbed Sig FreeIPL FreeHAn Pair
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ## The statement -/

/-- The base `σ³⊥`. -/
abbrev b3 : PLLFormula := base 3

/-- `σ³⊥ = ◯σ²⊥ ∨ (◯σ²⊥ ↠ σ²⊥)`. -/
theorem base_three : base 3 = (PLLFormula.somehow (base 2)).or ((PLLFormula.somehow (base 2)).ifThen (base 2)) :=
  rfl

/-- The relativised odd rung `φ_k = relX (rn (2k+1))` (`p ↦ ◯Y`, `⊥ ↦ t3`). -/
def phiK (k : Nat) : PLLFormula := ZL.relX (rn (2 * k + 1))

/-- The separator `c_r = φ_{r+1} ∨ (φ_{r+2} ↠ σ²⊥)`, designed to fail at the
bottom of `ZL r` and to hold at the bottom of every other `ZL n`. -/
def sepC (r : Nat) : PLLFormula := (phiK (r + 1)).or ((phiK (r + 2)).ifThen b2)

/-- **The generators**: `x₀ = ◯σ³⊥`, `x_r = σ³⊥ ∨ ((c_r ↠ σ²⊥) ↠ σ²⊥)`. -/
def gen : Nat → PLLFormula
  | 0 => .somehow b3
  | r + 1 => b3.or (((sepC (r + 1)).ifThen b2).ifThen b2)

/-- The index of a variable: its UTF-8 size less one (`pvar i ↦ i`). -/
def idx (a : String) : Nat := a.utf8ByteSize - 1

/-- **The generator assignment** `x3 a = gen (idx a)`. -/
def x3 (a : String) : PLLFormula := gen (idx a)

/-- **Free3**: the relativisation `A ↦ A[pvar i := x3 (pvar i), ⊥ := σ³⊥]` is
faithful on the ◯-free formulas in `pvar 0, …, pvar (n-1)`, for every `n`. -/
def Free3 : Prop :=
  ∀ (n : Nat) (A B : PLLFormula), boxFree A = true → boxFree B = true →
    varsBelow n A = true → varsBelow n B = true →
    (Deriv [A] B ↔ Deriv [relB b3 x3 A] (relB b3 x3 B))

/-- **FreeFamily3**: one family of variable-free generators above `σ³⊥`
freely generates the free Heyting algebra on every finite number of
generators. -/
def FreeFamily3 : Prop :=
  ∃ x : String → PLLFormula, (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [base 3] (x a)) ∧
    ∀ (n : Nat) (A B : PLLFormula), boxFree A = true → boxFree B = true →
      varsBelow n A = true → varsBelow n B = true →
      (Deriv [A] B ↔ Deriv [relB (base 3) x A] (relB (base 3) x B))

/-! ## The generators are variable-free and lie above `σ³⊥` -/

theorem b2_vf : atomFree b2 = true := rfl

theorem b3_vf : atomFree b3 = true := rfl

theorem phiK_vf (k : Nat) : atomFree (phiK k) = true := ZL.relX_vf _

theorem sepC_vf (r : Nat) : atomFree (sepC r) = true := by
  show (atomFree (phiK (r + 1)) && (atomFree (phiK (r + 2)) && atomFree b2)) = true
  rw [phiK_vf, phiK_vf]
  rfl

theorem gen_vf : ∀ r, atomFree (gen r) = true
  | 0 => rfl
  | r + 1 => by
      show (atomFree b3 && ((atomFree (sepC (r + 1)) && atomFree b2) && atomFree b2)) = true
      rw [sepC_vf]
      rfl

theorem x3_vf (a : String) : atomFree (x3 a) = true := gen_vf _

theorem b3_le_gen : ∀ r, Deriv [b3] (gen r)
  | 0 => (Deriv.iden (.head _) : Deriv [b3] b3).elim fun d => ⟨.laxIntro d⟩
  | _ + 1 => Deriv.orIntro1 (Deriv.iden (.head _))

theorem b3_le_x3 (a : String) : Deriv [b3] (x3 a) := b3_le_gen _

/-! ## The corollaries -/

/-- `Free3` gives `FreeFamily3`, with the witness `x3`. -/
theorem freeFamily3_of_free3 (h : Free3) : FreeFamily3 :=
  ⟨x3, x3_vf, b3_le_x3, h⟩

/-- `FreeFamily3` gives a copy of `Hₙ` in `[σ³⊥, ⊤]` for every `n`. -/
theorem freeHAnAbove_of_family (h : FreeFamily3) (n : Nat) : FreeHAnAbove (base 3) n :=
  let ⟨x, hvf, hle, hf⟩ := h
  ⟨x, hvf, hle, hf n⟩

/-- Every `FreeHAnAbove (σ³⊥) n` gives the conjecture, with `m = 3`. -/
theorem conjecture_of_base3 (h : ∀ n, FreeHAnAbove (base 3) n) : Conjecture :=
  fun n => ⟨3, h n⟩

/-! ## The side cell -/

/-- `(g1 ↠ g3) ∨ (g3 ↠ g1)`, `g1 = oddGap 0`, `g3 = oddGap 1`. -/
def sideCell : PLLFormula :=
  ((oddGap 0).ifThen (oddGap 1)).or ((oddGap 1).ifThen (oddGap 0))

set_option maxRecDepth 100000

/-- **The side cell is no theorem**: `⊬ (g1 ↠ g3) ∨ (g3 ↠ g1)` (subframe
tableau, `refbench fact`: countermodel of 27 worlds, minimised to 8; checked
here by the kernel against `sideCell` as computed in Lean).  So this cell does
not rule out the odd-gap pair as generators of a free Heyting algebra. -/
theorem side_cell : ¬ Deriv [] sideCell :=
  SubTab.no.verdict sideCell
    { n := 8, root := 0, le := [[true, true, true, true, true, true, true, true], [false, true, true, true, true, false, false, false], [false, false, true, false, false, false, false, false], [false, false, false, true, true, false, false, false], [false, false, false, false, true, false, false, false], [false, false, false, false, false, true, true, true], [false, false, false, false, false, false, true, false], [false, false, false, false, false, false, false, true]], S := [false, false, true, true, false, false, false, true], val := [[], [], [], [], [], [], [], []] }

/-! ## Stage 1: the designed cells (refutation stage, CLAUDE.md rules 7 and 9)

Three variables `p₀ = pvar 0`, `p₁ = pvar 1`, `p₂ = pvar 2` and the cells

    Ca = (p₁ → p₂) ∨ (p₂ → p₁),   Cb = ¬¬p₂ → p₂,   Cc = (p₀ → p₂) ∨ (p₂ → p₀),

none a theorem of IPC (`ipc_Ca`, `ipc_Cb`, `ipc_Cc`: a fork, a two-chain, a
fork).  Freeness needs each image `relB σ³⊥ x3 C` to be no theorem of PLL.

The gadget over a finite Kripke model `K` (pen design, `wip/f0FreeBase3-STATUS.md`),
here with the upper structure shared between the cells, as a `SubCM` table:

    0 e₀ (∉ S)   1 n₀ (∈ S)                       the tops (◯⊥, ¬◯⊥)
    2 L₀  3 L₁  4 L₂ (∈ S)                        the ladder of `ZL` (L_j sees L_{j'} for j'+2 ≤ j,
                                                  e₀ always, n₀ from L₁ up)
    5 f (∉ S, sees e₀, n₀)
    6 m₀ (∈ S)  7 m₁ (∈ S)  8 m₂ (∈ S)            the bottoms of ZL 0, ZL 1, ZL 2: m_r sees
                                                  e₀, n₀, f, L₀ … L_r
    9 kn (∉ S, sees e₀, n₀, L₀, f)                the bottom of ZL 0 taken out of S
    10 … w_k (∈ S iff k ⊮ p₀)                     copies of K; w_k sees 0, 1, 2, 5, 6, 9 always,
                                                  m_r and its cone iff k ⊮ p_r (r = 1, 2)

`m₀` and `kn` are the two killers (σ²⊥-maximal, in and out of `S`), `m₁`, `m₂`
the readers of `p₁`, `p₂`; `c_r` fails at `m_r` and holds at the other three.
`baseFacts` checks: `0 … 5` force `σ²⊥`; `6 … 9` refute it and are
`σ²⊥`-maximal; every world but the copies forces `σ³⊥`, the copies refute it;
the separations `c₁`, `c₂`; `c_r ↠ σ²⊥` at `m_r`; `m₀ ∈ S`, `kn ∉ S`,
`kn ⊩ ◯σ²⊥` and `kn ⊩ ◯Y`.  `read_*` checks that `gen i` holds at `w_k` iff
`p_i` holds at `k`.  All kernel-evaluated (`decide +kernel`). -/

/-- `p₀ = pvar 0`. -/
def p0F : PLLFormula := .prop (pvar 0)

/-- `p₁ = pvar 1`. -/
def p1F : PLLFormula := .prop (pvar 1)

/-- `p₂ = pvar 2`. -/
def p2F : PLLFormula := .prop (pvar 2)

/-- Ca = `(p₁ → p₂) ∨ (p₂ → p₁)`. -/
def Ca : PLLFormula := (p1F.ifThen p2F).or (p2F.ifThen p1F)

/-- Cb = `¬¬p₂ → p₂`. -/
def Cb : PLLFormula := (negF (negF p2F)).ifThen p2F

/-- Cc = `(p₀ → p₂) ∨ (p₂ → p₀)`. -/
def Cc : PLLFormula := (p0F.ifThen p2F).or (p2F.ifThen p0F)

/-- IPC: `⊬ (p₁ → p₂) ∨ (p₂ → p₁)` (a fork, `p₁` at one top, `p₂` at the other). -/
theorem ipc_Ca : ¬ Deriv [] Ca :=
  SubTab.no.verdict Ca
    { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
      S := [false, false, false], val := [[], ["pp"], ["ppp"]] }

/-- IPC: `⊬ ¬¬p₂ → p₂` (a two-chain, `p₂` at the top). -/
theorem ipc_Cb : ¬ Deriv [] Cb :=
  SubTab.no.verdict Cb
    { n := 2, root := 0, le := [[true, true], [false, true]], S := [false, false],
      val := [[], ["ppp"]] }

/-- IPC: `⊬ (p₀ → p₂) ∨ (p₂ → p₀)` (a fork, `p₀` at one top, `p₂` at the other). -/
theorem ipc_Cc : ¬ Deriv [] Cc :=
  SubTab.no.verdict Cc
    { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
      S := [false, false, false], val := [[], ["p"], ["ppp"]] }

/-- The gadget over the fork `k₀ < k₁, k₂`, `p₁` at `k₁`, `p₂` at `k₂`. -/
def TCa : SubTab.SubCM := { n := 13, root := 10, le := [[true, false, false, false, false, false, false, false, false, false, false, false, false], [false, true, false, false, false, false, false, false, false, false, false, false, false], [true, false, true, false, false, false, false, false, false, false, false, false, false], [true, true, false, true, false, false, false, false, false, false, false, false, false], [true, true, true, false, true, false, false, false, false, false, false, false, false], [true, true, false, false, false, true, false, false, false, false, false, false, false], [true, true, true, false, false, true, true, false, false, false, false, false, false], [true, true, true, true, false, true, false, true, false, false, false, false, false], [true, true, true, true, true, true, false, false, true, false, false, false, false], [true, true, true, false, false, true, false, false, false, true, false, false, false], [true, true, true, true, true, true, true, true, true, true, true, true, true], [true, true, true, true, true, true, true, false, true, true, false, true, false], [true, true, true, true, false, true, true, true, false, true, false, false, true]], S := [false, true, true, true, true, false, true, true, true, false, true, true, true], val := [[], [], [], [], [], [], [], [], [], [], [], [], []] }

/-- The gadget over the chain `k₀ < k₁`, `p₂` at `k₁`. -/
def TCb : SubTab.SubCM := { n := 12, root := 10, le := [[true, false, false, false, false, false, false, false, false, false, false, false], [false, true, false, false, false, false, false, false, false, false, false, false], [true, false, true, false, false, false, false, false, false, false, false, false], [true, true, false, true, false, false, false, false, false, false, false, false], [true, true, true, false, true, false, false, false, false, false, false, false], [true, true, false, false, false, true, false, false, false, false, false, false], [true, true, true, false, false, true, true, false, false, false, false, false], [true, true, true, true, false, true, false, true, false, false, false, false], [true, true, true, true, true, true, false, false, true, false, false, false], [true, true, true, false, false, true, false, false, false, true, false, false], [true, true, true, true, true, true, true, true, true, true, true, true], [true, true, true, true, false, true, true, true, false, true, false, true]], S := [false, true, true, true, true, false, true, true, true, false, true, true], val := [[], [], [], [], [], [], [], [], [], [], [], []] }

/-- The gadget over the fork `k₀ < k₁, k₂`, `p₀` at `k₁`, `p₂` at `k₂`. -/
def TCc : SubTab.SubCM := { n := 13, root := 10, le := [[true, false, false, false, false, false, false, false, false, false, false, false, false], [false, true, false, false, false, false, false, false, false, false, false, false, false], [true, false, true, false, false, false, false, false, false, false, false, false, false], [true, true, false, true, false, false, false, false, false, false, false, false, false], [true, true, true, false, true, false, false, false, false, false, false, false, false], [true, true, false, false, false, true, false, false, false, false, false, false, false], [true, true, true, false, false, true, true, false, false, false, false, false, false], [true, true, true, true, false, true, false, true, false, false, false, false, false], [true, true, true, true, true, true, false, false, true, false, false, false, false], [true, true, true, false, false, true, false, false, false, true, false, false, false], [true, true, true, true, true, true, true, true, true, true, true, true, true], [true, true, true, true, true, true, true, true, true, true, false, true, false], [true, true, true, true, false, true, true, true, false, true, false, false, true]], S := [false, true, true, true, true, false, true, true, true, false, true, false, true], val := [[], [], [], [], [], [], [], [], [], [], [], [], []] }

/-- The base facts of the gadget, as Boolean checks on a table (worlds as above). -/
def baseFacts (T : SubTab.SubCM) : Bool :=
  T.okB &&
  (List.range 6).all (fun i => T.forceB i b2) &&
  [6, 7, 8, 9].all (fun i => !(T.forceB i b2)) &&
  [6, 7, 8, 9].all (fun i => (List.range T.n).all fun j => !(T.leB i j) || j == i || T.forceB j b2) &&
  (List.range 10).all (fun i => T.forceB i b3) &&
  ((List.range T.n).filter (· ≥ 10)).all (fun i => !(T.forceB i b3)) &&
  !(T.forceB 7 (sepC 1)) && T.forceB 6 (sepC 1) && T.forceB 8 (sepC 1) && T.forceB 9 (sepC 1) &&
  !(T.forceB 8 (sepC 2)) && T.forceB 6 (sepC 2) && T.forceB 7 (sepC 2) && T.forceB 9 (sepC 2) &&
  T.forceB 7 ((sepC 1).ifThen b2) && T.forceB 8 ((sepC 2).ifThen b2) &&
  T.SB 6 && !(T.SB 9) && T.forceB 9 (.somehow b2) && T.forceB 9 xf

theorem baseFacts_Ca : baseFacts TCa = true := by decide +kernel

theorem baseFacts_Cb : baseFacts TCb = true := by decide +kernel

theorem baseFacts_Cc : baseFacts TCc = true := by decide +kernel

/-- `gen i` at `w_k` iff `p_i` at `k` (rows `w_{k₀}`, `w_{k₁}`, `w_{k₂}`; columns `i = 0, 1, 2`). -/
theorem read_Ca : ([10, 11, 12].map fun k => ([0, 1, 2].map fun i => TCa.forceB k (gen i))) =
    [[false, false, false], [false, true, false], [false, false, true]] := by decide +kernel

theorem read_Cb : ([10, 11].map fun k => ([0, 1, 2].map fun i => TCb.forceB k (gen i))) =
    [[false, false, false], [false, false, true]] := by decide +kernel

theorem read_Cc : ([10, 11, 12].map fun k => ([0, 1, 2].map fun i => TCc.forceB k (gen i))) =
    [[false, false, false], [true, false, false], [false, false, true]] := by decide +kernel

/-- **Cell Ca PASSES**: `⊬ (x₁ ↠ x₂) ∨ (x₂ ↠ x₁)`. -/
theorem cell_Ca : ¬ Deriv [] (relB b3 x3 Ca) := SubTab.no.verdict (relB b3 x3 Ca) TCa

/-- **Cell Cb PASSES**: `⊬ ((x₂ ↠ σ³⊥) ↠ σ³⊥) ↠ x₂`. -/
theorem cell_Cb : ¬ Deriv [] (relB b3 x3 Cb) := SubTab.no.verdict (relB b3 x3 Cb) TCb

/-- **Cell Cc PASSES**: `⊬ (x₀ ↠ x₂) ∨ (x₂ ↠ x₀)`. -/
theorem cell_Cc : ¬ Deriv [] (relB b3 x3 Cc) := SubTab.no.verdict (relB b3 x3 Cc) TCc

/-! ## Stage 2 (a): p-morphisms preserve forcing -/

/-- **Forcing is invariant under p-morphisms** (monotone, back condition, `S`
and the valuation preserved and reflected). -/
theorem force_pmorph (N M : SubframeModel) (f : N.W → M.W)
    (hle : ∀ {a b}, N.le a b → M.le (f a) (f b))
    (hback : ∀ a v, M.le (f a) v → ∃ b, N.le a b ∧ f b = v)
    (hS : ∀ a, f a ∈ M.S ↔ a ∈ N.S)
    (hV : ∀ x a, f a ∈ M.V x ↔ a ∈ N.V x) :
    ∀ (φ : PLLFormula) (a : N.W), (M.force (f a) φ ↔ N.force a φ)
  | .prop x, a => hV x a
  | .falsePLL, _ => Iff.rfl
  | .and A B, a => and_congr (force_pmorph N M f hle hback hS hV A a)
      (force_pmorph N M f hle hback hS hV B a)
  | .or A B, a => or_congr (force_pmorph N M f hle hback hS hV A a)
      (force_pmorph N M f hle hback hS hV B a)
  | .ifThen A B, a => by
      have ihA := force_pmorph N M f hle hback hS hV A
      have ihB := force_pmorph N M f hle hback hS hV B
      show (∀ v, M.le (f a) v → M.force v A → M.force v B) ↔
        (∀ b, N.le a b → N.force b A → N.force b B)
      constructor
      · intro h b hab hA
        exact (ihB b).mp (h (f b) (hle hab) ((ihA b).mpr hA))
      · intro h v hv hA
        obtain ⟨b, hab, rfl⟩ := hback a v hv
        exact (ihB b).mpr (h b hab ((ihA b).mp hA))
  | .somehow A, a => by
      have ihA := force_pmorph N M f hle hback hS hV A
      show (∀ v, M.le (f a) v → v ∈ M.S → M.force v A) ↔
        (∀ b, N.le a b → b ∈ N.S → N.force b A)
      constructor
      · intro h b hab hbS
        exact (ihA b).mp (h (f b) (hle hab) ((hS b).mpr hbS))
      · intro h v hv hvS
        obtain ⟨b, hab, rfl⟩ := hback a v hv
        exact (ihA b).mpr (h b hab ((hS b).mp hvS))

/-! ## Stage 2 (b): the cells `ZL r` -/

namespace Cell

/-- The bottom `m` of `ZL r`. -/
def bot (r : Nat) : (ZL.M r).W := ⟨r + 4, ZL.lt4 r⟩

theorem bot_S (r : Nat) : bot r ∈ (ZL.M r).S :=
  show r + 4 ≠ 0 ∧ r + 4 ≠ r + 3 from ⟨by omega, by omega⟩

theorem eq_bot {r : Nat} {a : (ZL.M r).W} (h : a.1 = r + 4) : a = bot r := Subtype.ext h

/-- Every world of `ZL r` but the bottom forces `σ²⊥`. -/
theorem b2_of_ne {r : Nat} (a : (ZL.M r).W) (h : a.1 ≠ r + 4) : (ZL.M r).force a b2 :=
  ZL.force_b2 a.2 h

theorem not_b2_bot (r : Nat) : ¬ (ZL.M r).force (bot r) b2 := ZL.not_force_b2_m (ZL.lt4 r)

/-- **Every world of `ZL r` forces `σ³⊥`**: the bottom is `σ²⊥`-maximal and in
`S`, so it forces `◯σ²⊥ ↠ σ²⊥`; every other world forces `σ²⊥`, hence `◯σ²⊥`. -/
theorem b3_all {r : Nat} (a : (ZL.M r).W) : (ZL.M r).force a b3 := by
  rcases Decidable.em (a.1 = r + 4) with h | h
  · have ha : a = bot r := eq_bot h
    subst ha
    show (ZL.M r).force (bot r) (PLLFormula.somehow b2) ∨
      (ZL.M r).force (bot r) ((PLLFormula.somehow b2).ifThen b2)
    refine Or.inr fun v _ hc => ?_
    rcases Decidable.em (v.1 = r + 4) with hv4 | hv4
    · have hvb : v = bot r := eq_bot hv4
      subst hvb
      exact absurd (hc (bot r) ((ZL.M r).refl _) (bot_S r)) (not_b2_bot r)
    · exact b2_of_ne v hv4
  · exact Or.inl fun v hv _ => SubframeModel.force_mono _ b2 hv (b2_of_ne a h)

theorem phi_bot (r k : Nat) : (ZL.M r).force (bot r) (phiK k) ↔ r + 2 ≤ k := ZL.cell_force r k

/-- **`c_s` holds at the bottom of `ZL r` for `r ≠ s`.** -/
theorem sep_bot {r s : Nat} (h : r ≠ s) : (ZL.M r).force (bot r) (sepC s) := by
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · exact Or.inl ((phi_bot r (s + 1)).mpr (by omega))
  · refine Or.inr fun v _ hφ => ?_
    rcases Decidable.em (v.1 = r + 4) with hv4 | hv4
    · have hvb : v = bot r := eq_bot hv4
      subst hvb
      exact absurd ((phi_bot r (s + 2)).mp hφ) (Nat.not_le_of_gt (Nat.add_lt_add_right hgt 2))
    · exact b2_of_ne v hv4

/-- **`c_r ↠ σ²⊥` holds at the bottom of `ZL r`** (it refutes `c_r`, and
every proper successor forces `σ²⊥`). -/
theorem sepimp_bot (r : Nat) : (ZL.M r).force (bot r) ((sepC r).ifThen b2) := by
  show ∀ v, (ZL.M r).le (bot r) v → (ZL.M r).force v (sepC r) → (ZL.M r).force v b2
  intro v _ hc
  rcases Decidable.em (v.1 = r + 4) with hv4 | hv4
  · have hvb : v = bot r := eq_bot hv4
    subst hvb
    rcases hc with hφ | himp
    · exact absurd ((phi_bot r (r + 1)).mp hφ) (Nat.not_le_of_gt (Nat.lt_succ_self (r + 1)))
    · exact himp _ ((ZL.M r).refl _) ((phi_bot r (r + 2)).mpr (Nat.le_refl _))
  · exact b2_of_ne v hv4

end Cell

/-- At a world forcing `◯Y`, every relativised odd rung holds (`p` is an
iterated first disjunct of `rn (2k+1)`). -/
theorem force_relX_rnP (M : SubframeModel) (v : M.W) (hx : M.force v xf) :
    ∀ k, M.force v (ZL.relX (rnP k).1)
  | 0 => hx
  | k + 1 => Or.inl (force_relX_rnP M v hx k)

theorem force_phiK_of_xf (M : SubframeModel) (v : M.W) (hx : M.force v xf) (k : Nat) :
    M.force v (phiK k) := by
  unfold phiK
  rw [rn_odd_eq]
  exact force_relX_rnP M v hx k

/-! ## Stage 2 (c): the gadget -/

namespace Gad

/-- The worlds of the gadget over a Kripke model with worlds `α`: a copy of
every cell `ZL r` (`z r a`), the non-`S` killer `kn`, and a copy `w k` of each
world `k`. -/
inductive Pt (α : Type) where
  | z (r : Nat) (a : (ZL.M r).W)
  | kn
  | w (k : α)

variable (K : SubframeModel) (D : Nat → K.W → Prop)

/-- The order: inside each cell `ZL r` its own order; `kn` sees the
non-bottom worlds of `ZL 0` (whose bottom it copies, out of `S`); `w_j ≤ w_k`
iff `j ≤ k`; `w_k` sees `kn` and all of `ZL 0`, and all of `ZL (r+1)` iff
`D (r+1) k`. -/
def Le : Pt K.W → Pt K.W → Prop
  | .z r a, .z r' a' => r = r' ∧ ZL.Le r a.1 a'.1
  | .kn, .kn => True
  | .kn, .z r a => r = 0 ∧ a.1 < 4
  | .w j, .w k => K.le j k
  | .w _, .kn => True
  | .w _, .z 0 _ => True
  | .w k, .z (r + 1) _ => D (r + 1) k
  | _, _ => False

/-- `S`: the `S` of each cell; `kn ∉ S`; `w_k ∈ S` iff `D 0 k`. -/
def SP : Pt K.W → Prop
  | .z r a => a ∈ (ZL.M r).S
  | .kn => False
  | .w k => D 0 k

variable {K D}

theorem Le.refl : ∀ a : Pt K.W, Le K D a a
  | .z r a => ⟨rfl, ZL.Le.refl r a.1⟩
  | .kn => trivial
  | .w k => K.refl k

theorem lt4_of {a b : Nat} (ha : a < 4) (hb : b < 5) (h : ZL.Le 0 a b) : b < 4 := by
  unfold ZL.Le at h
  rcases h with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, h'⟩ | h <;> omega

theorem Le.trans (hD : ∀ r {j k : K.W}, K.le j k → D r k → D r j) {a b c : Pt K.W}
    (h₁ : Le K D a b) (h₂ : Le K D b c) : Le K D a c := by
  cases a with
  | z r a =>
    cases b with
    | z r' b =>
      cases c with
      | z r'' c =>
        obtain ⟨e₁, h₁⟩ := h₁
        obtain ⟨e₂, h₂⟩ := h₂
        subst e₁
        subst e₂
        exact ⟨rfl, ZL.Le.trans h₁ h₂⟩
      | kn => exact False.elim h₂
      | w _ => exact False.elim h₂
    | kn => exact False.elim h₁
    | w _ => exact False.elim h₁
  | kn =>
    cases b with
    | z r b =>
      cases c with
      | z r' c =>
        obtain ⟨e₁, hb⟩ := h₁
        obtain ⟨e₂, h₂⟩ := h₂
        subst e₁
        subst e₂
        exact ⟨rfl, lt4_of hb c.2 h₂⟩
      | kn => exact False.elim h₂
      | w _ => exact False.elim h₂
    | kn => exact h₂
    | w _ => exact False.elim h₁
  | w j =>
    cases b with
    | z r b =>
      cases c with
      | z r' c =>
        obtain ⟨e₂, _⟩ := h₂
        subst e₂
        cases r with
        | zero => trivial
        | succ r => exact h₁
      | kn => exact False.elim h₂
      | w _ => exact False.elim h₂
    | kn =>
      cases c with
      | z r c =>
        obtain ⟨e₂, _⟩ := h₂
        subst e₂
        trivial
      | kn => trivial
      | w _ => exact False.elim h₂
    | w k =>
      cases c with
      | z r c =>
        cases r with
        | zero => trivial
        | succ r => exact hD (r + 1) h₁ h₂
      | kn => trivial
      | w l => exact K.trans h₁ h₂

/-- **The gadget model `M(K, D)`**; no atoms. -/
def MK (hD : ∀ r {j k : K.W}, K.le j k → D r k → D r j) : SubframeModel where
  W := Pt K.W
  le := Le K D
  S := SP K D
  V _ := fun _ => False
  refl := Le.refl
  trans h₁ h₂ := Le.trans hD h₁ h₂
  hered _ h := False.elim h

variable (hD : ∀ r {j k : K.W}, K.le j k → D r k → D r j)

/-- **The cells embed as generated submodels**: forcing at `z r a` is forcing
at `a` in `ZL r`. -/
theorem zforce (r : Nat) (φ : PLLFormula) (a : (ZL.M r).W) :
    (MK hD).force (Pt.z r a) φ ↔ (ZL.M r).force a φ :=
  force_pmorph (ZL.M r) (MK hD) (Pt.z r) (fun h => ⟨rfl, h⟩)
    (fun a v hv => by
      cases v with
      | z r' b =>
        obtain ⟨e, hl⟩ := hv
        subst e
        exact ⟨b, hl, rfl⟩
      | kn => exact False.elim hv
      | w _ => exact False.elim hv)
    (fun _ => Iff.rfl) (fun _ _ => Iff.rfl) φ a

theorem z_b3 (r : Nat) (a : (ZL.M r).W) : (MK hD).force (Pt.z r a) b3 :=
  (zforce hD r b3 a).mpr (Cell.b3_all a)

/-! ### The killers -/

/-- The `S`-killer: the bottom of `ZL 0`. -/
theorem kS_S : (Pt.z 0 (Cell.bot 0) : (MK hD).W) ∈ (MK hD).S := Cell.bot_S 0

theorem kS_not_b2 : ¬ (MK hD).force (Pt.z 0 (Cell.bot 0)) b2 := fun h =>
  Cell.not_b2_bot 0 ((zforce hD 0 b2 _).mp h)

theorem kn_succ {v : (MK hD).W} (hv : (MK hD).le Pt.kn v) :
    v = Pt.kn ∨ ∃ a : (ZL.M 0).W, a.1 < 4 ∧ v = Pt.z 0 a := by
  cases v with
  | z r a =>
    obtain ⟨e, ha⟩ := hv
    subst e
    exact Or.inr ⟨a, ha, rfl⟩
  | kn => exact Or.inl rfl
  | w _ => exact False.elim hv

/-- `kn ⊩ ◯Y`: its `S`-successors are `n₀`, `L₀` of `ZL 0`. -/
theorem kn_xf : (MK hD).force Pt.kn xf := by
  show ∀ v, (MK hD).le Pt.kn v → v ∈ (MK hD).S → (MK hD).force v Yf
  intro v hv hS
  rcases kn_succ hD hv with h | ⟨a, ha, h⟩
  · subst h
    exact False.elim hS
  · subst h
    have hS' : a.1 ≠ 0 ∧ a.1 ≠ 0 + 3 := hS
    obtain ⟨_, h3⟩ := hS'
    exact (zforce hD 0 Yf a).mpr ((ZL.force_Y_iff a.2).mpr (by omega))

/-- `kn ⊮ σ²⊥`: `◯t3` fails by `L₀`, `◯t3 ↠ t3` by `f`. -/
theorem kn_not_b2 : ¬ (MK hD).force Pt.kn b2 := by
  intro h
  have h' : (MK hD).force Pt.kn SigOnto.c1F ∨ (MK hD).force Pt.kn SigOnto.g1F := h
  rcases h' with hc | hg
  · have h2 := hc (Pt.z 0 ⟨2, ZL.lt2 0⟩) ⟨rfl, by decide⟩ ⟨by decide, by decide⟩
    exact ZL.not_force_t3 (ZL.lt2 0) (Nat.le_refl 2) ((zforce hD 0 t3 _).mp h2)
  · have h3 := hg (Pt.z 0 ⟨3, ZL.lt3 0⟩) ⟨rfl, by decide⟩
      ((zforce hD 0 _ _).mpr (ZL.force_c1_f (ZL.lt3 0)))
    exact ZL.not_force_t3 (ZL.lt3 0) (by decide) ((zforce hD 0 t3 _).mp h3)

/-- `kn ⊩ ◯σ²⊥`. -/
theorem kn_c2 : (MK hD).force Pt.kn (.somehow b2) := by
  show ∀ v, (MK hD).le Pt.kn v → v ∈ (MK hD).S → (MK hD).force v b2
  intro v hv hS
  rcases kn_succ hD hv with h | ⟨a, ha, h⟩
  · subst h
    exact False.elim hS
  · subst h
    exact (zforce hD 0 b2 a).mpr (Cell.b2_of_ne a (by omega))

theorem kn_b3 : (MK hD).force Pt.kn b3 := Or.inl (kn_c2 hD)

theorem kn_sep (s : Nat) : (MK hD).force Pt.kn (sepC s) :=
  Or.inl (force_phiK_of_xf _ _ (kn_xf hD) (s + 1))

/-! ### The copies `w_k` -/

/-- **`w_k ⊮ σ³⊥`**: `◯σ²⊥` fails by the `S`-killer, `◯σ²⊥ ↠ σ²⊥` by `kn`. -/
theorem w_not_b3 (k : K.W) : ¬ (MK hD).force (Pt.w k) b3 := by
  intro h
  have h' : (MK hD).force (Pt.w k) (PLLFormula.somehow b2) ∨
      (MK hD).force (Pt.w k) ((PLLFormula.somehow b2).ifThen b2) := h
  rcases h' with hc | hg
  · exact kS_not_b2 hD (hc (Pt.z 0 (Cell.bot 0)) trivial (kS_S hD))
  · exact kn_not_b2 hD (hg Pt.kn trivial (kn_c2 hD))

/-- The back condition: every successor of `w_k` forces `σ³⊥` or is a `w_j`, `j ≥ k`. -/
theorem w_back (k : K.W) (v : (MK hD).W) (hv : (MK hD).le (Pt.w k) v) :
    (MK hD).force v b3 ∨ ∃ j, K.le k j ∧ Pt.w j = v := by
  cases v with
  | z r a => exact Or.inl (z_b3 hD r a)
  | kn => exact Or.inl (kn_b3 hD)
  | w j => exact Or.inr ⟨j, hv, rfl⟩

/-- **`x₀ = ◯σ³⊥` reads `¬ D 0`.** -/
theorem w_gen0 (k : K.W) : (MK hD).force (Pt.w k) (gen 0) ↔ ¬ D 0 k := by
  constructor
  · intro hx hk
    exact w_not_b3 hD k (hx (Pt.w k) (K.refl k) hk)
  · intro hk
    show ∀ v, (MK hD).le (Pt.w k) v → v ∈ (MK hD).S → (MK hD).force v b3
    intro v hv hS
    cases v with
    | z r a => exact z_b3 hD r a
    | kn => exact kn_b3 hD
    | w j => exact absurd (hD 0 hv hS) hk

/-- **`x_{s+1}` reads `¬ D (s+1)`.** -/
theorem w_gen_succ (k : K.W) (s : Nat) :
    (MK hD).force (Pt.w k) (gen (s + 1)) ↔ ¬ D (s + 1) k := by
  constructor
  · intro hx hk
    rcases hx with hb | himp
    · exact w_not_b3 hD k hb
    · have hr : (MK hD).force (Pt.z (s + 1) (Cell.bot (s + 1))) ((sepC (s + 1)).ifThen b2) :=
        (zforce hD (s + 1) _ _).mpr (Cell.sepimp_bot (s + 1))
      exact Cell.not_b2_bot (s + 1) ((zforce hD (s + 1) b2 _).mp (himp _ hk hr))
  · intro hk
    refine Or.inr ?_
    show ∀ v, (MK hD).le (Pt.w k) v → (MK hD).force v ((sepC (s + 1)).ifThen b2) →
      (MK hD).force v b2
    intro v hv hsep
    cases v with
    | z r a =>
      rcases Decidable.em (a.1 = r + 4) with h4 | h4
      · have ha : a = Cell.bot r := Cell.eq_bot h4
        subst ha
        rcases Decidable.em (r = s + 1) with hr | hr
        · subst hr
          exact absurd hv hk
        · exact hsep _ ((MK hD).refl _) ((zforce hD r _ _).mpr (Cell.sep_bot hr))
      · exact (zforce hD r b2 a).mpr (Cell.b2_of_ne a h4)
    | kn => exact hsep _ ((MK hD).refl _) (kn_sep hD (s + 1))
    | w j => exact absurd (hsep Pt.kn trivial (kn_sep hD (s + 1))) (kn_not_b2 hD)

end Gad

/-! ## Stage 2 (d): the generators read the variables; the transfer -/

/-- `σ³⊥ ≤ gen r` at every world of every model. -/
theorem b3_le_gen_sem (M : SubframeModel) (v : M.W) (r : Nat) (hv : M.force v b3) :
    M.force v (gen r) := by
  cases r with
  | zero => exact fun u hu _ => SubframeModel.force_mono M b3 hu hv
  | succ s => exact Or.inl hv

theorem b3_le_x3_sem (M : SubframeModel) (v : M.W) (a : String) (hv : M.force v b3) :
    M.force v (x3 a) := b3_le_gen_sem M v _ hv

/-- `pvar i` has `i + 1` UTF-8 bytes. -/
theorem utf8ByteSize_pvar : ∀ i, (pvar i).utf8ByteSize = i + 1
  | 0 => by decide
  | i + 1 => by
      have h : pvar (i + 1) = String.ofList ['p'] ++ pvar i := by
        show String.ofList (['p'] ++ List.replicate (i + 1) 'p') = _
        rw [String.ofList_append]
        rfl
      have h1 : (String.ofList ['p']).utf8ByteSize = 1 := by decide
      rw [h, String.utf8ByteSize_append, utf8ByteSize_pvar i, h1, Nat.add_comm]

theorem idx_pvar (i : Nat) : idx (pvar i) = i := by
  unfold idx
  rw [utf8ByteSize_pvar]
  rfl

/-- **`x3 (pvar i) = gen i`.** -/
theorem x3_pvar (i : Nat) : x3 (pvar i) = gen i := by
  unfold x3
  rw [idx_pvar]

namespace Gad

/-- The reading for `x3`: `D r k ⟺ k ⊮ pvar r`. -/
def Dp (K : SubframeModel) (r : Nat) (k : K.W) : Prop := k ∉ K.V (pvar r)

theorem Dp_down (K : SubframeModel) : ∀ r {j k : K.W}, K.le j k → Dp K r k → Dp K r j :=
  fun _ _ _ hjk hk hj => hk (K.hered hjk hj)

variable {K : SubframeModel} [FinDec K]

/-- **The generators read the valuation**: `w_k ⊩ gen i ⟺ k ⊩ pvar i`. -/
theorem w_read (k : K.W) (i : Nat) :
    (MK (Dp_down K)).force (Pt.w k) (gen i) ↔ k ∈ K.V (pvar i) := by
  cases i with
  | zero => exact (w_gen0 (Dp_down K) k).trans Decidable.not_not
  | succ s => exact (w_gen_succ (Dp_down K) k s).trans Decidable.not_not

/-- **The gadget transfer**: for ◯-free `A` over `pvar 0, …, pvar (n-1)`,

    w_k ⊩_{M(K)} relB σ³⊥ x3 A   ⟺   k ⊩_K A. -/
theorem transfer (n : Nat) : ∀ A : PLLFormula, boxFree A = true → varsBelow n A = true →
    ∀ k : K.W, ((MK (Dp_down K)).force (Pt.w k) (relB b3 x3 A) ↔ K.force k A) :=
  relB_transfer (MK (Dp_down K)) b3 x3 K Pt.w n (b3_le_x3_sem _) (w_not_b3 _) (fun h => h)
    (w_back _) (fun k i _ => by rw [x3_pvar]; exact w_read k i)

end Gad

/-! ## Stage 2 (e): `Free3` -/

/-- **`Free3`, direction `⟹`** (substitution). -/
theorem free3_preserves {n : Nat} {A B : PLLFormula} (hA : boxFree A = true)
    (hB : boxFree B = true) (vA : varsBelow n A = true) (vB : varsBelow n B = true)
    (hd : Deriv [A] B) : Deriv [relB b3 x3 A] (relB b3 x3 B) :=
  relB_preserves b3 x3 n b3_le_x3_sem hA hB vA vB hd

/-- **`Free3`, direction `⟸`** (faithfulness), by the gadget over every finite
Kripke model. -/
theorem free3_reflects {n : Nat} {A B : PLLFormula} (hA : boxFree A = true)
    (hB : boxFree B = true) (vA : varsBelow n A = true) (vB : varsBelow n B = true)
    (hd : Deriv [relB b3 x3 A] (relB b3 x3 B)) : Deriv [A] B := by
  obtain ⟨d⟩ := hd
  have hsem : ∀ (K : SubframeModel) [FinDec K] (k : K.W), K.force k A → K.force k B := by
    intro K _ k hk
    exact (Gad.transfer n B hB vB k).mp
      (SubframeModel.CF.soundness₁ d (Gad.MK (Gad.Dp_down K)) (Gad.Pt.w k)
        ((Gad.transfer n A hA vA k).mpr hk))
  have h2 : Deriv [] (A.ifThen B) := SubframeModel.CF.completeness_imp hsem
  exact Deriv.impElim (h2.rename fun _ h => absurd h List.not_mem_nil) (Deriv.iden (.head _))

/-- **PROVED: `Free3`.** -/
theorem free3 : Free3 := fun _ _ _ hA hB vA vB =>
  ⟨free3_preserves hA hB vA vB, free3_reflects hA hB vA vB⟩

/-- **PROVED: `FreeFamily3`.** -/
theorem freeFamily3 : FreeFamily3 := freeFamily3_of_free3 free3

/-- **PROVED: `[σ³⊥, ⊤]` contains the free Heyting algebra on `n` generators,
for every `n`, all from the one family `x3`.** -/
theorem freeHAnAbove_base3 (n : Nat) : FreeHAnAbove (base 3) n :=
  freeHAnAbove_of_family freeFamily3 n

/-- **PROVED: the conjecture** `∀ n ∃ m, FreeHAnAbove (σᵐ⊥) n`, with `m = 3`. -/
theorem conjecture : Conjecture := conjecture_of_base3 freeHAnAbove_base3

end Base3
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.Base3.base_three [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.x3_vf [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.b3_le_x3 [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.freeFamily3_of_free3 [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.freeHAnAbove_of_family [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.conjecture_of_base3 [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.side_cell [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.ipc_Ca [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.ipc_Cb [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.ipc_Cc [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.baseFacts_Ca [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.baseFacts_Cb [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.baseFacts_Cc [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.read_Ca [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.read_Cb [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.read_Cc [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.cell_Ca [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.cell_Cb [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.cell_Cc [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.force_pmorph [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Cell.b3_all [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Cell.sep_bot [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Cell.sepimp_bot [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.force_phiK_of_xf [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Gad.Le.trans [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Gad.zforce [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Gad.kn_xf [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Gad.kn_not_b2 [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Gad.w_not_b3 [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Gad.w_gen0 [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Gad.w_gen_succ [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.utf8ByteSize_pvar [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.x3_pvar [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Gad.w_read [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.Gad.transfer [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.free3_preserves [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.free3_reflects [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.free3 [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.freeFamily3 [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.freeHAnAbove_base3 [propext, Quot.sound]
#axioms_within PLLND.F0.Base3.conjecture [propext, Quot.sound]
