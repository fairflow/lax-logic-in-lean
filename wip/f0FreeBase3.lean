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
