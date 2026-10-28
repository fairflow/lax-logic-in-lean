import wip.f0FreeBase3
import Meta.Audit

/-!
# Any family of reader cells over `σ³⊥`; the σ-shift of a free copy

Follow-up to `wip/f0FreeBase3.lean` (brief 2026-10-28).  There the readers of
the generators are the bottoms of the cells `ZL r`.  Here (Goal 1) the
readers are ANY pairwise separated `σ²⊥`-maximal cells, and (Goal 2) a free
copy above a variable-free base `b` is carried by `σᵏ` to a free copy above
`σᵏ b`.

## The statements (committed before any proof, METHOD.md §1)

Goal 1, the choice of reader family does not matter:

    AnyFamily3 :  ∀ n,  Distinct σ²⊥ (n + 1)  →  FreeHAnAbove σ³⊥ n

and the cleaner variant with the two killers inside the family:

    CellsKill n F :  (∀ i j ≤ n, i ≠ j → F i, F j separated) ∧
                     F 0 ⊮ ◯σ²⊥ ∧ F 1 ⊩ ◯σ²⊥            (at the σ²⊥-maximal worlds)
    FromCells3 :  ∀ n F,  CellsKill n F  →  FreeHAnAbove σ³⊥ n

Goal 2, the σ-shift (for variable-free `b`):

    SigShift  :  ∀ b vf, ∀ k n,  FreeHAnAbove b n  →  FreeHAnAbove (σᵏ b) n
    SigShiftω :  ∀ b vf, ∀ k,    FreeHAωAbove b    →  FreeHAωAbove (σᵏ b)
    AllAbove3  :  ∀ m ≥ 3, ∀ n,  FreeHAnAbove σᵐ⊥ n
    AllAbove3ω :  ∀ m ≥ 3,       FreeHAωAbove σᵐ⊥

Fragment first (CLAUDE.md rule 8): as in `f0FreeBase3`, the ◯-free
variable-free fragment is `{⊥, ⊤}`; degenerate.

Status note: `wip/f0FreeAnyFamily-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace AnyFamily

open SemUI RNEmbed Sig FreeIPL FreeHAn Pair Base3
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ## The statements -/

/-- **Goal 1**: any `n + 1` pairwise separated `σ²⊥`-maximal cells give a copy
of the free Heyting algebra on `n` generators in `[σ³⊥, ⊤]`. -/
def AnyFamily3 : Prop := ∀ n, Distinct (base 2) (n + 1) → FreeHAnAbove (base 3) n

/-- The hypothesis of the cleaner variant: the cells `F 0, …, F n` pairwise
separated, `F 0` refuting `◯σ²⊥` and `F 1` forcing it at its `σ²⊥`-maximal
world (the two killers; `F 2, …, F n` are the readers). -/
def CellsKill (n : Nat) (F : Nat → Cell (base 2)) : Prop :=
  (∀ i j, i ≤ n → j ≤ n → i ≠ j → (F i).Separated (F j)) ∧
  ¬ (F 0).M.force (F 0).w (.somehow (base 2)) ∧ (F 1).M.force (F 1).w (.somehow (base 2))

/-- **The cleaner variant of Goal 1.** -/
def FromCells3 : Prop := ∀ (n : Nat) (F : Nat → Cell (base 2)), CellsKill n F → FreeHAnAbove (base 3) n

/-- **Goal 2**: the σ-shift of a free copy on `n` generators. -/
def SigShift : Prop :=
  ∀ b : PLLFormula, atomFree b = true → ∀ k n, FreeHAnAbove b n → FreeHAnAbove (sigN k b) n

/-- **Goal 2, every variable a generator.** -/
def SigShiftω : Prop :=
  ∀ b : PLLFormula, atomFree b = true → ∀ k, FreeHAωAbove b → FreeHAωAbove (sigN k b)

/-- **The corollary**: every base `σᵐ⊥`, `m ≥ 3`, carries every finite free copy. -/
def AllAbove3 : Prop := ∀ m, 3 ≤ m → ∀ n, FreeHAnAbove (base m) n

/-- **The corollary, every variable a generator.** -/
def AllAbove3ω : Prop := ∀ m, 3 ≤ m → FreeHAωAbove (base m)

/-! ## The generators for a family of separators -/

/-- The generators for separators `c`: `x₀ = ◯σ³⊥`, `x_g = σ³⊥ ∨ ((c g ↠ σ²⊥) ↠ σ²⊥)`. -/
def genC (c : Nat → PLLFormula) : Nat → PLLFormula
  | 0 => .somehow b3
  | r + 1 => b3.or (((c (r + 1)).ifThen b2).ifThen b2)

/-- The generator assignment `xC c a = genC c (idx a)`, so `xC c (pvar i) = genC c i`. -/
def xC (c : Nat → PLLFormula) (a : String) : PLLFormula := genC c (Base3.idx a)

/-- `f0FreeBase3`'s generators are the instance `c = sepC`. -/
theorem gen_eq_genC : gen = genC sepC := by
  funext r
  cases r <;> rfl

/-! ## Stage 1: one designed instance with another reader family (CLAUDE.md rules 7, 9)

`n = 3`.  The killers: `F 0` = the bottom `m₀` of `ZL 0` (it refutes `◯σ²⊥`),
`F 1` = `kn`, the bottom of `ZL 0` taken out of `S` (it forces `◯σ²⊥`).  The
readers in the REVERSED order: `p₁` is read by `m₂` (the bottom of `ZL 2`),
`p₂` by `m₁` (the bottom of `ZL 1`); in `f0FreeBase3` `p_r` is read by `m_r`.
The separators by the recipe of the general proof (a disjunction, one
disjunct for each other distinguished world, holding there and failing at the
reader; a separating formula of the wrong orientation `φ` is turned by
`φ ↦ φ ↠ σ²⊥`):

    c₁ = φ₂ ∨ (φ₂ ∨ φ₃)               fails at m₂; φ₂ for m₀, kn; φ₃ for m₁
    c₂ = φ₂ ∨ (φ₂ ∨ (φ₃ ↠ σ²⊥))       fails at m₁; φ₂ for m₀, kn; φ₃ ↠ σ²⊥ for m₂

(`φ₃` holds at `m₁` and fails at `m₂`: the wrong orientation for `c₂`.)
The upper structure is shared as in `f0FreeBase3` (worlds `0 e₀`, `1 n₀`,
`2–4 L₀–L₂`, `5 f`, `6 m₀`, `7 m₁`, `8 m₂`, `9 kn`); the copies `w_k` (from
`10`) see the cones of `m₀` and `kn` always, the cone of `m₂` iff `k ⊮ p₁`,
the cone of `m₁` iff `k ⊮ p₂`, and are in `S` iff `k ⊮ p₀`.  Tables written
by a script from that description (transitivity asserted there and by `okB`). -/

set_option maxRecDepth 100000

/-- The Stage 1 separators. -/
def sepS1 : Nat → PLLFormula
  | 1 => (phiK 2).or ((phiK 2).or (phiK 3))
  | 2 => (phiK 2).or ((phiK 2).or ((phiK 3).ifThen b2))
  | _ => .falsePLL

/-- The control: `c₂` with the separating formula `φ₃` left in the wrong orientation. -/
def sepNaive : Nat → PLLFormula
  | 1 => (phiK 2).or ((phiK 2).or (phiK 3))
  | 2 => (phiK 2).or ((phiK 2).or (phiK 3))
  | _ => .falsePLL

/-- The gadget over the fork `k₀ < k₁, k₂`, `p₁` at `k₁`, `p₂` at `k₂`. -/
def T1a : SubTab.SubCM := { n := 13, root := 10, le := [[true, false, false, false, false, false, false, false, false, false, false, false, false], [false, true, false, false, false, false, false, false, false, false, false, false, false], [true, false, true, false, false, false, false, false, false, false, false, false, false], [true, true, false, true, false, false, false, false, false, false, false, false, false], [true, true, true, false, true, false, false, false, false, false, false, false, false], [true, true, false, false, false, true, false, false, false, false, false, false, false], [true, true, true, false, false, true, true, false, false, false, false, false, false], [true, true, true, true, false, true, false, true, false, false, false, false, false], [true, true, true, true, true, true, false, false, true, false, false, false, false], [true, true, true, false, false, true, false, false, false, true, false, false, false], [true, true, true, true, true, true, true, true, true, true, true, true, true], [true, true, true, true, false, true, true, true, false, true, false, true, false], [true, true, true, true, true, true, true, false, true, true, false, false, true]], S := [false, true, true, true, true, false, true, true, true, false, true, true, true], val := [[], [], [], [], [], [], [], [], [], [], [], [], []] }

/-- The gadget over the chain `k₀ < k₁`, `p₂` at `k₁`. -/
def T1b : SubTab.SubCM := { n := 12, root := 10, le := [[true, false, false, false, false, false, false, false, false, false, false, false], [false, true, false, false, false, false, false, false, false, false, false, false], [true, false, true, false, false, false, false, false, false, false, false, false], [true, true, false, true, false, false, false, false, false, false, false, false], [true, true, true, false, true, false, false, false, false, false, false, false], [true, true, false, false, false, true, false, false, false, false, false, false], [true, true, true, false, false, true, true, false, false, false, false, false], [true, true, true, true, false, true, false, true, false, false, false, false], [true, true, true, true, true, true, false, false, true, false, false, false], [true, true, true, false, false, true, false, false, false, true, false, false], [true, true, true, true, true, true, true, true, true, true, true, true], [true, true, true, true, true, true, true, false, true, true, false, true]], S := [false, true, true, true, true, false, true, true, true, false, true, true], val := [[], [], [], [], [], [], [], [], [], [], [], []] }

/-- The gadget over the fork `k₀ < k₁, k₂`, `p₀` at `k₁`, `p₂` at `k₂`. -/
def T1c : SubTab.SubCM := { n := 13, root := 10, le := [[true, false, false, false, false, false, false, false, false, false, false, false, false], [false, true, false, false, false, false, false, false, false, false, false, false, false], [true, false, true, false, false, false, false, false, false, false, false, false, false], [true, true, false, true, false, false, false, false, false, false, false, false, false], [true, true, true, false, true, false, false, false, false, false, false, false, false], [true, true, false, false, false, true, false, false, false, false, false, false, false], [true, true, true, false, false, true, true, false, false, false, false, false, false], [true, true, true, true, false, true, false, true, false, false, false, false, false], [true, true, true, true, true, true, false, false, true, false, false, false, false], [true, true, true, false, false, true, false, false, false, true, false, false, false], [true, true, true, true, true, true, true, true, true, true, true, true, true], [true, true, true, true, true, true, true, true, true, true, false, true, false], [true, true, true, true, true, true, true, false, true, true, false, false, true]], S := [false, true, true, true, true, false, true, true, true, false, true, false, true], val := [[], [], [], [], [], [], [], [], [], [], [], [], []] }

/-- The base facts of the Stage 1 gadget, for separators `c`: `0 … 5` force
`σ²⊥`; `6 … 9` refute it and are `σ²⊥`-maximal; every non-copy forces `σ³⊥`,
every copy refutes it; `m₀ ⊮ ◯σ²⊥`, `kn ⊩ ◯σ²⊥`; `c 1` fails at `m₂` and
holds at `m₀`, `m₁`, `kn`; `c 2` fails at `m₁` and holds at `m₀`, `m₂`, `kn`. -/
def baseFacts1 (c : Nat → PLLFormula) (T : SubTab.SubCM) : Bool :=
  T.okB &&
  (List.range 6).all (fun i => T.forceB i b2) &&
  [6, 7, 8, 9].all (fun i => !(T.forceB i b2)) &&
  [6, 7, 8, 9].all (fun i => (List.range T.n).all fun j => !(T.leB i j) || T.leB j i || T.forceB j b2) &&
  (List.range 10).all (fun i => T.forceB i b3) &&
  ((List.range T.n).filter (· ≥ 10)).all (fun i => !(T.forceB i b3)) &&
  !(T.forceB 6 (.somehow b2)) && T.forceB 9 (.somehow b2) &&
  !(T.forceB 8 (c 1)) && T.forceB 6 (c 1) && T.forceB 7 (c 1) && T.forceB 9 (c 1) &&
  !(T.forceB 7 (c 2)) && T.forceB 6 (c 2) && T.forceB 8 (c 2) && T.forceB 9 (c 2)

theorem baseFacts1_a : baseFacts1 sepS1 T1a = true := by decide +kernel

theorem baseFacts1_b : baseFacts1 sepS1 T1b = true := by decide +kernel

theorem baseFacts1_c : baseFacts1 sepS1 T1c = true := by decide +kernel

/-- The two-way turn: `φ₃` holds at `m₁` and fails at `m₂`; `φ₃ ↠ σ²⊥` holds
at `m₂` and fails at `m₁`. -/
theorem twoWay1 : (T1a.forceB 7 (phiK 3), T1a.forceB 8 (phiK 3),
    T1a.forceB 8 ((phiK 3).ifThen b2), T1a.forceB 7 ((phiK 3).ifThen b2)) =
    (true, false, true, false) := by decide +kernel

/-- **The control fails**: with `φ₃` in the wrong orientation, `c₂` fails at
`m₂`, so the base facts fail. -/
theorem control_naive : baseFacts1 sepNaive T1a = false := by decide +kernel

/-- `genC sepS1 i` at `w_k` iff `p_i` at `k` (rows `w_{k₀}`, `w_{k₁}`, `w_{k₂}`; columns `i = 0, 1, 2`). -/
theorem read1_a : ([10, 11, 12].map fun k => ([0, 1, 2].map fun i => T1a.forceB k (genC sepS1 i))) =
    [[false, false, false], [false, true, false], [false, false, true]] := by decide +kernel

theorem read1_b : ([10, 11].map fun k => ([0, 1, 2].map fun i => T1b.forceB k (genC sepS1 i))) =
    [[false, false, false], [false, false, true]] := by decide +kernel

theorem read1_c : ([10, 11, 12].map fun k => ([0, 1, 2].map fun i => T1c.forceB k (genC sepS1 i))) =
    [[false, false, false], [true, false, false], [false, false, true]] := by decide +kernel

/-- **Cell Ca PASSES** with the reversed readers: `⊬ (x₁ ↠ x₂) ∨ (x₂ ↠ x₁)`. -/
theorem cell1_Ca : ¬ Deriv [] (relB b3 (xC sepS1) Ca) := SubTab.no.verdict (relB b3 (xC sepS1) Ca) T1a

/-- **Cell Cb PASSES**: `⊬ ((x₂ ↠ σ³⊥) ↠ σ³⊥) ↠ x₂`. -/
theorem cell1_Cb : ¬ Deriv [] (relB b3 (xC sepS1) Cb) := SubTab.no.verdict (relB b3 (xC sepS1) Cb) T1b

/-- **Cell Cc PASSES**: `⊬ (x₀ ↠ x₂) ∨ (x₂ ↠ x₀)`. -/
theorem cell1_Cc : ¬ Deriv [] (relB b3 (xC sepS1) Cc) := SubTab.no.verdict (relB b3 (xC sepS1) Cc) T1c

end AnyFamily
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.AnyFamily.gen_eq_genC [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.baseFacts1_a [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.baseFacts1_b [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.baseFacts1_c [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.twoWay1 [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.control_naive [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.read1_a [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.read1_b [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.read1_c [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.cell1_Ca [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.cell1_Cb [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.cell1_Cc [propext, Quot.sound]
