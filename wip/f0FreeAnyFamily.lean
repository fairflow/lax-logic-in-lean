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

## Results

**PROVED, all six statements**, pins `[propext, Quot.sound]`, no
`Classical.choice`, no `sorry`, no `native_decide`:
`anyFamily3` (hence `freeHAnAbove_base3_of_distinct`, and `f0FreeBase3`'s
`∀ n, FreeHAnAbove σ³⊥ n` again from `base2_unbounded`, `freeHAnAbove_base3'`),
`fromCells3`, `sigShift`, `sigShiftω`, `allAbove3`, `allAbove3ω`.

* Stage 1: one designed instance, readers in the reversed order, separators
  by the recipe below (`cell1_Ca`, `cell1_Cb`, `cell1_Cc`, tables).
* The gadget over ANY upper model `U` (`GadU.MK`): the copies `w_k` of a finite
  `K` see `vis k`, an up-set of `U`; the killers are a world `dS ⊮ ◯σ²⊥` and a
  world `dN ⊩ ◯σ²⊥`, `dN ⊮ σ²⊥`, visible from every copy.  For a family of
  cells, `U` is their disjoint sum (`Sum`, each summand a generated submodel,
  `sum_force`), the killers are the cells `F 0`, `F 1`, the reader of `p_g` is
  `F (g+1)`, visible from `w_k` iff `k ⊮ p_g`.
* Separators (`disj_sep`): `c_g` is a disjunction, one disjunct for each other
  cell, holding there and failing at the reader; a separating formula `φ` of
  the wrong orientation is turned, `φ ↦ φ ↠ σ²⊥` (`orient`, `turn`).
* From `Distinct σ²⊥ (n + 1)` (`anyFamily3`): each given cell forces `◯σ²⊥` or
  not (decidable, a finite cell).  The `S`-killer is a given cell refuting
  `◯σ²⊥` if there is one, else the bottom of `ZL 0`, separated from every
  given cell by `◯σ²⊥` itself; likewise the non-`S` killer, with `kn`
  (`kNcell`, the bottom of `ZL 0` out of `S`).  The readers are the given cells
  less those two (`skip2_props`).  No case split on equality of theories.
* The σ-shift: `σᵏ (relB b x A) = relB (σᵏ b) (σᵏ ∘ x) A` for every `A`
  (`sigN_relB`), then `sigN_faithful` and `sigN_mono` of `wip/f0SelfSim.lean`;
  `σᵏ (σᵐ⊥) = σᵐ⁺ᵏ⊥` (`sigN_base`).

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

/-! ## Stage 2 (a): the generators -/

theorem genC_vf (c : Nat → PLLFormula) (hc : ∀ g, atomFree (c g) = true) :
    ∀ r, atomFree (genC c r) = true
  | 0 => rfl
  | r + 1 => by
      show (atomFree b3 && ((atomFree (c (r + 1)) && atomFree b2) && atomFree b2)) = true
      rw [hc]
      rfl

theorem b3_le_genC (c : Nat → PLLFormula) : ∀ r, Deriv [b3] (genC c r)
  | 0 => (Deriv.iden (.head _) : Deriv [b3] b3).elim fun d => ⟨.laxIntro d⟩
  | _ + 1 => Deriv.orIntro1 (Deriv.iden (.head _))

theorem b3_le_genC_sem (c : Nat → PLLFormula) (M : SubframeModel) (v : M.W) (r : Nat)
    (hv : M.force v b3) : M.force v (genC c r) := by
  cases r with
  | zero => exact fun u hu _ => SubframeModel.force_mono M b3 hu hv
  | succ s => exact Or.inl hv

theorem xC_pvar (c : Nat → PLLFormula) (i : Nat) : xC c (pvar i) = genC c i := by
  unfold xC
  rw [idx_pvar]

/-! ## Stage 2 (b): cells -/

/-- Forcing at the `σ²⊥`-maximal world of a cell. -/
def holds {b : PLLFormula} (C : Cell b) (φ : PLLFormula) : Prop := C.M.force C.w φ

instance holds_dec {b : PLLFormula} (C : Cell b) (φ : PLLFormula) : Decidable (holds C φ) :=
  @SubframeModel.CF.decForce C.M C.fin C.w φ

/-- **Every world above the `σ²⊥`-maximal world of a cell forces `σ³⊥`.** -/
theorem cone_b3 (C : Cell b2) (v : C.M.W) (hv : C.M.le C.w v) : C.M.force v b3 := by
  haveI := C.fin
  have hw : C.M.force C.w b3 := by
    show C.M.force C.w (PLLFormula.somehow b2) ∨ C.M.force C.w ((PLLFormula.somehow b2).ifThen b2)
    rcases Decidable.em (C.M.force C.w (PLLFormula.somehow b2)) with h | h
    · exact Or.inl h
    · refine Or.inr fun u hu hc => Decidable.byContradiction fun hb => h ?_
      exact SubframeModel.force_mono C.M _ (C.max.2 u hu hb) hc
  exact SubframeModel.force_mono C.M b3 hv hw

/-- **The turn**: at a `σ²⊥`-maximal world refuting `φ`, `φ ↠ σ²⊥` holds. -/
theorem turn (C : Cell b2) {φ : PLLFormula} (h : ¬ holds C φ) : holds C (φ.ifThen b2) := by
  haveI := C.fin
  show ∀ v, C.M.le C.w v → C.M.force v φ → C.M.force v b2
  intro v hv hφ
  exact Decidable.byContradiction fun hb => h (SubframeModel.force_mono C.M φ (C.max.2 v hv hb) hφ)

/-- At a `σ²⊥`-maximal world forcing `φ`, `φ ↠ σ²⊥` fails. -/
theorem not_turn (C : Cell b2) {φ : PLLFormula} (h : holds C φ) : ¬ holds C (φ.ifThen b2) :=
  fun hi => C.max.1 (hi C.w (C.M.refl _) h)

theorem sep_symm {b : PLLFormula} {C C' : Cell b} (h : C.Separated C') : C'.Separated C :=
  let ⟨φ, hφ, hne⟩ := h
  ⟨φ, hφ, fun hi => hne hi.symm⟩

/-- **Two-way separation**: separated `σ²⊥`-maximal worlds are separated in
the orientation asked for (`φ ↦ φ ↠ σ²⊥` turns a separating formula). -/
theorem orient {C t : Cell b2} (h : C.Separated t) :
    ∃ ψ, atomFree ψ = true ∧ holds C ψ ∧ ¬ holds t ψ := by
  obtain ⟨φ, hφ, hne⟩ := h
  rcases Decidable.em (holds C φ) with hC | hC
  · exact ⟨φ, hφ, hC, fun ht => hne ⟨fun _ => ht, fun _ => hC⟩⟩
  · have ht : holds t φ := Decidable.byContradiction fun ht =>
      hne ⟨fun h => absurd h hC, fun h => absurd h ht⟩
    refine ⟨φ.ifThen b2, ?_, turn C hC, not_turn t ht⟩
    show (atomFree φ && atomFree b2) = true
    rw [hφ]
    rfl

/-- Separation by `◯σ²⊥`. -/
theorem sep_box {C C' : Cell b2} (h : ¬ holds C (.somehow b2)) (h' : holds C' (.somehow b2)) :
    C.Separated C' :=
  ⟨.somehow b2, rfl, fun hi => h (hi.mpr h')⟩

/-! ## Stage 2 (c): the separators -/

/-- **The reader separator**: a disjunction failing at `t` and holding at every
`F j`, `j < m`, `Q j`, each separated from `t`. -/
theorem disj_sep (t : Cell b2) (F : Nat → Cell b2) (Q : Nat → Prop) [DecidablePred Q] :
    ∀ m, (∀ j, j < m → Q j → (F j).Separated t) →
      ∃ c, atomFree c = true ∧ ¬ holds t c ∧ ∀ j, j < m → Q j → holds (F j) c
  | 0, _ => ⟨.falsePLL, rfl, fun h => h, fun _ hj _ => absurd hj (Nat.not_lt_zero _)⟩
  | m + 1, h => by
      obtain ⟨c, hc, hfail, hhold⟩ := disj_sep t F Q m fun j hj hQ => h j (Nat.lt_succ_of_lt hj) hQ
      rcases Decidable.em (Q m) with hQ | hQ
      · obtain ⟨ψ, hψ, hψF, hψt⟩ := orient (h m (Nat.lt_succ_self m) hQ)
        refine ⟨c.or ψ, ?_, ?_, ?_⟩
        · show (atomFree c && atomFree ψ) = true
          rw [hc, hψ]
          rfl
        · rintro (h1 | h2)
          · exact hfail h1
          · exact hψt h2
        · intro j hj hQj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
          · exact Or.inl (hhold j hlt hQj)
          · subst heq
            exact Or.inr hψF
      · refine ⟨c, hc, hfail, fun j hj hQj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · exact hhold j hlt hQj
        · subst heq
          exact absurd hQj hQ

/-- Finite choice of variable-free formulas, without `Classical.choice`. -/
theorem choose_vf (P : Nat → PLLFormula → Prop) :
    ∀ m, (∀ i, i < m → ∃ φ, atomFree φ = true ∧ P i φ) →
      ∃ f : Nat → PLLFormula, (∀ i, atomFree (f i) = true) ∧ ∀ i, i < m → P i (f i)
  | 0, _ => ⟨fun _ => .falsePLL, fun _ => rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | m + 1, h => by
      obtain ⟨f, hf, hP⟩ := choose_vf P m fun i hi => h i (Nat.lt_succ_of_lt hi)
      obtain ⟨φ, hφ, hPφ⟩ := h m (Nat.lt_succ_self m)
      refine ⟨fun i => if i = m then φ else f i, fun i => ?_, fun i hi => ?_⟩
      · show atomFree (if i = m then φ else f i) = true
        split
        · exact hφ
        · exact hf i
      · show P i (if i = m then φ else f i)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · rw [if_neg (Nat.ne_of_lt hlt)]
          exact hP i hlt
        · rw [if_pos heq]
          subst heq
          exact hPφ

/-! ## Stage 2 (d): the disjoint sum of a family of models -/

/-- The order of the disjoint sum. -/
def SumLe (F : Nat → SubframeModel) : (Σ r, (F r).W) → (Σ r, (F r).W) → Prop
  | ⟨r, a⟩, ⟨r', b⟩ => ∃ h : r = r', (F r').le (h ▸ a) b

theorem SumLe.refl (F : Nat → SubframeModel) : ∀ p, SumLe F p p
  | ⟨r, a⟩ => ⟨rfl, (F r).refl a⟩

theorem SumLe.trans (F : Nat → SubframeModel) :
    ∀ {p q s : Σ r, (F r).W}, SumLe F p q → SumLe F q s → SumLe F p s
  | ⟨r, a⟩, ⟨_, b⟩, ⟨_, c⟩, ⟨e1, l1⟩, ⟨e2, l2⟩ => by
      subst e1
      subst e2
      exact ⟨rfl, (F r).trans l1 l2⟩

theorem SumLe.hered (F : Nat → SubframeModel) {x : String} :
    ∀ {p q : Σ r, (F r).W}, SumLe F p q → p.2 ∈ (F p.1).V x → q.2 ∈ (F q.1).V x
  | ⟨r, a⟩, ⟨_, b⟩, ⟨e, l⟩, hv => by
      subst e
      exact (F r).hered l hv

/-- **The disjoint sum** of a family of subframe models. -/
def Sum (F : Nat → SubframeModel) : SubframeModel where
  W := Σ r, (F r).W
  le := SumLe F
  S := fun p => p.2 ∈ (F p.1).S
  V x := fun p => p.2 ∈ (F p.1).V x
  refl := SumLe.refl F
  trans h1 h2 := SumLe.trans F h1 h2
  hered h hv := SumLe.hered F h hv

/-- **Each summand is a generated submodel of the sum.** -/
theorem sum_force (F : Nat → SubframeModel) (r : Nat) :
    ∀ (φ : PLLFormula) (a : (F r).W), (Sum F).force ⟨r, a⟩ φ ↔ (F r).force a φ :=
  force_pmorph (F r) (Sum F) (fun a => ⟨r, a⟩) (fun h => ⟨rfl, h⟩)
    (fun a v hv => by
      obtain ⟨r', b⟩ := v
      obtain ⟨e, l⟩ := hv
      subst e
      exact ⟨b, l, rfl⟩)
    (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)

/-! ## Stage 2 (e): the gadget over any upper model `U` -/

namespace GadU

/-- The worlds: the worlds `u a` of `U` and the copies `w k` of `K`. -/
inductive Pt (α β : Type) where
  | u (a : α)
  | w (k : β)

variable {U K : SubframeModel} (S0 : K.W → Prop) (vis : K.W → U.W → Prop)

/-- The order: `U`'s order, `K`'s order on the copies, `w k ≤ u b` iff `vis k b`. -/
def Le : Pt U.W K.W → Pt U.W K.W → Prop
  | .u a, .u b => U.le a b
  | .w j, .w k => K.le j k
  | .w k, .u b => vis k b
  | .u _, .w _ => False

/-- `S`: `U`'s `S`; `w k ∈ S` iff `S0 k`. -/
def SP : Pt U.W K.W → Prop
  | .u a => a ∈ U.S
  | .w k => S0 k

/-- The valuation: `U`'s on `U`, empty on the copies. -/
def VP (x : String) : Pt U.W K.W → Prop
  | .u a => a ∈ U.V x
  | .w _ => False

/-- The conditions: `S0` a down-set; `vis k` an up-set of `U`, antitone in `k`. -/
structure Hyp : Prop where
  S0_down : ∀ {j k : K.W}, K.le j k → S0 k → S0 j
  vis_up : ∀ {k : K.W} {a b : U.W}, vis k a → U.le a b → vis k b
  vis_down : ∀ {j k : K.W} {b : U.W}, K.le j k → vis k b → vis j b

theorem Le.refl : ∀ p : Pt U.W K.W, Le vis p p
  | .u a => U.refl a
  | .w k => K.refl k

variable {S0 vis}

theorem Le.trans (h : Hyp S0 vis) {p q s : Pt U.W K.W} (h1 : Le vis p q) (h2 : Le vis q s) :
    Le vis p s := by
  cases p <;> cases q <;> cases s
  · exact U.trans h1 h2
  · exact False.elim h2
  · exact False.elim h1
  · exact False.elim h1
  · exact h.vis_up h1 h2
  · exact False.elim h2
  · exact h.vis_down h1 h2
  · exact K.trans h1 h2

theorem hered {x : String} {p q : Pt U.W K.W} (hl : Le vis p q) (hv : VP x p) : VP x q := by
  cases p with
  | u a =>
    cases q with
    | u b => exact U.hered hl hv
    | w _ => exact False.elim hl
  | w _ => exact False.elim hv

/-- **The gadget model.** -/
def MK (h : Hyp S0 vis) : SubframeModel where
  W := Pt U.W K.W
  le := Le vis
  S := SP S0
  V x := VP x
  refl := Le.refl vis
  trans h1 h2 := Le.trans h h1 h2
  hered h1 h2 := hered h1 h2

variable (h : Hyp S0 vis)

/-- **`U` is a generated submodel of the gadget.** -/
theorem uforce : ∀ (φ : PLLFormula) (a : U.W), (MK h).force (.u a) φ ↔ U.force a φ :=
  force_pmorph U (MK h) Pt.u (fun hl => hl)
    (fun a v hv => by
      cases v with
      | u b => exact ⟨b, hv, rfl⟩
      | w _ => exact False.elim hv)
    (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)

/-- **The copies refute `σ³⊥`**, given a world `dS ⊮ ◯σ²⊥` and a world
`dN ⊩ ◯σ²⊥`, `dN ⊮ σ²⊥` above every copy. -/
theorem w_not_b3 {dS dN : U.W} (hvS : ∀ k, vis k dS) (hvN : ∀ k, vis k dN)
    (hS : ¬ U.force dS (.somehow b2)) (hN : U.force dN (.somehow b2)) (hN2 : ¬ U.force dN b2)
    (k : K.W) : ¬ (MK h).force (.w k) b3 := by
  intro hb
  have hb' : (MK h).force (.w k) (PLLFormula.somehow b2) ∨
      (MK h).force (.w k) ((PLLFormula.somehow b2).ifThen b2) := hb
  rcases hb' with hc | hg
  · exact hS ((uforce h _ dS).mp (SubframeModel.force_mono (MK h) (.somehow b2)
      (show (MK h).le (.w k) (.u dS) from hvS k) hc))
  · exact hN2 ((uforce h b2 dN).mp (hg (.u dN) (hvN k) ((uforce h _ dN).mpr hN)))

/-- The back condition. -/
theorem w_back (hb3 : ∀ k b, vis k b → U.force b b3) (k : K.W) (v : (MK h).W)
    (hv : (MK h).le (.w k) v) : (MK h).force v b3 ∨ ∃ j, K.le k j ∧ Pt.w j = v := by
  cases v with
  | u b => exact Or.inl ((uforce h b3 b).mpr (hb3 k b hv))
  | w j => exact Or.inr ⟨j, hv, rfl⟩

/-- **`x₀ = ◯σ³⊥` reads `¬ S0`.** -/
theorem w_gen0 (hb3 : ∀ k b, vis k b → U.force b b3)
    (hnot : ∀ k, ¬ (MK h).force (.w k) b3) (k : K.W) :
    (MK h).force (.w k) (.somehow b3) ↔ ¬ S0 k := by
  constructor
  · intro hx hk
    exact hnot k (hx (.w k) (K.refl k) hk)
  · intro hk
    show ∀ v, (MK h).le (.w k) v → v ∈ (MK h).S → (MK h).force v b3
    intro v hv hS
    cases v with
    | u b => exact (uforce h b3 b).mpr (hb3 k b hv)
    | w j => exact absurd (h.S0_down hv hS) hk

/-- **`x_g` fails at a copy that sees its reader.** -/
theorem w_gen_false {c : PLLFormula} {k : K.W} {ρ : U.W} (hv : vis k ρ)
    (hρ : U.force ρ (c.ifThen b2)) (hρ2 : ¬ U.force ρ b2)
    (hnot : ¬ (MK h).force (.w k) b3) :
    ¬ (MK h).force (.w k) (b3.or ((c.ifThen b2).ifThen b2)) := by
  rintro (hb | himp)
  · exact hnot hb
  · exact hρ2 ((uforce h b2 ρ).mp (himp (.u ρ) hv ((uforce h _ ρ).mpr hρ)))

/-- **`x_g` holds at a copy all of whose `U`-successors force `c`.** -/
theorem w_gen_true {c : PLLFormula} {k : K.W} {dN : U.W} (hvN : ∀ k, vis k dN)
    (hN2 : ¬ U.force dN b2) (hc : ∀ b, vis k b → U.force b c) :
    (MK h).force (.w k) (b3.or ((c.ifThen b2).ifThen b2)) := by
  refine Or.inr ?_
  show ∀ v, (MK h).le (.w k) v → (MK h).force v (c.ifThen b2) → (MK h).force v b2
  intro v hv himp
  cases v with
  | u b => exact himp (.u b) ((MK h).refl _) ((uforce h c b).mpr (hc b hv))
  | w j =>
    exact absurd ((uforce h b2 dN).mp (himp (.u dN) (hvN j)
      ((uforce h c dN).mpr (hc dN (hvN k))))) hN2

end GadU

/-! ## Stage 2 (f): the gadget for a family of cells -/

section Family

variable (n : Nat) (F : Nat → Cell b2)

/-- The upper model: the disjoint sum of the cells. -/
abbrev UF : SubframeModel := Sum (fun r => (F r).M)

/-- The distinguished worlds `d r = (r, w_r)`. -/
def dw (r : Nat) : (UF F).W := ⟨r, (F r).w⟩

theorem dw_force (r : Nat) (φ : PLLFormula) : (UF F).force (dw F r) φ ↔ holds (F r) φ :=
  sum_force (fun r => (F r).M) r φ (F r).w

theorem dw_cone_b3 (r : Nat) (b : (UF F).W) (hb : (UF F).le (dw F r) b) : (UF F).force b b3 := by
  obtain ⟨r', v⟩ := b
  obtain ⟨e, l⟩ := hb
  subst e
  exact (sum_force (fun r => (F r).M) r b3 v).mpr (cone_b3 (F r) v l)

/-- Visibility from the copy `w k`: the cones of `d 0`, `d 1` always, the cone
of `d (g+1)` iff `k ⊮ p_g` (`1 ≤ g < n`). -/
def visF (K : SubframeModel) (k : K.W) (b : (UF F).W) : Prop :=
  (UF F).le (dw F 0) b ∨ (UF F).le (dw F 1) b ∨
    ∃ g, 1 ≤ g ∧ g < n ∧ k ∉ K.V (pvar g) ∧ (UF F).le (dw F (g + 1)) b

/-- `w k ∈ S` iff `k ⊮ p₀`. -/
def S0p (K : SubframeModel) (k : K.W) : Prop := k ∉ K.V (pvar 0)

theorem hypF (K : SubframeModel) : GadU.Hyp (S0p K) (visF n F K) where
  S0_down hjk hk hj := hk (K.hered hjk hj)
  vis_up hv hab := by
    rcases hv with h0 | h1 | ⟨g, hg1, hgn, hk, hle⟩
    · exact Or.inl ((UF F).trans h0 hab)
    · exact Or.inr (Or.inl ((UF F).trans h1 hab))
    · exact Or.inr (Or.inr ⟨g, hg1, hgn, hk, (UF F).trans hle hab⟩)
  vis_down hjk hv := by
    rcases hv with h0 | h1 | ⟨g, hg1, hgn, hk, hle⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨g, hg1, hgn, fun hj => hk (K.hered hjk hj), hle⟩)

theorem visF_b3 (K : SubframeModel) (k : K.W) (b : (UF F).W) (hv : visF n F K k b) :
    (UF F).force b b3 := by
  rcases hv with h0 | h1 | ⟨g, _, _, _, hle⟩
  · exact dw_cone_b3 F 0 b h0
  · exact dw_cone_b3 F 1 b h1
  · exact dw_cone_b3 F (g + 1) b hle

/-- **The gadget transfer** for a family of cells with separators `c`: for
◯-free `A` over `pvar 0, …, pvar (n-1)`, `w_k ⊩ relB σ³⊥ (xC c) A ⟺ k ⊩ A`. -/
theorem transferF (c : Nat → PLLFormula)
    (hfail : ∀ g, g < n → ¬ holds (F (g + 1)) (c g))
    (hhold : ∀ g, g < n → ∀ j, j ≤ n → j ≠ g + 1 → holds (F j) (c g))
    (hk0 : ¬ holds (F 0) (.somehow b2)) (hk1 : holds (F 1) (.somehow b2))
    (K : SubframeModel) [FinDec K] :
    ∀ A : PLLFormula, boxFree A = true → varsBelow n A = true →
      ∀ k : K.W, ((GadU.MK (hypF n F K)).force (.w k) (relB b3 (xC c) A) ↔ K.force k A) := by
  have hvS : ∀ k, visF n F K k (dw F 0) := fun _ => Or.inl ((UF F).refl _)
  have hvN : ∀ k, visF n F K k (dw F 1) := fun _ => Or.inr (Or.inl ((UF F).refl _))
  have hN2 : ¬ (UF F).force (dw F 1) b2 := fun h => (F 1).max.1 ((dw_force F 1 b2).mp h)
  have hnot := GadU.w_not_b3 (hypF n F K) hvS hvN (fun h => hk0 ((dw_force F 0 _).mp h))
    ((dw_force F 1 _).mpr hk1) hN2
  refine relB_transfer (GadU.MK (hypF n F K)) b3 (xC c) K GadU.Pt.w n
    (fun v _ hv => b3_le_genC_sem c _ v _ hv) hnot (fun hjk => hjk)
    (GadU.w_back (hypF n F K) (visF_b3 n F K)) ?_
  intro k i hi
  rw [xC_pvar]
  cases i with
  | zero => exact (GadU.w_gen0 (hypF n F K) (visF_b3 n F K) hnot k).trans Decidable.not_not
  | succ g =>
    constructor
    · intro hx
      refine Decidable.byContradiction fun hk => ?_
      have hv : visF n F K k (dw F (g + 1 + 1)) :=
        Or.inr (Or.inr ⟨g + 1, Nat.succ_le_succ (Nat.zero_le g), hi, hk, (UF F).refl _⟩)
      have hρ : (UF F).force (dw F (g + 1 + 1)) ((c (g + 1)).ifThen b2) :=
        (dw_force F _ _).mpr (turn (F (g + 1 + 1)) (hfail (g + 1) hi))
      have hρ2 : ¬ (UF F).force (dw F (g + 1 + 1)) b2 := fun h =>
        (F (g + 1 + 1)).max.1 ((dw_force F _ b2).mp h)
      exact GadU.w_gen_false (hypF n F K) hv hρ hρ2 (hnot k) hx
    · intro hk
      refine GadU.w_gen_true (hypF n F K) hvN hN2 fun b hv => ?_
      rcases hv with h0 | h1 | ⟨s, _, hsn, hks, hle⟩
      · exact SubframeModel.force_mono (UF F) _ h0
          ((dw_force F 0 _).mpr (hhold (g + 1) hi 0 (Nat.zero_le n) (Nat.succ_ne_zero _).symm))
      · have hne : (1 : Nat) ≠ g + 1 + 1 := fun e => Nat.succ_ne_zero g (Nat.succ.inj e).symm
        exact SubframeModel.force_mono (UF F) _ h1
          ((dw_force F 1 _).mpr (hhold (g + 1) hi 1 (by omega) hne))
      · have hne : s + 1 ≠ g + 1 + 1 := fun e => by
          have e' : s = g + 1 := Nat.succ.inj e
          rw [e'] at hks
          exact hks hk
        exact SubframeModel.force_mono (UF F) _ hle
          ((dw_force F (s + 1) _).mpr (hhold (g + 1) hi (s + 1) hsn hne))

/-- **A family of cells with separators gives a free copy above `σ³⊥`.** -/
theorem freeHAn_of_seps (c : Nat → PLLFormula) (hcvf : ∀ g, atomFree (c g) = true)
    (hfail : ∀ g, g < n → ¬ holds (F (g + 1)) (c g))
    (hhold : ∀ g, g < n → ∀ j, j ≤ n → j ≠ g + 1 → holds (F j) (c g))
    (hk0 : ¬ holds (F 0) (.somehow b2)) (hk1 : holds (F 1) (.somehow b2)) :
    FreeHAnAbove (base 3) n := by
  refine ⟨xC c, fun _ => genC_vf c hcvf _, fun _ => b3_le_genC c _, ?_⟩
  intro A B hA hB vA vB
  refine ⟨relB_preserves b3 (xC c) n (fun M v _ hv => b3_le_genC_sem c M v _ hv) hA hB vA vB, ?_⟩
  intro hd
  obtain ⟨d⟩ := hd
  have hsem : ∀ (K : SubframeModel) [FinDec K] (k : K.W), K.force k A → K.force k B := by
    intro K _ k hk
    exact (transferF n F c hfail hhold hk0 hk1 K B hB vB k).mp
      (SubframeModel.CF.soundness₁ d (GadU.MK (hypF n F K)) (GadU.Pt.w k)
        ((transferF n F c hfail hhold hk0 hk1 K A hA vA k).mpr hk))
  have h2 : Deriv [] (A.ifThen B) := SubframeModel.CF.completeness_imp hsem
  exact Deriv.impElim (h2.rename fun _ h => absurd h List.not_mem_nil) (Deriv.iden (.head _))

end Family

/-- **PROVED: `FromCells3`**, the cleaner variant. -/
theorem fromCells3 : FromCells3 := by
  intro n F ⟨hsep, hk0, hk1⟩
  have hex : ∀ g, g < n → ∃ c, atomFree c = true ∧
      (¬ holds (F (g + 1)) c ∧ ∀ j, j ≤ n → j ≠ g + 1 → holds (F j) c) := by
    intro g hg
    obtain ⟨c, hc, hfail, hhold⟩ := disj_sep (F (g + 1)) F (fun j => j ≠ g + 1) (n + 1)
      (fun j hj hne => hsep j (g + 1) (Nat.le_of_lt_succ hj) hg hne)
    exact ⟨c, hc, hfail, fun j hj hne => hhold j (Nat.lt_succ_of_le hj) hne⟩
  obtain ⟨c, hcvf, hc⟩ := choose_vf _ n hex
  exact freeHAn_of_seps n F c hcvf (fun g hg => (hc g hg).1) (fun g hg => (hc g hg).2) hk0 hk1

/-! ## Stage 2 (g): from `n + 1` separated cells to the cleaner variant -/

/-- The non-`S` killer as a table: the bottom of `ZL 0` (world `4`) out of `S`
(the table of `cell_11` of `f0FreeHAn`). -/
def TkN : SubTab.SubCM := { n := 5, root := 4, le := [[true, false, false, false, false], [false, true, false, false, false], [true, false, true, false, false], [true, true, false, true, false], [true, true, true, true, true]], S := [false, true, true, false, false], val := [[], [], [], [], []] }

theorem TkN_ok : TkN.okB = true := by decide +kernel

/-- `σ²⊥`-maximality of world `i` of a table, as a Boolean. -/
def bmaxB (T : SubTab.SubCM) (i : Nat) : Bool :=
  !(T.forceB i b2) && (List.range T.n).all (fun j => !(T.leB i j) || T.forceB j b2 || T.leB j i)

theorem bmax_of_B (T : SubTab.SubCM) (hT : T.okB = true) (i : (T.toModel hT).W)
    (hb : bmaxB T i.1 = true) : BMax b2 (T.toModel hT) i := by
  unfold bmaxB at hb
  rw [Bool.and_eq_true] at hb
  obtain ⟨h1, h2⟩ := hb
  refine ⟨fun hf => ?_, fun v hv hn => ?_⟩
  · rw [(SubTab.SubCM.forceB_iff hT b2 i).mpr hf] at h1
    exact Bool.false_ne_true h1
  · have h3 := List.all_eq_true.mp h2 v.1 (List.mem_range.mpr v.2)
    have hle : T.leB i.1 v.1 = true := hv
    have hf : T.forceB v.1 b2 = false := by
      cases hc : T.forceB v.1 b2
      · rfl
      · exact absurd ((SubTab.SubCM.forceB_iff hT b2 v).mp hc) hn
    rw [hle, hf] at h3
    exact h3

/-- **The non-`S` killer** as a cell. -/
def kNcell : Cell b2 where
  M := TkN.toModel TkN_ok
  fin := inferInstance
  w := ⟨4, by decide⟩
  max := bmax_of_B TkN TkN_ok ⟨4, by decide⟩ (by decide +kernel)

theorem kN_box : holds kNcell (.somehow b2) :=
  (SubTab.SubCM.forceB_iff TkN_ok (.somehow b2) ⟨4, by decide⟩).mp (by decide +kernel)

/-- The `S`-killer `ZL 0` refutes `◯σ²⊥` (its bottom is in `S`). -/
theorem kS_box : ¬ holds (ZL.cell 0) (.somehow b2) := fun h =>
  (ZL.cell 0).max.1 (h (ZL.cell 0).w ((ZL.cell 0).M.refl _) (Base3.Cell.bot_S 0))

/-- The given cells, then the two fixed killers at `n + 1` and `n + 2`. -/
def ext (n : Nat) (cs : Fin (n + 1) → Cell b2) (i : Nat) : Cell b2 :=
  if h : i < n + 1 then cs ⟨i, h⟩ else if i = n + 1 then ZL.cell 0 else kNcell

theorem ext_lt (n : Nat) (cs : Fin (n + 1) → Cell b2) (i : Nat) (h : i < n + 1) :
    ext n cs i = cs ⟨i, h⟩ := dif_pos h

theorem ext_S (n : Nat) (cs : Fin (n + 1) → Cell b2) : ext n cs (n + 1) = ZL.cell 0 := by
  unfold ext
  rw [dif_neg (Nat.lt_irrefl _), if_pos rfl]

theorem ext_N (n : Nat) (cs : Fin (n + 1) → Cell b2) : ext n cs (n + 2) = kNcell := by
  unfold ext
  rw [dif_neg (Nat.not_lt.mpr (Nat.le_succ (n + 1))), if_neg (Nat.succ_ne_self (n + 1))]

/-- Bounded search for a decidable predicate, without choice. -/
theorem bsearch (P : Nat → Prop) [DecidablePred P] :
    ∀ m, (∃ i, i < m ∧ P i) ∨ (∀ i, i < m → ¬ P i)
  | 0 => Or.inr fun _ hi => absurd hi (Nat.not_lt_zero _)
  | m + 1 => by
      rcases bsearch P m with ⟨i, hi, hP⟩ | hno
      · exact Or.inl ⟨i, Nat.lt_succ_of_lt hi, hP⟩
      · rcases Decidable.em (P m) with hm | hm
        · exact Or.inl ⟨m, Nat.lt_succ_self m, hm⟩
        · refine Or.inr fun i hi => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
          · exact hno i hlt
          · subst heq
            exact hm

/-- Skip the index `a`. -/
def skip (a r : Nat) : Nat := if r < a then r else r + 1

/-- An injection avoiding two given indices, moving each index by at most two. -/
theorem skip2_props (a b : Nat) (hab : a ≠ b) : ∃ σ : Nat → Nat, (∀ r, σ r ≤ r + 2) ∧
    (∀ r, σ r ≠ a) ∧ (∀ r, σ r ≠ b) ∧ (∀ r s, r ≠ s → σ r ≠ σ s) := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · refine ⟨fun r => skip b (skip a r), fun r => ?_, fun r => ?_, fun r => ?_, fun r s hrs => ?_⟩
    all_goals
      simp only [skip]
      split_ifs <;> omega
  · refine ⟨fun r => skip a (skip b r), fun r => ?_, fun r => ?_, fun r => ?_, fun r s hrs => ?_⟩
    all_goals
      simp only [skip]
      split_ifs <;> omega

/-- The family: the two killers, then the readers `G (σ r)`. -/
def famK (G : Nat → Cell b2) (iS iN : Nat) (σ : Nat → Nat) : Nat → Cell b2
  | 0 => G iS
  | 1 => G iN
  | r + 2 => G (σ r)

theorem famK_sep (n : Nat) (G : Nat → Cell b2) (iS iN : Nat) (σ : Nat → Nat)
    (hS : ¬ holds (G iS) (.somehow b2)) (hN : holds (G iN) (.somehow b2))
    (hσle : ∀ r, σ r ≤ r + 2) (hσinj : ∀ r s, r ≠ s → σ r ≠ σ s)
    (hG : ∀ i j, i ≤ n → j ≤ n → i ≠ j → (G i).Separated (G j))
    (hSsep : ∀ r, r + 2 ≤ n → (G (σ r)).Separated (G iS))
    (hNsep : ∀ r, r + 2 ≤ n → (G (σ r)).Separated (G iN)) :
    ∀ i j, i ≤ n → j ≤ n → i ≠ j → (famK G iS iN σ i).Separated (famK G iS iN σ j)
  | 0, 0, _, _, h => absurd rfl h
  | 0, 1, _, _, _ => sep_box hS hN
  | 0, s + 2, _, hj, _ => sep_symm (hSsep s hj)
  | 1, 0, _, _, _ => sep_symm (sep_box hS hN)
  | 1, 1, _, _, h => absurd rfl h
  | 1, s + 2, _, hj, _ => sep_symm (hNsep s hj)
  | r + 2, 0, hi, _, _ => hSsep r hi
  | r + 2, 1, hi, _, _ => hNsep r hi
  | r + 2, s + 2, hi, hj, h =>
      hG (σ r) (σ s) (Nat.le_trans (hσle r) hi) (Nat.le_trans (hσle s) hj)
        (hσinj r s fun e => h (by rw [e]))

/-- **PROVED: `AnyFamily3`**: any `n + 1` pairwise separated `σ²⊥`-maximal
cells give a free copy on `n` generators above `σ³⊥`. -/
theorem anyFamily3 : AnyFamily3 := by
  intro n ⟨cs, hcs⟩
  have hG : ∀ i j, i ≤ n → j ≤ n → i ≠ j → (ext n cs i).Separated (ext n cs j) := by
    intro i j hi hj hij
    rw [ext_lt n cs i (Nat.lt_succ_of_le hi), ext_lt n cs j (Nat.lt_succ_of_le hj)]
    exact hcs _ _ fun e => hij (congrArg Fin.val e)
  obtain ⟨iS, hiS, hS, hSall⟩ : ∃ iS, iS ≤ n + 1 ∧ ¬ holds (ext n cs iS) (.somehow b2) ∧
      (n + 1 ≤ iS → ∀ i, i ≤ n → holds (ext n cs i) (.somehow b2)) := by
    rcases bsearch (fun i => ¬ holds (ext n cs i) (.somehow b2)) (n + 1) with ⟨i, hi, h⟩ | hall
    · exact ⟨i, Nat.le_of_lt hi, h, fun h' => absurd (Nat.lt_of_lt_of_le hi h') (Nat.lt_irrefl _)⟩
    · refine ⟨n + 1, Nat.le_refl _, ?_, fun _ i hi =>
        Decidable.byContradiction fun h => hall i (Nat.lt_succ_of_le hi) h⟩
      rw [ext_S]
      exact kS_box
  obtain ⟨iN, hiN, hiN1, hN, hNall⟩ : ∃ iN, iN ≤ n + 2 ∧ iN ≠ n + 1 ∧
      holds (ext n cs iN) (.somehow b2) ∧
      (n + 1 ≤ iN → ∀ i, i ≤ n → ¬ holds (ext n cs i) (.somehow b2)) := by
    rcases bsearch (fun i => holds (ext n cs i) (.somehow b2)) (n + 1) with ⟨i, hi, h⟩ | hall
    · exact ⟨i, Nat.le_trans (Nat.le_of_lt hi) (Nat.le_succ _), Nat.ne_of_lt hi, h,
        fun h' => absurd (Nat.lt_of_lt_of_le hi h') (Nat.lt_irrefl _)⟩
    · refine ⟨n + 2, Nat.le_refl _, Nat.succ_ne_self _, ?_, fun _ i hi =>
        hall i (Nat.lt_succ_of_le hi)⟩
      rw [ext_N]
      exact kN_box
  have hne : iS ≠ iN := fun e => hS (e ▸ hN)
  obtain ⟨σ, hσle, hσS, hσN, hσinj⟩ := skip2_props iS iN hne
  have hSsep : ∀ r, r + 2 ≤ n → (ext n cs (σ r)).Separated (ext n cs iS) := by
    intro r hr
    have hσn : σ r ≤ n := Nat.le_trans (hσle r) hr
    rcases Nat.lt_or_ge iS (n + 1) with h | h
    · exact hG (σ r) iS hσn (Nat.le_of_lt_succ h) (hσS r)
    · exact sep_symm (sep_box hS (hSall h (σ r) hσn))
  have hNsep : ∀ r, r + 2 ≤ n → (ext n cs (σ r)).Separated (ext n cs iN) := by
    intro r hr
    have hσn : σ r ≤ n := Nat.le_trans (hσle r) hr
    rcases Nat.lt_or_ge iN (n + 1) with h | h
    · exact hG (σ r) iN hσn (Nat.le_of_lt_succ h) (hσN r)
    · exact sep_box (hNall h (σ r) hσn) hN
  exact fromCells3 n (famK (ext n cs) iS iN σ)
    ⟨famK_sep n (ext n cs) iS iN σ hS hN hσle hσinj hG hSsep hNsep, hS, hN⟩

/-- **PROVED (Goal 1)**: `Distinct σ²⊥ (n + 1) → FreeHAnAbove σ³⊥ n`. -/
theorem freeHAnAbove_base3_of_distinct (n : Nat) :
    Distinct (base 2) (n + 1) → FreeHAnAbove (base 3) n :=
  anyFamily3 n

/-- The check: `f0FreeBase3`'s theorem again, from `base2_unbounded`. -/
theorem freeHAnAbove_base3' (n : Nat) : FreeHAnAbove (base 3) n :=
  freeHAnAbove_base3_of_distinct n (base2_unbounded (n + 1))

/-! ## Goal 2: the σ-shift -/

/-- `σ` commutes with the relativisation: `σ (relB b x A) = relB (σ b) (σ ∘ x) A`. -/
theorem sig_relB (b : PLLFormula) (x : String → PLLFormula) :
    ∀ A : PLLFormula, sig (relB b x A) = relB (sig b) (fun a => sig (x a)) A
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and A B => by
      show (sig (relB b x A)).and (sig (relB b x B)) = _
      rw [sig_relB b x A, sig_relB b x B]
      rfl
  | .or A B => by
      show (sig (relB b x A)).or (sig (relB b x B)) = _
      rw [sig_relB b x A, sig_relB b x B]
      rfl
  | .ifThen A B => by
      show (sig (relB b x A)).ifThen (sig (relB b x B)) = _
      rw [sig_relB b x A, sig_relB b x B]
      rfl
  | .somehow A => by
      show (sig (relB b x A)).somehow = _
      rw [sig_relB b x A]
      rfl

/-- **The structural identity** `σᵏ (relB b x A) = relB (σᵏ b) (σᵏ ∘ x) A`, for every `A`. -/
theorem sigN_relB : ∀ (k : Nat) (b : PLLFormula) (x : String → PLLFormula) (A : PLLFormula),
    sigN k (relB b x A) = relB (sigN k b) (fun a => sigN k (x a)) A
  | 0, _, _, _ => rfl
  | k + 1, b, x, A => by
      show sigN k (sig (relB b x A)) = relB (sigN k (sig b)) (fun a => sigN k (sig (x a))) A
      rw [sig_relB]
      exact sigN_relB k (sig b) (fun a => sig (x a)) A

/-- The relativisation of any formula by a variable-free base and generators is variable-free. -/
theorem relB_vf {b : PLLFormula} {x : String → PLLFormula} (hb : atomFree b = true)
    (hx : ∀ a, atomFree (x a) = true) : ∀ A : PLLFormula, atomFree (relB b x A) = true
  | .prop a => hx a
  | .falsePLL => hb
  | .and A B => by
      show (atomFree (relB b x A) && atomFree (relB b x B)) = true
      rw [relB_vf hb hx A, relB_vf hb hx B]
      rfl
  | .or A B => by
      show (atomFree (relB b x A) && atomFree (relB b x B)) = true
      rw [relB_vf hb hx A, relB_vf hb hx B]
      rfl
  | .ifThen A B => by
      show (atomFree (relB b x A) && atomFree (relB b x B)) = true
      rw [relB_vf hb hx A, relB_vf hb hx B]
      rfl
  | .somehow A => relB_vf hb hx A

/-- **PROVED: the σ-shift**, `FreeHAnAbove b n → FreeHAnAbove (σᵏ b) n` for variable-free `b`. -/
theorem freeHAnAbove_sigN {b : PLLFormula} (hb : atomFree b = true) (k n : Nat) :
    FreeHAnAbove b n → FreeHAnAbove (sigN k b) n := by
  intro ⟨x, hvf, hle, hf⟩
  refine ⟨fun a => sigN k (x a), fun a => sigN_vf k (hvf a), fun a => sigN_mono k hb (hvf a) (hle a), ?_⟩
  intro A B hA hB vA vB
  rw [hf A B hA hB vA vB, sigN_faithful k (relB_vf hb hvf A) (relB_vf hb hvf B), sigN_relB,
    sigN_relB]

/-- **PROVED: the σ-shift, every variable a generator.** -/
theorem freeHAωAbove_sigN {b : PLLFormula} (hb : atomFree b = true) (k : Nat) :
    FreeHAωAbove b → FreeHAωAbove (sigN k b) := by
  intro ⟨x, hvf, hle, hf⟩
  refine ⟨fun a => sigN k (x a), fun a => sigN_vf k (hvf a), fun a => sigN_mono k hb (hvf a) (hle a), ?_⟩
  intro A B hA hB
  rw [hf A B hA hB, sigN_faithful k (relB_vf hb hvf A) (relB_vf hb hvf B), sigN_relB, sigN_relB]

theorem sigShift : SigShift := fun _ hb k n => freeHAnAbove_sigN hb k n

theorem sigShiftω : SigShiftω := fun _ hb k => freeHAωAbove_sigN hb k

/-- `σ ∘ σⁿ = σⁿ ∘ σ`. -/
theorem sig_sigN : ∀ (m : Nat) (φ : PLLFormula), sig (sigN m φ) = sigN m (sig φ)
  | 0, _ => rfl
  | m + 1, φ => sig_sigN m (sig φ)

/-- **Composition**: `σᵃ (σᵇ φ) = σᵇ⁺ᵃ φ`. -/
theorem sigN_sigN : ∀ (a b : Nat) (φ : PLLFormula), sigN a (sigN b φ) = sigN (b + a) φ
  | 0, _, _ => rfl
  | a + 1, b, φ => by
      show sigN a (sig (sigN b φ)) = sigN (b + a) (sig φ)
      rw [sig_sigN]
      exact sigN_sigN a b (sig φ)

/-- `σᵏ (σᵐ⊥) = σᵐ⁺ᵏ⊥`. -/
theorem sigN_base (k m : Nat) : sigN k (base m) = base (m + k) := sigN_sigN k m _

/-- **PROVED: every base `σᵐ⊥`, `m ≥ 3`, carries every finite free copy.** -/
theorem freeHAnAbove_base_ge3 (m : Nat) (hm : 3 ≤ m) (n : Nat) : FreeHAnAbove (base m) n := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 3 + k := ⟨m - 3, by omega⟩
  rw [← sigN_base]
  exact freeHAnAbove_sigN b3_vf k n (freeHAnAbove_base3 n)

/-- **PROVED: every base `σᵐ⊥`, `m ≥ 3`, carries the free copy on every variable.** -/
theorem freeHAωAbove_base_ge3 (m : Nat) (hm : 3 ≤ m) : FreeHAωAbove (base m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 3 + k := ⟨m - 3, by omega⟩
  rw [← sigN_base]
  exact freeHAωAbove_sigN b3_vf k freeHAωAbove_base3

theorem allAbove3 : AllAbove3 := freeHAnAbove_base_ge3

theorem allAbove3ω : AllAbove3ω := freeHAωAbove_base_ge3

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
#axioms_within PLLND.F0.AnyFamily.genC_vf [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.b3_le_genC [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.b3_le_genC_sem [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.xC_pvar [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.cone_b3 [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.turn [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.not_turn [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.orient [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.sep_box [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.disj_sep [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.choose_vf [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.sum_force [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.GadU.Le.trans [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.GadU.uforce [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.GadU.w_not_b3 [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.GadU.w_back [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.GadU.w_gen0 [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.GadU.w_gen_false [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.GadU.w_gen_true [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.dw_cone_b3 [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.hypF [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.transferF [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.freeHAn_of_seps [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.fromCells3 [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.TkN_ok [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.bmax_of_B [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.kNcell [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.kN_box [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.kS_box [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.ext_S [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.ext_N [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.bsearch [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.skip2_props [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.famK_sep [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.anyFamily3 [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.freeHAnAbove_base3_of_distinct [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.freeHAnAbove_base3' [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.sig_relB [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.sigN_relB [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.relB_vf [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.freeHAnAbove_sigN [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.freeHAωAbove_sigN [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.sigShift [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.sigShiftω [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.sig_sigN [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.sigN_sigN [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.sigN_base [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.freeHAnAbove_base_ge3 [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.freeHAωAbove_base_ge3 [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.allAbove3 [propext, Quot.sound]
#axioms_within PLLND.F0.AnyFamily.allAbove3ω [propext, Quot.sound]
