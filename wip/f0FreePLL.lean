import wip.f0FreeBase3
import Meta.Audit

/-!
# PLL embeds faithfully into its closed fragment (readers only, `◯` kept)

Follow-up to `wip/f0FreeBase3.lean` (2026-10-28; conjecture approved by
Matthew the same day).  There the generators `x₀ = ◯σ³⊥` and the readers
`x_{r+1} = gen (r+1)` freely generate the free Heyting algebra above
`σ³⊥ = base 3`, for ◯-free formulas.  Here `x₀` is dropped and only the
readers are used; the claim is that the relativisation is then faithful on
ALL formulas, `◯` included, with `◯ ↦ ◯`.

## The statement (committed before any proof, METHOD.md §1)

    y a = gen (code a + 1)                                         (`xr`)
    g = relB σ³⊥ y :  a ↦ y a,  ⊥ ↦ σ³⊥,  ∧ ∨ ↠ ◯ ↦ themselves

    FreeReaders :      ∀ A B,  [A] ⊢ B  ⟺  [relB σ³⊥ y A] ⊢ relB σ³⊥ y B

    FreePLLAbove b :   ∃ x, (∀ a, x a variable-free) ∧ (∀ a, [b] ⊢ x a) ∧
                          ∀ A B,  [A] ⊢ B  ⟺  [relB b x A] ⊢ relB b x B
    target:            FreePLLAbove (σ³⊥)

    FreePLLnAbove b n : the same with A, B over pvar 0, …, pvar (n-1)

Fragment first (CLAUDE.md rule 8): the ◯-free instance is

    FreeReadersIPC :   ∀ A B ◯-free,  [A] ⊢ B  ⟺  [relB σ³⊥ y A] ⊢ relB σ³⊥ y B

proved by the gadget of `f0FreeBase3` without `x₀` and with the `S` of the
copies arbitrary.

## Why `x₀` must go (pen, the manager)

`x₀` reads `S`-membership on the copy of `K`, and `◯` reads `S` too: in the
`x₀` gadget, `◯x₁` at `w_k` holds iff `k ⊩ p₀ ∨ p₁`, so the range is not
closed under `◯`.  Without `x₀` the copy keeps `K`'s own `S`.

## Refutation stage (CLAUDE.md rule 9: designed cells only)

The atoms with codes `0` and `1` are `""` and `"\x00"` (`a0`, `a1`), so that
`y a0 = gen 1`, `y a1 = gen 2` are small enough to evaluate in the kernel.

    O1 = ◯p → p,    O2 = ◯p ∨ ¬◯p,    O3 = ◯(p ∨ q) → ◯p ∨ ◯q

Status note: `wip/f0FreePLL-STATUS.md`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace FreePLL

open SemUI RNEmbed Sig FreeIPL FreeHAn Pair Base3
open PLLND.LaxInfinite (atomFree)
open SubframeModel.CF (FinDec)

/-! ## The statement -/

/-- **The readers**: `y a = gen (code a + 1)`.  The generator `x₀ = gen 0 = ◯σ³⊥`
of `f0FreeBase3` is not used. -/
def xr (a : String) : PLLFormula := gen (Base3.code a + 1)

/-- **`[b, ⊤]` contains a faithful copy of PLL**: a substitution of
variable-free formulas above `b` for the atoms, `b` for `⊥`, and `◯` for `◯`,
reflects and preserves derivability for ALL formulas. -/
def FreePLLAbove (b : PLLFormula) : Prop :=
  ∃ x : String → PLLFormula, (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [b] (x a)) ∧
    ∀ A B : PLLFormula, (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))

/-- **The `n`-variable form**: formulas over `pvar 0, …, pvar (n-1)`. -/
def FreePLLnAbove (b : PLLFormula) (n : Nat) : Prop :=
  ∃ x : String → PLLFormula, (∀ a, atomFree (x a) = true) ∧ (∀ a, Deriv [b] (x a)) ∧
    ∀ A B : PLLFormula, varsBelow n A = true → varsBelow n B = true →
      (Deriv [A] B ↔ Deriv [relB b x A] (relB b x B))

/-- **FreeReaders**: the readers `xr` give a faithful copy of PLL above `σ³⊥`. -/
def FreeReaders : Prop :=
  ∀ A B : PLLFormula, Deriv [A] B ↔ Deriv [relB b3 xr A] (relB b3 xr B)

/-- **Stage A, the ◯-free fragment**: the readers alone, on ◯-free formulas. -/
def FreeReadersIPC : Prop :=
  ∀ A B : PLLFormula, boxFree A = true → boxFree B = true →
    (Deriv [A] B ↔ Deriv [relB b3 xr A] (relB b3 xr B))

/-! ## The designed cells (Stage B) -/

/-- The atom with code `0`. -/
def a0 : String := ""

/-- The atom with code `1`. -/
def a1 : String := "\x00"

/-- `p`, read by `gen 1`. -/
def pA : PLLFormula := .prop a0

/-- `q`, read by `gen 2`. -/
def qA : PLLFormula := .prop a1

/-- `O1 = ◯p → p`. -/
def O1 : PLLFormula := (PLLFormula.somehow pA).ifThen pA

/-- `O2 = ◯p ∨ ¬◯p`. -/
def O2 : PLLFormula := (PLLFormula.somehow pA).or (negF (PLLFormula.somehow pA))

/-- `O3 = ◯(p ∨ q) → ◯p ∨ ◯q`. -/
def O3 : PLLFormula :=
  (PLLFormula.somehow (pA.or qA)).ifThen ((PLLFormula.somehow pA).or (PLLFormula.somehow qA))

/-! ## The readers are variable-free and lie above `σ³⊥` -/

theorem xr_vf (a : String) : atomFree (xr a) = true := gen_vf _

theorem b3_le_xr (a : String) : Deriv [b3] (xr a) := b3_le_gen _

theorem b3_le_xr_sem (M : SubframeModel) (v : M.W) (a : String) (hv : M.force v b3) :
    M.force v (xr a) := b3_le_gen_sem M v _ hv

/-! ## Stage A: the gadget without `x₀`, the `S` of the copies a parameter

The gadget of `f0FreeBase3` (`Base3.Gad`), with two changes: the copy `w_k`
is in `S` iff `Sw k`, for a parameter `Sw : K → Prop`; and the reader
`ZL (r+1)` sits above `w_k` iff `k` refutes every atom of code `r` (`Dr`).
The `S`-killer (the bottom of `ZL 0`) and the non-`S` killer `kn` sit above
every copy, as before.  Nothing in the readings of the killers and readers
looks at the `S` of a copy, so the lemmas of `Base3.Gad` carry over verbatim
(`zforce` … `w_gen_succ`), for every `Sw`. -/

namespace GadR

open Base3.Gad (Pt Le)

/-- The reading: `Dr 0` is empty (row `0`, the `S`-killer, is above every
copy whatever `D 0` is); `Dr (r+1) k`: `k` refutes every atom of code `r`. -/
def Dr (K : SubframeModel) : Nat → K.W → Prop
  | 0, _ => False
  | r + 1, k => ∀ a, Base3.code a = r → k ∉ K.V a

theorem Dr_down (K : SubframeModel) : ∀ r {j k : K.W}, K.le j k → Dr K r k → Dr K r j
  | 0, _, _, _, h => h
  | _ + 1, _, _, hjk, hk => fun a ha hj => hk a ha (K.hered hjk hj)

/-- `S` of the gadget: the `S` of each cell; `kn ∉ S`; `w_k ∈ S` iff `Sw k`. -/
def SPw (K : SubframeModel) (Sw : K.W → Prop) : Pt K.W → Prop
  | .z r a => a ∈ (ZL.M r).S
  | .kn => False
  | .w k => Sw k

/-- **The readers' gadget `M(K, Sw)`**; no atoms. -/
def MS (K : SubframeModel) (Sw : K.W → Prop) : SubframeModel where
  W := Pt K.W
  le := Le K (Dr K)
  S := SPw K Sw
  V _ := fun _ => False
  refl := Base3.Gad.Le.refl
  trans h₁ h₂ := Base3.Gad.Le.trans (Dr_down K) h₁ h₂
  hered _ h := False.elim h

variable {K : SubframeModel} {Sw : K.W → Prop}

/-- The cells embed as generated submodels. -/
theorem zforce (r : Nat) (φ : PLLFormula) (a : (ZL.M r).W) :
    (MS K Sw).force (Pt.z r a) φ ↔ (ZL.M r).force a φ :=
  force_pmorph (ZL.M r) (MS K Sw) (Pt.z r) (fun h => ⟨rfl, h⟩)
    (fun a v hv => by
      cases v with
      | z r' b =>
        obtain ⟨e, hl⟩ := hv
        subst e
        exact ⟨b, hl, rfl⟩
      | kn => exact False.elim hv
      | w _ => exact False.elim hv)
    (fun _ => Iff.rfl) (fun _ _ => Iff.rfl) φ a

theorem z_b3 (r : Nat) (a : (ZL.M r).W) : (MS K Sw).force (Pt.z r a) b3 :=
  (zforce r b3 a).mpr (Cell.b3_all a)

theorem kS_S : (Pt.z 0 (Cell.bot 0) : (MS K Sw).W) ∈ (MS K Sw).S := Cell.bot_S 0

theorem kS_not_b2 : ¬ (MS K Sw).force (Pt.z 0 (Cell.bot 0)) b2 := fun h =>
  Cell.not_b2_bot 0 ((zforce 0 b2 _).mp h)

theorem kn_succ {v : (MS K Sw).W} (hv : (MS K Sw).le Pt.kn v) :
    v = Pt.kn ∨ ∃ a : (ZL.M 0).W, a.1 < 4 ∧ v = Pt.z 0 a := by
  cases v with
  | z r a =>
    obtain ⟨e, ha⟩ := hv
    subst e
    exact Or.inr ⟨a, ha, rfl⟩
  | kn => exact Or.inl rfl
  | w _ => exact False.elim hv

theorem kn_xf : (MS K Sw).force Pt.kn xf := by
  show ∀ v, (MS K Sw).le Pt.kn v → v ∈ (MS K Sw).S → (MS K Sw).force v Yf
  intro v hv hS
  rcases kn_succ hv with h | ⟨a, ha, h⟩
  · subst h
    exact False.elim hS
  · subst h
    have hS' : a.1 ≠ 0 ∧ a.1 ≠ 0 + 3 := hS
    obtain ⟨_, h3⟩ := hS'
    exact (zforce 0 Yf a).mpr ((ZL.force_Y_iff a.2).mpr (by omega))

theorem kn_not_b2 : ¬ (MS K Sw).force Pt.kn b2 := by
  intro h
  have h' : (MS K Sw).force Pt.kn SigOnto.c1F ∨ (MS K Sw).force Pt.kn SigOnto.g1F := h
  rcases h' with hc | hg
  · have h2 := hc (Pt.z 0 ⟨2, ZL.lt2 0⟩) ⟨rfl, by decide⟩ ⟨by decide, by decide⟩
    exact ZL.not_force_t3 (ZL.lt2 0) (Nat.le_refl 2) ((zforce 0 t3 _).mp h2)
  · have h3 := hg (Pt.z 0 ⟨3, ZL.lt3 0⟩) ⟨rfl, by decide⟩
      ((zforce 0 _ _).mpr (ZL.force_c1_f (ZL.lt3 0)))
    exact ZL.not_force_t3 (ZL.lt3 0) (by decide) ((zforce 0 t3 _).mp h3)

theorem kn_c2 : (MS K Sw).force Pt.kn (.somehow b2) := by
  show ∀ v, (MS K Sw).le Pt.kn v → v ∈ (MS K Sw).S → (MS K Sw).force v b2
  intro v hv hS
  rcases kn_succ hv with h | ⟨a, ha, h⟩
  · subst h
    exact False.elim hS
  · subst h
    exact (zforce 0 b2 a).mpr (Cell.b2_of_ne a (by omega))

theorem kn_b3 : (MS K Sw).force Pt.kn b3 := Or.inl kn_c2

theorem kn_sep (s : Nat) : (MS K Sw).force Pt.kn (sepC s) :=
  Or.inl (force_phiK_of_xf _ _ kn_xf (s + 1))

/-- **`w_k ⊮ σ³⊥`**, whatever `Sw`: `◯σ²⊥` fails by the `S`-killer,
`◯σ²⊥ ↠ σ²⊥` by `kn`. -/
theorem w_not_b3 (k : K.W) : ¬ (MS K Sw).force (Pt.w k) b3 := by
  intro h
  have h' : (MS K Sw).force (Pt.w k) (PLLFormula.somehow b2) ∨
      (MS K Sw).force (Pt.w k) ((PLLFormula.somehow b2).ifThen b2) := h
  rcases h' with hc | hg
  · exact kS_not_b2 (hc (Pt.z 0 (Cell.bot 0)) trivial kS_S)
  · exact kn_not_b2 (hg Pt.kn trivial kn_c2)

/-- The back condition: every successor of `w_k` forces `σ³⊥` or is a `w_j`, `j ≥ k`. -/
theorem w_back (k : K.W) (v : (MS K Sw).W) (hv : (MS K Sw).le (Pt.w k) v) :
    (MS K Sw).force v b3 ∨ ∃ j, K.le k j ∧ Pt.w j = v := by
  cases v with
  | z r a => exact Or.inl (z_b3 r a)
  | kn => exact Or.inl kn_b3
  | w j => exact Or.inr ⟨j, hv, rfl⟩

/-- **`x_{s+1}` reads `¬ Dr (s+1)`**, whatever `Sw`. -/
theorem w_gen_succ (k : K.W) (s : Nat) :
    (MS K Sw).force (Pt.w k) (gen (s + 1)) ↔ ¬ Dr K (s + 1) k := by
  constructor
  · intro hx hk
    rcases hx with hb | himp
    · exact w_not_b3 k hb
    · have hr : (MS K Sw).force (Pt.z (s + 1) (Cell.bot (s + 1))) ((sepC (s + 1)).ifThen b2) :=
        (zforce (s + 1) _ _).mpr (Cell.sepimp_bot (s + 1))
      exact Cell.not_b2_bot (s + 1) ((zforce (s + 1) b2 _).mp (himp _ hk hr))
  · intro hk
    refine Or.inr ?_
    show ∀ v, (MS K Sw).le (Pt.w k) v → (MS K Sw).force v ((sepC (s + 1)).ifThen b2) →
      (MS K Sw).force v b2
    intro v hv hsep
    cases v with
    | z r a =>
      rcases Decidable.em (a.1 = r + 4) with h4 | h4
      · have ha : a = Cell.bot r := Cell.eq_bot h4
        subst ha
        rcases Decidable.em (r = s + 1) with hr | hr
        · subst hr
          exact absurd hv hk
        · exact hsep _ ((MS K Sw).refl _) ((zforce r _ _).mpr (Cell.sep_bot hr))
      · exact (zforce r b2 a).mpr (Cell.b2_of_ne a h4)
    | kn => exact hsep _ ((MS K Sw).refl _) (kn_sep (s + 1))
    | w j => exact absurd (hsep Pt.kn trivial (kn_sep (s + 1))) kn_not_b2

/-- **The readers read the valuation**: `w_k ⊩ xr a ⟺ k ⊩ a`, whatever `Sw`. -/
theorem w_read [FinDec K] (k : K.W) (a : String) :
    (MS K Sw).force (Pt.w k) (xr a) ↔ k ∈ K.V a := by
  refine (w_gen_succ k (Base3.code a)).trans ⟨fun hn => ?_, fun hk hD => hD a rfl hk⟩
  exact Decidable.byContradiction fun hk => hn fun a' ha' hk' => by
    have e : a' = a := Base3.code_inj ha'
    subst e
    exact hk hk'

/-- **The ◯-free gadget transfer**, for every `S` on the copies:
`w_k ⊩ relB σ³⊥ xr A ⟺ k ⊩ A` for ◯-free `A`. -/
theorem transferIPC [FinDec K] : ∀ A : PLLFormula, boxFree A = true →
    ∀ k : K.W, ((MS K Sw).force (Pt.w k) (relB b3 xr A) ↔ K.force k A) :=
  relB_transferω (MS K Sw) b3 xr K Pt.w (fun v _ hv => b3_le_xr_sem _ v _ hv)
    w_not_b3 (fun h => h) w_back w_read

end GadR

/-- **Stage A, direction `⟸`**, by the gadget (here with no copy in `S`). -/
theorem freeReadersIPC_reflects {A B : PLLFormula} (hA : boxFree A = true)
    (hB : boxFree B = true) (hd : Deriv [relB b3 xr A] (relB b3 xr B)) : Deriv [A] B := by
  obtain ⟨d⟩ := hd
  have hsem : ∀ (K : SubframeModel) [FinDec K] (k : K.W), K.force k A → K.force k B := by
    intro K _ k hk
    exact (GadR.transferIPC (Sw := fun _ => False) B hB k).mp
      (SubframeModel.CF.soundness₁ d (GadR.MS K fun _ => False) (Base3.Gad.Pt.w k)
        ((GadR.transferIPC (Sw := fun _ => False) A hA k).mpr hk))
  have h2 : Deriv [] (A.ifThen B) := SubframeModel.CF.completeness_imp hsem
  exact Deriv.impElim (h2.rename fun _ h => absurd h List.not_mem_nil) (Deriv.iden (.head _))

/-- **PROVED: `FreeReadersIPC`** (Stage A, the ◯-free fragment). -/
theorem freeReadersIPC : FreeReadersIPC := fun _ _ hA hB =>
  ⟨relB_preservesω b3 xr (fun M v _ hv => b3_le_xr_sem M v _ hv) hA hB,
   freeReadersIPC_reflects hA hB⟩

/-! ## Stage B: the designed cells (refutation stage, CLAUDE.md rules 7 and 9)

Three PLL non-theorems in which `◯` does the work,

    O1 = ◯p → p,    O2 = ◯p ∨ ¬◯p,    O3 = ◯(p ∨ q) → ◯p ∨ ◯q,

with `p = a0`, `q = a1` (codes `0`, `1`, read by `gen 1`, `gen 2`).  Each has
a designed subframe countermodel `K1`, `K2`, `K3` (`pll_O1` … `pll_O3`).
Freeness needs each image `relB σ³⊥ xr Oᵢ` to be no theorem of PLL; the
readers' gadget over `Kᵢ`, written as a table by `gadT` (the upper worlds
`0 … 9` of `f0FreeBase3`'s tables, `e₀ n₀ L₀ L₁ L₂ f m₀ m₁ m₂ kn`, then one
copy `10 + i` of each world `i` of `Kᵢ`, in `S` iff `i` is), refutes it at
the copy of the root (`cell_O1` … `cell_O3`).  The base facts of
`f0FreeBase3` (`baseFacts`) hold on each table, and the readers read the
valuation at every copy (`readsB`).  All by `decide +kernel`. -/

set_option maxRecDepth 100000

/-- `K1`: one world, not in `S`, no atoms (`◯p` holds vacuously, `p` fails). -/
def K1 : SubTab.SubCM := { n := 1, root := 0, le := [[true]], S := [false], val := [[]] }

/-- `K2`: `k₀ ∈ S` below `k₁ ∉ S`, no atoms (`k₀ ⊮ ◯p`; `k₁ ⊩ ◯p`, so `k₀ ⊮ ¬◯p`). -/
def K2 : SubTab.SubCM :=
  { n := 2, root := 0, le := [[true, true], [false, true]], S := [true, false], val := [[], []] }

/-- `K3`: `k₀ ∉ S` below two `S`-tops, `p` at `k₁`, `q` at `k₂`. -/
def K3 : SubTab.SubCM :=
  { n := 3, root := 0, le := [[true, true, true], [false, true, false], [false, false, true]],
    S := [false, true, true], val := [[], [a0], [a1]] }

/-- PLL: `⊬ ◯p → p`. -/
theorem pll_O1 : ¬ Deriv [] O1 := SubTab.no.verdict O1 K1

/-- PLL: `⊬ ◯p ∨ ¬◯p`. -/
theorem pll_O2 : ¬ Deriv [] O2 := SubTab.no.verdict O2 K2

/-- PLL: `⊬ ◯(p ∨ q) → ◯p ∨ ◯q`. -/
theorem pll_O3 : ¬ Deriv [] O3 := SubTab.no.verdict O3 K3

/-- The order rows of the upper worlds `0 … 9` (`e₀ n₀ L₀ L₁ L₂ f m₀ m₁ m₂ kn`),
as in `f0FreeBase3`'s tables. -/
def upLe : List (List Bool) :=
  [[true, false, false, false, false, false, false, false, false, false],
   [false, true, false, false, false, false, false, false, false, false],
   [true, false, true, false, false, false, false, false, false, false],
   [true, true, false, true, false, false, false, false, false, false],
   [true, true, true, false, true, false, false, false, false, false],
   [true, true, false, false, false, true, false, false, false, false],
   [true, true, true, false, false, true, true, false, false, false],
   [true, true, true, true, false, true, false, true, false, false],
   [true, true, true, true, true, true, false, false, true, false],
   [true, true, true, false, false, true, false, false, false, true]]

/-- `S` on the upper worlds. -/
def upS : List Bool := [false, true, true, true, true, false, true, true, true, false]

/-- **The readers' gadget over a table `K`** (readers `m₁` for `a0`, `m₂` for
`a1`): the copy `10 + i` of `i` is in `S` iff `i` is; it sees `e₀ n₀ L₀ f m₀ kn`
always, `m₁` (and `L₁`) iff `i ⊮ a0`, `m₂` (and `L₁ L₂`) iff `i ⊮ a1`, and the
copies of the successors of `i`. -/
def gadT (K : SubTab.SubCM) : SubTab.SubCM :=
  { n := 10 + K.n, root := 10 + K.root,
    le := upLe.map (· ++ List.replicate K.n false) ++
      (List.range K.n).map fun i =>
        [true, true, true, !(K.vB a0 i) || !(K.vB a1 i), !(K.vB a1 i), true, true,
          !(K.vB a0 i), !(K.vB a1 i), true] ++ (List.range K.n).map fun j => K.leB i j,
    S := upS ++ (List.range K.n).map K.SB,
    val := List.replicate (10 + K.n) [] }

/-- The readers read the valuation at every copy, and the copies carry `K`'s `S`. -/
def readsB (K : SubTab.SubCM) : Bool :=
  (List.range K.n).all fun i =>
    ((gadT K).forceB (10 + i) (xr a0) == K.vB a0 i) &&
    ((gadT K).forceB (10 + i) (xr a1) == K.vB a1 i) &&
    ((gadT K).SB (10 + i) == K.SB i)

theorem baseFacts_K1 : baseFacts (gadT K1) = true := by decide +kernel

theorem baseFacts_K2 : baseFacts (gadT K2) = true := by decide +kernel

theorem baseFacts_K3 : baseFacts (gadT K3) = true := by decide +kernel

theorem reads_K1 : readsB K1 = true := by decide +kernel

theorem reads_K2 : readsB K2 = true := by decide +kernel

theorem reads_K3 : readsB K3 = true := by decide +kernel

/-- **Cell O1 PASSES**: `⊬ ◯y₀ ↠ y₀`, `y₀ = xr a0 = gen 1`. -/
theorem cell_O1 : ¬ Deriv [] (relB b3 xr O1) := SubTab.no.verdict (relB b3 xr O1) (gadT K1)

/-- **Cell O2 PASSES**: `⊬ ◯y₀ ∨ (◯y₀ ↠ σ³⊥)`. -/
theorem cell_O2 : ¬ Deriv [] (relB b3 xr O2) := SubTab.no.verdict (relB b3 xr O2) (gadT K2)

/-- **Cell O3 PASSES**: `⊬ ◯(y₀ ∨ y₁) ↠ ◯y₀ ∨ ◯y₁`, `y₁ = xr a1 = gen 2`. -/
theorem cell_O3 : ¬ Deriv [] (relB b3 xr O3) := SubTab.no.verdict (relB b3 xr O3) (gadT K3)

end FreePLL
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.FreePLL.xr_vf [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.b3_le_xr [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.GadR.zforce [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.GadR.kn_xf [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.GadR.kn_not_b2 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.GadR.w_not_b3 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.GadR.w_gen_succ [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.GadR.w_read [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.GadR.transferIPC [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.freeReadersIPC_reflects [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.freeReadersIPC [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.pll_O1 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.pll_O2 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.pll_O3 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.baseFacts_K1 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.baseFacts_K2 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.baseFacts_K3 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.reads_K1 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.reads_K2 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.reads_K3 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.cell_O1 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.cell_O2 [propext, Quot.sound]
#axioms_within PLLND.F0.FreePLL.cell_O3 [propext, Quot.sound]
