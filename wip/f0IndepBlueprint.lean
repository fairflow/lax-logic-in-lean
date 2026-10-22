import wip.gapWidth
import Meta.Audit

/-!
# Independence of the odd gaps: the multi-edge lift (blueprint, B2)

**Status.**  `multi_edge_forcing` is OPEN.  Its `sorry` is a statement for
review, written by direction of the LaxLogic manager (2026-10-22); it is not
a claim.  Everything else in this file is sorry-free and pinned.

## The conjecture

With `g k = gap k = ◯t(2k+1) ↠ t(2k+1)` (`wip/gapWidth.lean`),

    Indep:  for all finite disjoint S, T ⊆ ℕ,   ⋀_{i∈S} g(2i+1)  ⊬  ⋁_{j∈T} g(2j+1)

(`Indep`; `⋀[] = ⊤`, `⋁[] = ⊥`).  If it holds, the odd gaps generate a free
distributive lattice on ω generators inside F0, which is dense, so ℚ embeds
in F0.  The case `|T| = 1` is PROVED (`odd_gaps_single`,
`wip/f0OddGaps.lean`); the open content is `|T| ≥ 2`: one world must refute
several gaps at once and still force the gaps of `S`.

## The design

`cmE m` (`wip/chainOff.lean`) is the abyss-lifted Rieger–Nishimura ladder with
one internal `Rₘ`-edge `(m+3) ⇝ 0`; at the edge world it refutes exactly
`g(m+1)` and `g(m+2)` and forces every other gap (`gap_fails`, `gap_forced`).
`cmM ms` has one such edge for every level `m ∈ ms`: the edge worlds are
`E = {m+3 : m ∈ ms}`, each with `e ⇝ 0` and `e ⇝ ⊤` (the fallible top).
Same skeleton (`riL ladder`), same fallible top, same valuation.

For a finite `T`, the levels are `2j` for `j ∈ T` (`levels T`), so
`E = {2j+3 : j ∈ T}`, and the root is the highest edge world,
`root T = 2·max T + 3`.

**The forcing lemma** (`MultiEdgeForcing`, OPEN):

    ∀ T,  (∀ i ∉ T, ∀ x,  cmM (levels T), x ⊩ g(2i+1))
        ∧ (∀ j ∈ T,       cmM (levels T), root T ⊮ g(2j+1)).

**The reduction** (`indep_of_forcing`, PROVED): `MultiEdgeForcing → Indep`,
by soundness at the root (the conjuncts of `S` are forced since `S ∩ T = ∅`,
and a disjunction is forced at a non-fallible world only through a disjunct).

## Why the forcing lemma should hold (pen argument, not checked)

1. The edges sit at worlds `≥ 3`, so `T(◯⊥)` on the skeleton is still `{0}`
   (world `1` is in the cone of every world `≥ 3`, and `1`, `2` are not
   edges), and the substituted rungs keep their ladder truth sets
   (as `cmE_force_oBot`, `cmE_transfer`): `T(t(2k+1)) = [0, k]`.
2. `◯N` holds at `x` iff every `y` in the cone of `x` is `0`, an edge world,
   or forces `N`.  The cone of `x` is `{x} ∪ [0, x−2]`, so
   `T(◯t(2k+1)) = {x : cone(x) ⊆ [0, k] ∪ E}`.
3. Hence `g k` fails at `w` iff some `v` in the cone of `w` has
   `v ∈ E`, `v > k` and `[k+1, v−2] ⊆ E`.
4. For `k = 2i+1`: `E` consists of odd numbers, so `[2i+2, v−2] ⊆ E` forces
   `v − 2 < 2i + 2`, i.e. `v = 2i+3`.  So `g(2i+1)` fails somewhere iff
   `2i+3 ∈ E` iff `i ∈ T`.  For `i ∉ T` it is forced at every world; for
   `j ∈ T` it fails at every world whose cone contains `2j+3`, in particular
   at the root (the edge worlds are odd and `≤ root T`, so they lie in
   `{root T} ∪ [0, root T − 2]`).

The even gaps `g(2j+2)` also fail at the root; they play no part.  With
`T = [j]` the lift is `cmE (2j)` up to the form of the `Rₘ` clause, and the
lemma is `gap_fails` with `gap_forced` (`odd_gaps_single`).

## Validation on the designed cells (B1, 2026-10-22)

The truncation of `cmM (levels T)` to the cone of its root, written as a
`FRJ.Search.Tab` in the format of `pll`/`pllfast` and kernel-checked by the
same certificate path, refutes both `|T| = 2` cells of B1
(`wip/f0IndepCells.lean`, pins `[propext, Quot.sound]`):

* `g3 ⊬ g1 ∨ g5`  (`S = {1}`, `T = {0, 2}`, edges `{3, 7}`, root `7`,
  7 skeleton worlds + top): `cellA_refuted`;
* `g1 ∧ g3 ⊬ g5 ∨ g7`  (`S = {0, 1}`, `T = {2, 3}`, edges `{7, 9}`, root `9`,
  9 skeleton worlds + top): `cellB_refuted`.

These are instances of the forcing lemma checked on finite models; they are
evidence for the design, not a proof of the lemma.
-/

open PLLFormula

namespace PLLND
namespace F0

open SemUI RNEmbed

/-! ## The conjecture -/

/-- **Indep**: for all finite disjoint `S`, `T`,
`⋀_{i∈S} g(2i+1) ⊬ ⋁_{j∈T} g(2j+1)`. -/
def Indep : Prop :=
  ∀ S T : List Nat, (∀ i ∈ S, i ∉ T) →
    [bigAnd (S.map fun i => gap (2 * i + 1))] ⊬
      PLLND.bigOr (T.map fun j => gap (2 * j + 1))

/-! ## The multi-edge lift -/

/-- `v` is an edge world: `v = m + 3` for a level `m ∈ ms`. -/
def IsEdge (ms : List Nat) (v : Nat) : Prop := ∃ m ∈ ms, v = m + 3

theorem not_isEdge_zero {ms : List Nat} : ¬ IsEdge ms 0 :=
  fun ⟨m, _, h⟩ => Nat.succ_ne_zero (m + 2) h.symm

/-- `Rₘ` with one internal edge `e ⇝ 0` per edge world `e` (and `e ⇝ ⊤`,
for transitivity through `0 ⇝ ⊤`). -/
def RmM (ms : List Nat) : Option Nat → Option Nat → Prop
  | some v, some w => v = w ∨ (IsEdge ms v ∧ w = 0)
  | some v, none   => v = 0 ∨ IsEdge ms v
  | none,   none   => True
  | none,   some _ => False

/-- **The multi-edge lift** of the ladder: the edges of `cmE m` for every
level `m ∈ ms` at once. -/
@[reducible] def cmM (ms : List Nat) : ConstraintModel where
  W := Option Nat
  Ri := riL ladder
  Rm := RmM ms
  F := {x | x = none}
  V _ := {x | x = none}
  refl_i x := by
    cases x with
    | none => exact trivial
    | some a => exact ladder.refl a
  trans_i {x y z} h1 h2 := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h1 : False).elim
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
    | some a =>
        cases y with
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
        | some b =>
            cases z with
            | none => exact trivial
            | some c => exact ladder.trans h1 h2
  refl_m x := by
    cases x with
    | none => exact trivial
    | some a => exact Or.inl rfl
  trans_m {x y z} h1 h2 := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h1 : False).elim
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
    | some a =>
        cases y with
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact h1
        | some b =>
            cases z with
            | none =>
                rcases (h1 : a = b ∨ (IsEdge ms a ∧ b = 0)) with rfl | ⟨ha, _⟩
                · exact h2
                · exact Or.inr ha
            | some c =>
                rcases (h1 : a = b ∨ (IsEdge ms a ∧ b = 0)) with rfl | ⟨ha, rfl⟩
                · exact h2
                · rcases (h2 : (0 : Nat) = c ∨ (IsEdge ms 0 ∧ c = 0)) with rfl | ⟨h0, _⟩
                  · exact Or.inr ⟨ha, rfl⟩
                  · exact (not_isEdge_zero h0).elim
  sub_mi {x y} h := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h : False).elim
        | none => exact trivial
    | some a =>
        cases y with
        | none => exact trivial
        | some b =>
            rcases (h : a = b ∨ (IsEdge ms a ∧ b = 0)) with rfl | ⟨⟨m, _, rfl⟩, rfl⟩
            · exact ladder.refl a
            · exact Or.inr (Nat.le_add_left 2 (m + 1))
  hered_F {x y} h hx := by
    obtain rfl := (hx : x = none)
    cases y with
    | some b => exact (h : False).elim
    | none => exact rfl
  hered_V {a x y} h hx := by
    obtain rfl := (hx : x = none)
    cases y with
    | some b => exact (h : False).elim
    | none => exact rfl
  full_F {a x} hx := hx

/-- The levels for an index set `T`: one edge, at world `2j+3`, per `j ∈ T`. -/
def levels (T : List Nat) : List Nat := T.map (2 * ·)

/-- The root: the highest edge world, `2·max T + 3`. -/
def root (T : List Nat) : Nat := 2 * T.foldr max 0 + 3

/-! ## The forcing lemma (OPEN) -/

/-- **The general forcing lemma**, as a statement: on `cmM (levels T)`, every
odd gap with index outside `T` is forced at every skeleton world, and every
odd gap with index in `T` fails at the root. -/
def MultiEdgeForcing : Prop :=
  ∀ T : List Nat,
    (∀ i : Nat, i ∉ T → ∀ x : Nat, (cmM (levels T)).force (some x) (gap (2 * i + 1))) ∧
    (∀ j ∈ T, ¬ (cmM (levels T)).force (some (root T)) (gap (2 * j + 1)))

/-- **BLUEPRINT — OPEN.**  The forcing lemma.  Statement for review only, by
direction (2026-10-22); the proof is not attempted here.  Pen argument in the
module header. -/
theorem multi_edge_forcing : MultiEdgeForcing := by
  sorry

/-! ## The reduction (PROVED) -/

/-- A finite disjunction is forced at a skeleton world only through one of its
disjuncts (`⋁[] = ⊥` is forced only at the fallible top). -/
theorem cmM_force_bigOr (ms : List Nat) (x : Nat) :
    ∀ L : List PLLFormula, (cmM ms).force (some x) (PLLND.bigOr L) →
      ∃ φ ∈ L, (cmM ms).force (some x) φ
  | [], h => absurd (h : (some x : Option Nat) = none) (Option.some_ne_none x)
  | φ :: L, h => by
      rcases (h : (cmM ms).force (some x) φ ∨ (cmM ms).force (some x) (PLLND.bigOr L))
        with h | h
      · exact ⟨φ, List.mem_cons_self .., h⟩
      · obtain ⟨ψ, hψ, h'⟩ := cmM_force_bigOr ms x L h
        exact ⟨ψ, List.mem_cons_of_mem _ hψ, h'⟩

/-- **The forcing lemma implies independence**: soundness at the root. -/
theorem indep_of_forcing (H : MultiEdgeForcing) : Indep := by
  intro S T hST hd
  have hctx : Deriv (S.map fun i => gap (2 * i + 1))
      (PLLND.bigOr (T.map fun j => gap (2 * j + 1))) :=
    Deriv.cutHead (Deriv.bigAndIntro fun _ hD => Deriv.iden hD) hd
  obtain ⟨d⟩ := hctx
  obtain ⟨hS, hT⟩ := H T
  have hs := soundness d (cmM (levels T)) (some (root T)) (fun ψ hψ => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hψ
    exact hS i (hST i hi) (root T))
  obtain ⟨φ, hφ, hf⟩ := cmM_force_bigOr _ _ _ hs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hφ
  exact hT j hj hf

end F0
end PLLND

#axioms_within PLLND.F0.cmM [propext, Quot.sound]
#axioms_within PLLND.F0.cmM_force_bigOr [propext, Quot.sound]
#axioms_within PLLND.F0.indep_of_forcing [propext, Quot.sound]
-- The blueprint statement: its `sorry` is explicit here (TOOLS.md §6); the
-- other two axioms come from the frame-law proofs inside `cmM`.
#axioms_within PLLND.F0.multi_edge_forcing [propext, sorryAx, Quot.sound]
