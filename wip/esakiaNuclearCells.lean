import wip.esakiaNuclearFin

/-!
# Nuclear Esakia duality, finite case: the designed cells (round 1)

The refutation stage for the statements of `wip/esakiaNuclearFin.lean`
(CLAUDE.md rules 7 and 9): three designed cells, each checking BOTH
directions of the correspondence,

* algebra → dual → algebra: `(A, j) ↦ (X_A, S_j) ↦ (Up(X_A), j_{S_j}) ≅ (A, j)`
  (F1, F4, F6, F7, F8, F9);
* poset → algebra → poset: `(X, S) ↦ (Up(X), j_S) ↦ (X_{Up(X)}, S_{j_S}) ≅ (X, S)`
  (F2, F3, F5);

plus two morphism cells (F10a, F10) and the negative gates.  Every fact is
a closed instance of a statement, decided by the kernel (`decide +kernel`),
choice-free.

| cell | algebra `A` | poset `X` | nuclei tested |
|---|---|---|---|
| C0 | the 1-element algebra (boundary) | the empty poset | the only one |
| C1 | the 3-element chain `C₃` | the 2-chain | all 4 (exhaustive over the 27 self-maps) |
| C2 | the Boolean algebra `2²` | the 2-antichain | all 4 (exhaustive over the 256 self-maps) |
| C3 | `RN₈`, the 8-element Rieger–Nishimura truncation | the 4-point RN ladder | designed: `u_p, v_p, w_p, w_⊥ = ¬¬, u_p ∧ ¬¬`; and all 16 via F6 |

Why these: `C₃` is the smallest algebra on which the ORIENTATION of `↓` in
`j_S(U) = X ∖ ↓(S ∖ U)` and of `⊑` matters (the gate G1 below fails there);
`2²` is the smallest with two incomparable meet-primes, and every nucleus
on a Boolean algebra is closed (`j x = j ⊥ ∨ x`), checked as a control;
`RN₈` has a non-linear, non-discrete dual (the ladder), the first place
where `max` in [BG] Thm 34 (`S_{w_a} = max(X ∖ α(a))`) differs from
`X ∖ α(a)` on a non-maximal point (gate G2).
-/

namespace EsakiaNuclear.Cells

open EsakiaNuclear

/-! ## The algebras and posets -/

/-- The 3-element chain `0 < 1 < 2`. -/
def chain3 : FinHA := FinHA.ofOrd ⟨3, fun a b => Nat.ble a b⟩

/-- The 2-element chain, as an algebra (for the morphism cells). -/
def two : FinHA := FinHA.ofOrd ⟨2, fun a b => Nat.ble a b⟩

/-- The Boolean algebra `2²`: `0 = ⊥ < 1, 2 < 3 = ⊤`. -/
def bool4 : FinHA := FinHA.ofOrd ⟨4, fun a b => a == 0 || b == 3 || a == b⟩

/-- Up-sets of the elements of `RN₈`, listing everything above each one.
The elements, named by the one-variable formulas they interpret:
`0 = ⊥, 1 = p, 2 = ¬p, 3 = p ∨ ¬p, 4 = ¬¬p, 5 = ¬¬p ∨ ¬p, 6 = ¬¬p → p,
7 = ⊤`, the bottom of the Rieger–Nishimura lattice with everything above
`¬¬p ∨ ¬p` and `¬¬p → p` collapsed to `⊤`.  Given as an abstract order; its
dual is computed, and checked against the ladder below
(`rn8_dual_iso_ladder4`). -/
def rn8Above : Nat → List Nat
  | 0 => [0, 1, 2, 3, 4, 5, 6, 7]
  | 1 => [1, 3, 4, 5, 6, 7]
  | 2 => [2, 3, 5, 6, 7]
  | 3 => [3, 5, 6, 7]
  | 4 => [4, 5, 7]
  | 5 => [5, 7]
  | 6 => [6, 7]
  | _ => [7]

/-- `RN₈` as a finite Heyting algebra. -/
def rn8 : FinHA := FinHA.ofOrd ⟨8, fun a b => (rn8Above a).contains b⟩

/-- The 2-chain `0 < 1`. -/
def chain2 : FinOrd := ⟨2, fun x y => Nat.ble x y⟩

/-- The 2-antichain. -/
def anti2 : FinOrd := ⟨2, fun x y => x == y⟩

/-- The first four points of the Rieger–Nishimura ladder, in the library's
order `PLLND.rnLe x y :⟺ y = x ∨ y + 1 < x` (`LaxLogic/PLL/Semantics/
LaxInfinite.lean`): `2 ≤ 0`, `3 ≤ 0`, `3 ≤ 1`. -/
def ladder4 : FinOrd := ⟨4, fun x y => x == y || Nat.blt (y + 1) x⟩

/-- The nuclei on `H` among all self-maps of its carrier, as tables. -/
def nucleiOf (H : FinHA) : List (List Nat) :=
  (allTables H.ord.n).filter fun t => H.isNucleus (tab t)

/-! ## Well-formedness of the cells -/

theorem chain3_isHA : chain3.isHA = true := by decide +kernel
theorem two_isHA : two.isHA = true := by decide +kernel
theorem bool4_isHA : bool4.isHA = true := by decide +kernel
theorem rn8_isHA : rn8.isHA = true := by decide +kernel
theorem chain2_isPoset : chain2.isPoset = true := by decide +kernel
theorem anti2_isPoset : anti2.isPoset = true := by decide +kernel
theorem ladder4_isPoset : ladder4.isPoset = true := by decide +kernel

/-- The computed dual of `RN₈` is the 4-point ladder, by `0 ↦ 0, 1 ↦ 1,
2 ↦ 3, 3 ↦ 2` (the meet-primes are `¬p, ¬¬p, ¬¬p ∨ ¬p, ¬¬p → p`). -/
theorem rn8_dual_iso_ladder4 :
    rn8.mprimes = [2, 4, 5, 6] ∧
    ∀ i ∈ List.range 4, ∀ k ∈ List.range 4,
      rn8.dual.le i k = ladder4.le ([0, 1, 3, 2].getD i 0) ([0, 1, 3, 2].getD k 0) := by
  decide +kernel

/-! ## C0: the boundary cell, the one-element algebra and the empty poset -/

/-- The one-element (degenerate) Heyting algebra, `⊤ = ⊥`. -/
def one : FinHA := FinHA.ofOrd ⟨1, fun _ _ => true⟩

/-- The empty poset. -/
def empty0 : FinOrd := ⟨0, fun _ _ => true⟩

theorem one_isHA : one.isHA = true := by decide +kernel
/-- The dual of the degenerate algebra is empty, and it has one nucleus. -/
theorem c0_dual : one.mprimes = [] ∧ nucleiOf one = [[0]] := by decide +kernel
theorem c0_F1 : AlphaIso one := by decide +kernel
theorem c0_F2 : EpsIso empty0 := by decide +kernel
theorem c0_F4 : ∀ t ∈ nucleiOf one, Rep one (tab t) := by decide +kernel
theorem c0_F6 : ∀ S ∈ allSubs one.mprimes.length, Bij one S := by decide +kernel
theorem c0_F3 : ∀ S ∈ allSubs 0, JSNucleus empty0 S := by decide +kernel
theorem c0_F5 : ∀ S ∈ allSubs 0, EpsS empty0 S := by decide +kernel

/-! ## C1: the 3-element chain -/

/-- F1 at `C₃` (◯-free). -/
theorem c1_F1 : AlphaIso chain3 := by decide +kernel
/-- F2 at the 2-chain (◯-free). -/
theorem c1_F2 : EpsIso chain2 := by decide +kernel
/-- Exactly 4 of the 27 self-maps of `C₃` are nuclei (`2^|X_{C₃}|`). -/
theorem c1_nuclei : nucleiOf chain3 = [[0, 1, 2], [1, 1, 2], [0, 2, 2], [2, 2, 2]] := by
  decide +kernel
/-- F4 at `C₃`, every nucleus. -/
theorem c1_F4 : ∀ t ∈ nucleiOf chain3, Rep chain3 (tab t) := by decide +kernel
/-- F6 at `C₃`, every subset of `X_{C₃}`. -/
theorem c1_F6 : ∀ S ∈ allSubs chain3.mprimes.length, Bij chain3 S := by decide +kernel
/-- F7 at `C₃`, every pair of nuclei. -/
theorem c1_F7 : ∀ t ∈ nucleiOf chain3, ∀ t' ∈ nucleiOf chain3,
    OrdRev chain3 (tab t) (tab t') := by decide +kernel
/-- F8 at `C₃`, every pair of nuclei. -/
theorem c1_F8 : ∀ t ∈ nucleiOf chain3, ∀ t' ∈ nucleiOf chain3,
    MeetUnion chain3 (tab t) (tab t') := by decide +kernel
/-- F9 at `C₃`, every element. -/
theorem c1_F9 : ∀ a ∈ chain3.pts, Thm34 chain3 a := by decide +kernel
/-- F3 at the 2-chain, every subset. -/
theorem c1_F3 : ∀ S ∈ allSubs 2, JSNucleus chain2 S := by decide +kernel
/-- F5 at the 2-chain, every subset. -/
theorem c1_F5 : ∀ S ∈ allSubs 2, EpsS chain2 S := by decide +kernel

/-! ## C2: the Boolean algebra `2²` -/

theorem c2_F1 : AlphaIso bool4 := by decide +kernel
theorem c2_F2 : EpsIso anti2 := by decide +kernel
/-- Exactly 4 of the 256 self-maps of `2²` are nuclei. -/
theorem c2_nuclei : (nucleiOf bool4).length = 4 := by decide +kernel
/-- Control: every nucleus on `2²` is closed, `j x = j ⊥ ∨ x`. -/
theorem c2_closed : ∀ t ∈ nucleiOf bool4, ∀ x ∈ bool4.pts,
    tab t x = bool4.join (tab t bool4.bot) x := by decide +kernel
theorem c2_F4 : ∀ t ∈ nucleiOf bool4, Rep bool4 (tab t) := by decide +kernel
theorem c2_F6 : ∀ S ∈ allSubs bool4.mprimes.length, Bij bool4 S := by decide +kernel
theorem c2_F7 : ∀ t ∈ nucleiOf bool4, ∀ t' ∈ nucleiOf bool4,
    OrdRev bool4 (tab t) (tab t') := by decide +kernel
theorem c2_F8 : ∀ t ∈ nucleiOf bool4, ∀ t' ∈ nucleiOf bool4,
    MeetUnion bool4 (tab t) (tab t') := by decide +kernel
theorem c2_F9 : ∀ a ∈ bool4.pts, Thm34 bool4 a := by decide +kernel
theorem c2_F3 : ∀ S ∈ allSubs 2, JSNucleus anti2 S := by decide +kernel
theorem c2_F5 : ∀ S ∈ allSubs 2, EpsS anti2 S := by decide +kernel

/-! ## C3: the Rieger–Nishimura truncation `RN₈` and the ladder -/

/-- The generator `p` of `RN₈`. -/
def p : Nat := 1

/-- The designed nuclei on `RN₈`: closed `u_p`, open `v_p`, `w_p`,
`w_⊥ = ¬¬`, and the meet `u_p ∧ ¬¬`. -/
def rnNuclei : List (Nat → Nat) :=
  [rn8.u p, rn8.v p, rn8.w p, rn8.w rn8.bot, rn8.jMeet (rn8.u p) (rn8.w rn8.bot)]

theorem c3_F1 : AlphaIso rn8 := by decide +kernel
theorem c3_F2 : EpsIso ladder4 := by decide +kernel
/-- The designed maps are nuclei. -/
theorem c3_nuclei : ∀ j ∈ rnNuclei, rn8.isNucleus j = true := by decide +kernel
/-- F4 at `RN₈`, each designed nucleus. -/
theorem c3_F4 : ∀ j ∈ rnNuclei, Rep rn8 j := by decide +kernel
/-- F9 at `RN₈`, every element (this covers `u_p, v_p, w_p, w_⊥`). -/
theorem c3_F9 : ∀ a ∈ rn8.pts, Thm34 rn8 a := by decide +kernel
/-- F8 at `RN₈` for `u_p ∧ ¬¬` ([BG] Cor 31). -/
theorem c3_F8 : MeetUnion rn8 (rn8.u p) (rn8.w rn8.bot) := by decide +kernel
/-- F6 at `RN₈`, every one of the 16 subsets of the ladder: each gives a
nucleus, and `S_{jA S} = S`. -/
theorem c3_F6 : ∀ S ∈ allSubs rn8.mprimes.length, Bij rn8 S := by decide +kernel
/-- F7 at `RN₈` over the 16 nuclei of F6, all 256 ordered pairs. -/
theorem c3_F7 : ∀ S ∈ allSubs 4, ∀ S' ∈ allSubs 4,
    OrdRev rn8 (rn8.jA S) (rn8.jA S') := by decide +kernel
/-- F8 at `RN₈` over the 16 nuclei of F6, all 256 ordered pairs. -/
theorem c3_F8all : ∀ S ∈ allSubs 4, ∀ S' ∈ allSubs 4,
    MeetUnion rn8 (rn8.jA S) (rn8.jA S') := by decide +kernel
/-- F3 at the ladder, every subset. -/
theorem c3_F3 : ∀ S ∈ allSubs 4, JSNucleus ladder4 S := by decide +kernel
/-- F5 at the ladder, every subset. -/
theorem c3_F5 : ∀ S ∈ allSubs 4, EpsS ladder4 S := by decide +kernel

/-! ## M: morphism cells (F10a, F10) -/

/-- The Heyting embedding `2 ↪ C₃`, `0 ↦ 0, 1 ↦ 2`. -/
def incl : Nat → Nat := tab [0, 2]
/-- The Heyting quotient `C₃ ↠ 2`, `0 ↦ 0, 1 ↦ 1, 2 ↦ 1`. -/
def quot : Nat → Nat := tab [0, 1, 1]

theorem m_incl_hom : isHAHom two chain3 incl = true := by decide +kernel
theorem m_quot_hom : isHAHom chain3 two quot = true := by decide +kernel
/-- F10a (◯-free) at both maps. -/
theorem m_F10a : PMorph two chain3 incl ∧ PMorph chain3 two quot := by decide +kernel
/-- F10 at the embedding, every pair of nuclei (2 × 4). -/
theorem m_F10_incl : ∀ t ∈ nucleiOf two, ∀ t' ∈ nucleiOf chain3,
    NuclearHom two chain3 (tab t) (tab t') incl := by decide +kernel
/-- F10 at the quotient, every pair of nuclei (4 × 2). -/
theorem m_F10_quot : ∀ t ∈ nucleiOf chain3, ∀ t' ∈ nucleiOf two,
    NuclearHom chain3 two (tab t) (tab t') quot := by decide +kernel

/-- **REFUTED: the naive transfer of [BBCGGJ] Remark 4.6.**  Along the
embedding `2 ↪ C₃`, with the identity nucleus on `2` and `¬¬` on `C₃`, the
embedding commutes with the nuclei, but `h_*⁻¹(S_id) = X_{C₃} ≠ S_{¬¬}`. -/
theorem m_naive_refuted : ¬ NaiveHom two chain3 (tab [0, 1]) (tab [0, 2, 2]) incl := by
  decide +kernel

/-- The same pair is nuclear, and (∗) holds. -/
theorem m_naive_cell_nuclear :
    (two.pts.all fun a => incl (tab [0, 1] a) == tab [0, 2, 2] (incl a)) = true ∧
    starCond two chain3 (tab [0, 1]) (tab [0, 2, 2]) incl = true := by decide +kernel

/-! ## Negative gates (watched failing) -/

/-- G1: `j_S` with the orientation reversed, `X ∖ ↑(S ∖ U)`. -/
def jSup (X : FinOrd) (S U : Bits) : Bits :=
  X.pts.map fun x => !(X.pts.any fun y => X.le y x && mem S y && !(mem U y))

/-- G1 fails: with `↑` in place of `↓`, F4's identity breaks at `C₃`. -/
theorem gate_G1 : ¬ ∀ t ∈ nucleiOf chain3,
    ∀ a ∈ chain3.pts, chain3.alpha (tab t a) = jSup chain3.dual (chain3.Sj (tab t)) (chain3.alpha a) := by
  decide +kernel

/-- G2 fails: dropping `max` from [BG] Thm 34(3) breaks it at `RN₈`. -/
theorem gate_G2 : ¬ ∀ a ∈ rn8.pts, rn8.Sj (rn8.w a) = bcompl (rn8.alpha a) := by
  decide +kernel

/-- G3 fails: a non-nucleus (`0 ↦ 1, 1 ↦ 2, 2 ↦ 2`, not idempotent) is
rejected. -/
theorem gate_G3 : chain3.isNucleus (tab [1, 2, 2]) = false := by decide +kernel

/-- G4 fails: a corrupted presentation (`2²` with `→` replaced by `∧`) is
rejected by `isHA`. -/
theorem gate_G4 : ({ bool4 with himpT := bool4.meetT } : FinHA).isHA = false := by
  decide +kernel

end EsakiaNuclear.Cells

/-! ## Axiom pins: every cell is choice-free, `[propext]` at most -/

#axioms_within EsakiaNuclear.Cells.one_isHA [propext]
#axioms_within EsakiaNuclear.Cells.c0_dual [propext]
#axioms_within EsakiaNuclear.Cells.c0_F1 [propext]
#axioms_within EsakiaNuclear.Cells.c0_F2 [propext]
#axioms_within EsakiaNuclear.Cells.c0_F4 [propext]
#axioms_within EsakiaNuclear.Cells.c0_F6 [propext]
#axioms_within EsakiaNuclear.Cells.c0_F3 [propext]
#axioms_within EsakiaNuclear.Cells.c0_F5 [propext]
#axioms_within EsakiaNuclear.Cells.chain3_isHA [propext]
#axioms_within EsakiaNuclear.Cells.two_isHA [propext]
#axioms_within EsakiaNuclear.Cells.bool4_isHA [propext]
#axioms_within EsakiaNuclear.Cells.rn8_isHA [propext]
#axioms_within EsakiaNuclear.Cells.chain2_isPoset [propext]
#axioms_within EsakiaNuclear.Cells.anti2_isPoset [propext]
#axioms_within EsakiaNuclear.Cells.ladder4_isPoset [propext]
#axioms_within EsakiaNuclear.Cells.rn8_dual_iso_ladder4 [propext]
#axioms_within EsakiaNuclear.Cells.c1_F1 [propext]
#axioms_within EsakiaNuclear.Cells.c1_F2 [propext]
#axioms_within EsakiaNuclear.Cells.c1_nuclei [propext]
#axioms_within EsakiaNuclear.Cells.c1_F4 [propext]
#axioms_within EsakiaNuclear.Cells.c1_F6 [propext]
#axioms_within EsakiaNuclear.Cells.c1_F7 [propext]
#axioms_within EsakiaNuclear.Cells.c1_F8 [propext]
#axioms_within EsakiaNuclear.Cells.c1_F9 [propext]
#axioms_within EsakiaNuclear.Cells.c1_F3 [propext]
#axioms_within EsakiaNuclear.Cells.c1_F5 [propext]
#axioms_within EsakiaNuclear.Cells.c2_F1 [propext]
#axioms_within EsakiaNuclear.Cells.c2_F2 [propext]
#axioms_within EsakiaNuclear.Cells.c2_nuclei [propext]
#axioms_within EsakiaNuclear.Cells.c2_closed [propext]
#axioms_within EsakiaNuclear.Cells.c2_F4 [propext]
#axioms_within EsakiaNuclear.Cells.c2_F6 [propext]
#axioms_within EsakiaNuclear.Cells.c2_F7 [propext]
#axioms_within EsakiaNuclear.Cells.c2_F8 [propext]
#axioms_within EsakiaNuclear.Cells.c2_F9 [propext]
#axioms_within EsakiaNuclear.Cells.c2_F3 [propext]
#axioms_within EsakiaNuclear.Cells.c2_F5 [propext]
#axioms_within EsakiaNuclear.Cells.c3_F1 [propext]
#axioms_within EsakiaNuclear.Cells.c3_F2 [propext]
#axioms_within EsakiaNuclear.Cells.c3_nuclei [propext]
#axioms_within EsakiaNuclear.Cells.c3_F4 [propext]
#axioms_within EsakiaNuclear.Cells.c3_F9 [propext]
#axioms_within EsakiaNuclear.Cells.c3_F8 [propext]
#axioms_within EsakiaNuclear.Cells.c3_F6 [propext]
#axioms_within EsakiaNuclear.Cells.c3_F7 [propext]
#axioms_within EsakiaNuclear.Cells.c3_F8all [propext]
#axioms_within EsakiaNuclear.Cells.c3_F3 [propext]
#axioms_within EsakiaNuclear.Cells.c3_F5 [propext]
#axioms_within EsakiaNuclear.Cells.m_incl_hom [propext]
#axioms_within EsakiaNuclear.Cells.m_quot_hom [propext]
#axioms_within EsakiaNuclear.Cells.m_F10a [propext]
#axioms_within EsakiaNuclear.Cells.m_F10_incl [propext]
#axioms_within EsakiaNuclear.Cells.m_F10_quot [propext]
#axioms_within EsakiaNuclear.Cells.m_naive_refuted [propext]
#axioms_within EsakiaNuclear.Cells.m_naive_cell_nuclear [propext]
#axioms_within EsakiaNuclear.Cells.gate_G1 [propext]
#axioms_within EsakiaNuclear.Cells.gate_G2 [propext]
#axioms_within EsakiaNuclear.Cells.gate_G3 [propext]
#axioms_within EsakiaNuclear.Cells.gate_G4 [propext]

-- The pin gate, watched failing: `c3_F6` does use `propext`, so the empty
-- bound is rejected, and the rejection is the expected message.
/-- error: 'EsakiaNuclear.Cells.c3_F6' depends on propext, which the bound does not allow.
  declared: []
Locate the entry with:  #axiom_path propext EsakiaNuclear.Cells.c3_F6 -/
#guard_msgs in
#axioms_within EsakiaNuclear.Cells.c3_F6 []
