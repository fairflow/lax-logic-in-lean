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

/-- The computed dual of `C₃` is the 2-chain, by `0 ↦ 1, 1 ↦ 0`. -/
theorem chain3_dual_iso_chain2 :
    chain3.mprimes = [0, 1] ∧
    ∀ i ∈ List.range 2, ∀ k ∈ List.range 2,
      chain3.dual.le i k = chain2.le ([1, 0].getD i 0) ([1, 0].getD k 0) := by
  decide +kernel

/-- The computed dual of `2²` is the 2-antichain, by the identity. -/
theorem bool4_dual_iso_anti2 :
    bool4.mprimes = [1, 2] ∧
    ∀ i ∈ List.range 2, ∀ k ∈ List.range 2, bool4.dual.le i k = anti2.le i k := by
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

/-! ## R: a screen of the bridge statement R3 (`wip/esakiaNuclearGen.lean`)

R3 is stated for the library's `ConstraintModel` (sets, not decidable).  This
section screens it in the finite encoding: a finite constraint model as
tables, its complex algebra `(H_C, j_C)` as a `FinHA` with a nucleus, and
the claims R2, R3a, R3b, R3c checked on two designed models.  These are
tests of the statement's content, not instances of the `Set`-level
statement. -/

/-- A finite constraint model as tables (worlds `0, …, n-1`). -/
structure FinCons where
  n : Nat
  ri : Nat → Nat → Bool
  rm : Nat → Nat → Bool
  fall : Bits

namespace FinCons

variable (C : FinCons)

def pts : List Nat := List.range C.n

/-- `Rᵢ`, `Rₘ` preorders, `Rₘ ⊆ Rᵢ`, `F` hereditary. -/
def wf : Bool :=
  (C.pts.all fun x => C.ri x x && C.rm x x) &&
  (C.pts.all fun x => C.pts.all fun y => C.pts.all fun z =>
    (!(C.ri x y && C.ri y z) || C.ri x z) && (!(C.rm x y && C.rm y z) || C.rm x z)) &&
  (C.pts.all fun x => C.pts.all fun y =>
    (!(C.rm x y) || C.ri x y) && (!(C.ri x y && mem C.fall x) || mem C.fall y))

/-- `Rᵢ` is antisymmetric. -/
def antisymm : Bool := C.pts.all fun x => C.pts.all fun y => !(C.ri x y && C.ri y x) || x == y

/-- `U ∈ H_C`: hereditary along `Rᵢ` and containing `F`. -/
def isHC (U : Bits) : Bool :=
  (C.pts.all fun x => C.pts.all fun y => !(mem U x && C.ri x y) || mem U y) &&
  (C.pts.all fun x => !(mem C.fall x) || mem U x)

def hcs : List Bits := (allSubs C.n).filter C.isHC

def hcIdx (U : Bits) : Nat :=
  ((List.range C.hcs.length).find? fun i => C.hcs.getD i [] == U).getD 0

/-- `j_C(U) = {w | ∀ v, w Rᵢ v → ∃ u, v Rₘ u ∧ u ∈ U}`. -/
def jC (U : Bits) : Bits :=
  C.pts.map fun w => C.pts.all fun v => !(C.ri w v) || C.pts.any fun u => C.rm v u && mem U u

/-- `(H_C, ⊆)` as a finite Heyting algebra: `∩`, `∪`, Kripke `→`, `⊤ = W`,
`⊥ = F`. -/
def hcHA : FinHA :=
  let U (i : Nat) : Bits := C.hcs.getD i []
  let I := List.range C.hcs.length
  let imp (A B : Bits) : Bits :=
    C.pts.map fun x => C.pts.all fun y => !(C.ri x y && mem A y) || mem B y
  { ord := ⟨C.hcs.length, fun i k => C.pts.all fun x => !(mem (U i) x) || mem (U k) x⟩
    meetT := I.map fun i => I.map fun k => C.hcIdx (List.zipWith (· && ·) (U i) (U k))
    joinT := I.map fun i => I.map fun k => C.hcIdx (List.zipWith (· || ·) (U i) (U k))
    himpT := I.map fun i => I.map fun k => C.hcIdx (imp (U i) (U k))
    top := C.hcIdx (C.pts.map fun _ => true)
    bot := C.hcIdx C.fall }

def jCIdx (i : Nat) : Nat := C.hcIdx (C.jC (C.hcs.getD i []))

/-- `W ∖ ↓w`. -/
def mPt (w : Nat) : Bits := C.pts.map fun u => !(C.ri u w)

/-- `w` is `Rₘ`-final (the library's `ConstraintModel.RmFinal`). -/
def rmFinal (w : Nat) : Bool := C.pts.all fun u => !(C.rm w u) || C.rm u w

/-- R2 (finite encoding): `H_C` is a Heyting algebra and `j_C` a nucleus on it. -/
def R2screen : Bool := C.hcHA.isHA && C.hcHA.isNucleus C.jCIdx

/-- R3a (finite encoding): `j_C(W ∖ ↓w) = W ∖ ↓w ↔ w` is `Rₘ`-final. -/
def R3aScreen : Bool := C.pts.all fun w => (C.jC (C.mPt w) == C.mPt w) == C.rmFinal w

/-- R3b (finite encoding): every meet-prime of `H_C` is some `W ∖ ↓w`,
`w ∉ F`. -/
def R3bScreen : Bool :=
  C.hcHA.mprimes.all fun m => C.pts.any fun w => !(mem C.fall w) && C.hcs.getD m [] == C.mPt w

/-- R3c (finite encoding): each `W ∖ ↓w`, `w ∉ F`, is a meet-prime, ordered
dually to `Rᵢ`. -/
def R3cScreen : Bool :=
  (C.pts.all fun w => mem C.fall w || C.hcHA.isMeetPrime (C.hcIdx (C.mPt w))) &&
  (C.pts.all fun v => C.pts.all fun w =>
    (C.pts.all fun x => !(mem (C.mPt v) x) || mem (C.mPt w) x) == C.ri w v)

end FinCons

/-- Designed model `C_R`: `0 ≤ 1`, `0 ≤ 2`, all `≤ 3`; `3` fallible;
`Rₘ`: `0 Rₘ 1` and `2 Rₘ 3` (with reflexivity).  `Rₘ`-final non-fallible
worlds: `1` only. -/
def cR : FinCons :=
  { n := 4
    ri := fun x y => x == y || y == 3 || (x == 0 && (y == 1 || y == 2))
    rm := fun x y => x == y || (x == 0 && y == 1) || (x == 2 && y == 3)
    fall := [false, false, false, true] }

theorem cR_wf : cR.wf = true ∧ cR.antisymm = true := by decide +kernel
/-- R2, R3a, R3b, R3c pass at `C_R`; the dual `S` is `{W ∖ ↓1}`. -/
theorem cR_R3 : cR.R2screen = true ∧ cR.R3aScreen = true ∧ cR.R3bScreen = true ∧
    cR.R3cScreen = true := by decide +kernel
/-- Non-vacuity: `j_C` is neither the identity nor `⊤` on `H_C`, and exactly
one point (`w = 1`) is `Rₘ`-final among the non-fallible worlds. -/
theorem cR_nonvacuous : cR.hcs.length = 5 ∧
    (cR.hcHA.pts.any fun i => cR.jCIdx i != i) = true ∧
    (cR.hcHA.pts.any fun i => cR.jCIdx i != cR.hcHA.top) = true ∧
    ([0, 1, 2].map cR.rmFinal) = [false, true, false] := by decide +kernel

/-- Designed counter-cell for the HYPOTHESIS of R3a: `Rᵢ` a preorder with
`0 ≡ 1`, `Rₘ` adds `0 Rₘ 1` only, no fallible worlds. -/
def cPre : FinCons :=
  { n := 2, ri := fun _ _ => true, rm := fun x y => x == y || (x == 0 && y == 1),
    fall := [false, false] }

/-- **R3a needs antisymmetry**: at `cPre` (well-formed, not antisymmetric),
`W ∖ ↓0 = ∅` is fixed by `j_C` but `0` is not `Rₘ`-final. -/
theorem cPre_R3a_fails : cPre.wf = true ∧ cPre.antisymm = false ∧
    cPre.R3aScreen = false := by decide +kernel

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
#axioms_within EsakiaNuclear.Cells.chain3_dual_iso_chain2 [propext]
#axioms_within EsakiaNuclear.Cells.bool4_dual_iso_anti2 [propext]
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
#axioms_within EsakiaNuclear.Cells.cR_wf [propext]
#axioms_within EsakiaNuclear.Cells.cR_R3 [propext]
#axioms_within EsakiaNuclear.Cells.cR_nonvacuous [propext]
#axioms_within EsakiaNuclear.Cells.cPre_R3a_fails [propext]

-- The pin gate, watched failing: `c3_F6` does use `propext`, so the empty
-- bound is rejected, and the rejection is the expected message.
/-- error: 'EsakiaNuclear.Cells.c3_F6' depends on propext, which the bound does not allow.
  declared: []
Locate the entry with:  #axiom_path propext EsakiaNuclear.Cells.c3_F6 -/
#guard_msgs in
#axioms_within EsakiaNuclear.Cells.c3_F6 []
