/-
# The residue attacked: a cone-trivial NON-maximal corner, realised and served

The open kernel after round 2 was the corner at a cone-trivial world
that is not `≤`-maximal, where a poisoned `Λ*`-implication defeats every
chosen valuation.  This file settles its status by instance:

    KR:  a < b,  V(a) = ∅,  V(b) = {p, w},  Rm = identity, infallible
    GR = (A ⊃ w) ⊃ ◯w,   A := p ∨ (p ⊃ q)

* the corner FIRES at `a` for body `w` (`residue_corner`): `cone(a) =
  {a}`, `a` is not maximal, `a ⊮ ◯w`, and every proper extension forces
  `w`;
* `Λ*_a = {A ⊃ w}` with `A` a CLASSICAL TAUTOLOGY, so the
  chosen-valuation route is PROVABLY blocked (`route3_blocked`): no
  valuation satisfies `Λ*_a` and refutes `w` — the first kernel-checked
  witness that frj-w4 §11 route 3 is insufficient;
* the demanded wit EXISTS anyway (`residueWit`), built by
  **Υ-enrichment**: the poisoned antecedent `A` enters `Υ` through its
  own irregular row (`orI` over `Ax^I` and a `⊃∉`), whereupon the
  `⋈^At`'s second zone retains `A ⊃ w` — the PAPER retention
  (`keptChain_of_ups`), no `RefAt` relaxation needed;
* the full supply is then total for this instance (`supplyR`), and
  `minModV` runs end to end: `provableV_residue`.

Design consequence (the general discharge): the corner's regular
`Z`-row is a join whose `Υ` is enriched with the poisoned antecedents —
each an `sfR`-member unforced at the corner world, so exactly the
demands the recursion's irregular layer already serves.  What is
missing is only the MEASURE that lets `I(◯Z)@a` call those `I(A)@a`
cells (the seen-mechanism of frj-w4 §11); no calculus gap and no new
supply is indicated, and the V-kept chains were NOT needed here.
-/
import wip.minmodv
import wip.minmodv_seen
import wip.minmodv_assembly
import wip.minmodv_liftmain
import FRJ.WitnessKit

set_option maxRecDepth 4000

namespace FRJ.MinModVResidue

open FRJ Form

/-! ## The instance -/

def pF : Form := .atom "p"
def qF : Form := .atom "q"
def wF : Form := .atom "w"
/-- The poisoned antecedent: classically tautologous, unforced at `a`. -/
def AF : Form := .or pF (.imp pF qF)
def AwF : Form := .imp AF wF
def GR : Form := .imp AwF (.circ wF)

/-- Two worlds `a = false < b = true`; `Rm` is the identity, so `a`'s
modal cone is `{a}` while `b` sits strictly above. -/
def KR : Kripke where
  W := Bool
  elems := [false, true]
  complete := fun w => by cases w <;> simp
  decEq := inferInstance
  le := fun x y => x = false ∨ y = true
  le_refl := fun a => by cases a <;> simp
  le_trans := fun {a b c} h1 h2 => by
    rcases h1 with h | h
    · exact Or.inl h
    · rcases h2 with h' | h'
      · rw [h'] at h; exact absurd h (by simp)
      · exact Or.inr h'
  le_antisymm := fun {a b} h1 h2 => by
    cases a <;> cases b <;> simp_all
  root := false
  root_le := fun _ => Or.inl rfl
  V := fun x s => x = true ∧ (s = "p" ∨ s = "w")
  V_mono := fun {a b} hab _ hV => by
    obtain ⟨ha, hs⟩ := hV
    subst ha
    rcases hab with h | h
    · exact absurd h (by simp)
    · exact ⟨h, hs⟩
  Rm := fun x y => x = y
  rm_refl := fun _ => rfl
  rm_trans := fun h1 h2 => h1.trans h2
  sub_mi := fun {a b} h => by subst h; cases a <;> simp
  Fal := fun _ => False
  fal_mono := fun _ h => h.elim
  fal_V := fun h => h.elim
  decLe := fun a b => inferInstanceAs (Decidable (a = false ∨ b = true))
  decV := fun a s => inferInstanceAs (Decidable (a = true ∧ (s = "p" ∨ s = "w")))
  decRm := fun a b => inferInstanceAs (Decidable (a = b))
  decFal := fun _ => inferInstanceAs (Decidable False)

theorem KR_infallible : KR.Infallible := fun _ h => h

/-! ## The corner is realised, and it is the RESIDUE corner -/

/-- `a` is cone-trivial, NOT `≤`-maximal, refutes `◯w`, and every proper
extension forces `w` — the exact firing condition of `CircSupplyV`, at a
world `circSupplyV_of_coneGrounded` cannot reach. -/
theorem residue_corner :
    KR.ConeTrivial false ∧
    (KR.le false true ∧ (true : KR.W) ≠ false) ∧
    ¬ KR.force false (.circ wF) ∧
    (∀ u, KR.le false u → u ≠ false → KR.force u wF) := by
  refine ⟨fun c h => h.symm, ⟨Or.inl rfl, by simp⟩, by decide, ?_⟩
  intro u _ hu
  cases u with
  | false => exact absurd rfl hu
  | true => exact ⟨rfl, Or.inr rfl⟩

theorem hloc_R : ∀ b : KR.W, circPart (lamStar KR b GR) = [] := by
  intro b
  cases b <;> decide

/-! ## (R1) The chosen-valuation route is PROVABLY blocked -/

/-- The poisoned antecedent is a classical tautology. -/
theorem classForce_A_true (ats : List Form) : classForce ats AF = true := by
  by_cases h : Form.atom "p" ∈ ats <;>
    simp [AF, pF, qF, classForce, h]

/-- **No valuation serves the corner**: anything satisfying `Λ*_a`
classically forces `w`.  Route 3 of frj-w4 §11 is insufficient — the
first kernel-checked residue witness. -/
theorem route3_blocked :
    ∀ ats : List Form,
      ¬ ((∀ X ∈ lamStar KR false GR, classForce ats X = true) ∧
         classForce ats wF = false) := by
  rintro ats ⟨hsat, href⟩
  have hAw : AwF ∈ lamStar KR false GR := by decide
  have h1 := hsat _ hAw
  have hstep : classForce ats AwF = classForce ats wF := by
    rw [show classForce ats AwF =
        (!classForce ats AF || classForce ats wF) from rfl,
      classForce_A_true ats]
    simp
  rw [hstep] at h1
  rw [h1] at href
  exact Bool.noConfusion href

/-! ## (R2) The demanded wit exists — Υ-enrichment beats the poison -/

namespace Wit

/-- `Ax^I` zone at `p`. -/
def Θp : List Form := FRJ.rm (gAt GR) pF ++ gImp GR ++ gCirc GR

/-- `· ; Ĝ∖{p} → p`. -/
def Rp : FRJVi GR [] Θp pF :=
  .axI pF (by decide) (by decide) (CtxEq.refl _)

/-- `Ĝ_at∖{q} ⇒ q` — the `Ax^R` row whose context `Clo`-grounds both
`p` (a member) and `A ⊃ w` (via the consequent `w`, a member). -/
def Rq : FRJVr GR .barren (FRJ.rm (gAt GR) qF) qF :=
  .axR qF (by decide) (by decide) (CtxEq.refl _)

/-- `· ; {A⊃w} → p⊃q` by `⊃∉`: the second poisoned disjunct, refuted at
the row `Rq` realises, with the poisoned implication RETAINED in `Θ`
(its `Clo`-membership goes through the consequent `w ∈ Ĝ_at∖{q}`). -/
def Rpq : FRJVi GR [] [AwF] (.imp pF qF) :=
  .impNotIn Rq
    (fun X hX => by
      rw [List.mem_singleton] at hX
      subst hX
      exact ⟨.imp (.base (by decide)), by decide⟩)
    (.base (by decide))
    (fun h => absurd (cloB_iff.mpr h) (by decide))
    (by decide)

/-- `· ; {A⊃w} → A` — the Υ-enrichment row: `A` becomes a premise right
formula, which is all the second-zone retention of `A ⊃ w` needs. -/
def RA : FRJVi GR [] (FRJ.cap Θp [AwF]) AF :=
  .orI Rp Rpq
    (List.nil_subset _) (List.nil_subset _)
    (by decide) (CtxEq.refl _) (CtxEq.refl _)

def stab1 : Fin 1 → List Form := fun _ => []
def th1 : Fin 1 → List Form := fun _ => FRJ.cap Θp [AwF]
def rhs1 : Fin 1 → Form := fun _ => AF

/-- The regular `w`-row: `⋈^At` over `{RA}`.  `Υ = {A}`, so the paper
second zone (`keptChain_restrict`) keeps `A ⊃ w`, and the conclusion
context is exactly `{A ⊃ w}`-flavoured — `Clo`-grounding `Λ*_a`. -/
def Rw : FRJVr GR .barren
    (joinCtxAtVBase stab1 th1 wF ++ restrict (thPool th1) (upsilon rhs1))
    wF :=
  .joinAt (fun _ => RA)
    (by decide)
    (hJ2_of_impAnteB (by decide))
    (by decide)
    (keptChain_restrict _ th1)
    (by decide) (by decide) (by decide)
    (CtxEq.refl _)

/-- The corner's irregular `◯w`-cell, by `◯∉` from `Rw`:
`· ; Λ*_a → ◯w`. -/
def wit : FRJVi GR [] (lamStar KR false GR) (.circ wF) :=
  .circNotIn Rw (Or.inl rfl)
    (fun X hX => by
      rw [show lamStar KR false GR = [AwF] from by decide,
        List.mem_singleton] at hX
      subst hX
      exact ⟨.base (by decide), by decide⟩)
    (by decide)

end Wit

/-- **The residue corner is SERVED**: the demanded covering wit exists,
though every chosen valuation fails. -/
def residueWit : IrrWitV KR GR false (.circ wF) :=
  ⟨[], lamStar KR false GR, Wit.wit, List.nil_subset _, fun _ hx => hx⟩

/-! ## (R3) The supply is total here, and the recursion runs end to end -/

def supplyR : CircSupplyV KR GR := fun a Z hZ hnf _ => by
  have hZw : Z = wF := by
    simp only [GR, AwF, AF, pF, qF, wF, sfR, sfPos, sfNeg] at hZ
    simp_all [wF]
  subst hZw
  cases a with
  | false => exact residueWit
  | true => exact absurd (by decide : KR.force true (.circ wF)) hnf

/-- **`minModV` end to end on the residue instance** — the corner where
round 2's frame-condition discharge cannot reach, closed by the
Υ-enrichment wit. -/
theorem provableV_residue : ProvableV GR :=
  completenessV_of_supply KR hloc_R KR_infallible supplyR
    (by change ¬ KR.force KR.root GR; decide)

/-! ## Round 3: the same instance, supply-free by the goal guard

`GR`'s left-implication antecedents (`A`, `p`) are `◯`-free, so the
seen-parametrised recursion serves it with NO supply — on this frame,
which is exactly the non-cone-grounded one round 2 could not reach. -/

theorem provableV_residue_guarded : ProvableV GR :=
  completenessV_of_circAnteFree KR
    (guard_of_guardB (by decide))
    hloc_R KR_infallible
    (by change ¬ KR.force KR.root GR; decide)

/-- info: 'FRJ.MinModVResidue.provableV_residue_guarded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_residue_guarded

/-! ## The assembly closes the instance with NOTHING: no supply, no
guard, no frame condition — `completenessV` end to end on the residue
model. -/

theorem provableV_residue_assembled : ProvableV GR :=
  completenessV KR hloc_R KR_infallible
    (by change ¬ KR.force KR.root GR; decide)

/-- info: 'FRJ.MinModVResidue.provableV_residue_assembled' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_residue_assembled

/-- The residue cell through the LIFTED recursion. -/
theorem provableV_residue_lifted : ProvableV GR :=
  completenessV_of_hloc KR hloc_R KR_infallible
    (by change ¬ KR.force KR.root GR; decide)

/-- info: 'FRJ.MinModVResidue.provableV_residue_lifted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_residue_lifted

/-- info: 'FRJ.MinModVResidue.route3_blocked' depends on axioms: [propext] -/
#guard_msgs in
#print axioms route3_blocked

/-- info: 'FRJ.MinModVResidue.provableV_residue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_residue

end FRJ.MinModVResidue
