/-
# The repaired calculus derives the ρ-order cell `[ρ19] ⊢? ρ18` — negative

    G1918 = (ρ11 ⊃ b) ⊃ (ρ14 ∨ ρ9)
          = ((◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥)) ⊃ ◯¬◯⊥)
              ⊃ (((◯¬◯⊥ ∨ ¬¬◯⊥) ⊃ (◯⊥ ∨ ¬◯⊥)) ∨ (◯¬◯⊥ ∨ ¬¬◯⊥))

HAND-BUILT (2026-08-26, Matthew's directive: anticipate the steps, no
engine) against the cell's banked 5-world countermodel (`sep-86`,
root 0: a bad world 1 forcing b and ρ9 but not ρ4, whose cone holds the
¬a-world 2 [Rm from 1], the fallible top 3, and the a-world 4 [Rm to
3]).  The tree, bottom-up (a = ◯⊥, b = ◯¬a; contexts up to `≐`):

    R1    Ax^I ⊥              · ; Ĝ → ⊥
    Ta    ⊃∈ⁱ Λ={a}           a ; Ĝ∖{a} → ¬a
    R3a   ⋈^At_F {Ta}         [blocked] a, ¬¬a, b ⇒ ⊥      (world 4)
    i_na  ⊃∉ R3a (A=a)        · ; b, ρ19 → ¬a
    R2    ⋈^At {R1}           [barren] ¬a ⇒ ⊥              (world 2;
                               kept: ¬a via the RefAt ◯-clause on a)
    i_nna ⊃∉ R2 (A=¬a)        · ; ρ19 → ¬¬a
    iA    ◯∉ R2               · ; ¬a, b, ρ19 → a
    Q     ⋈^∨,p {iA,i_na} promise {R2}
                              [chain ⊥] b ⇒ a ∨ ¬a (= ρ4)  (world 1;
                               b promise-kept: Clo {¬a} ∋ ¬a)
    i14   ⊃∉ Q (A=ρ9)         · ; ρ19 → ρ14
    i11   ⊃∉ Q (A=b)          · ; ρ19 → ρ11
    ROOT  ⋈^∨ {i14,i11,i_na,i_nna}
                              [barren] ρ19 ⇒ ρ14 ∨ ρ9 (= ρ18)
                               (kept: ρ19, ante ρ11 ∈ Υ; RefAt ρ14 by
                                ups, RefAt ρ9 = or(circ(ups ¬a), ups ¬¬a))
    goal  ⊃∈ ROOT             [barren] ρ19 ⇒ G1918
-/
import FRJ.WitnessV1215
import FRJ.WitnessKit

set_option maxRecDepth 4000

open FRJ Form

namespace FRJ.WitnessV1918


/-! ## The cell -/

def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def nnaF : Form := .imp naF .bot
def r4 : Form := .or aF naF
def r9 : Form := .or bF nnaF
def r11 : Form := .imp bF r4
def r14 : Form := .imp r9 r4
def r18 : Form := .or r14 r9
def r19 : Form := .imp r11 bF
def G1918 : Form := .imp r19 r18

namespace W1918

/-- The `Ax^I` second zone. -/
def Θax : List Form := FRJ.rm (gAt G1918) .bot ++ gImp G1918 ++ gCirc G1918

def R1 : FRJVi G1918 [] Θax .bot :=
  .axI .bot (by decide) (by decide) (CtxEq.refl _)

/-- `a ; Ĝ∖{a} → ¬a` — the assume-`a` fragment of world 4. -/
def Ta : FRJVi G1918 [aF] (FRJ.sdiff Θax [aF]) naF :=
  .impInI (Th := FRJ.sdiff Θax [aF]) (Lam := [aF]) R1
    (zoneSplit (by decide)) cap_sdiff_eq_nil
    (by decide) (by decide) (CtxEq.refl _) (CtxEq.refl _)

/-- World 4, blocked (`a`'s cone hits the fallible top): the context
retains `a` (stable circ), `b` (θ-circ intersection) and `¬¬a` (the
Υ-restricted implication zone). -/
def Γ3a : List Form :=
  joinCtxAtF (fun _ : Fin 1 => [aF]) (fun _ : Fin 1 => FRJ.sdiff Θax [aF])
    (fun _ : Fin 1 => naF) .bot

def R3a : FRJVr G1918 .blocked Γ3a .bot :=
  .joinAtF (n := 0) (F := .bot)
    (stab := fun _ => [aF]) (th := fun _ => FRJ.sdiff Θax [aF])
    (rhs := fun _ => naF)
    (fun _ => Ta) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (by decide) (by decide) (CtxEq.refl _)

/-- `· ; b, ρ19 → ¬a` — `¬a` fails in world 4's cone. -/
def i_na : FRJVi G1918 [] [bF, r19] naF :=
  .impNotIn R3a (by decide) (by decide) (by decide) (by decide)

/-! World 2, the barren `¬a`-world: `⋈^At {R1}`, kept chain adopts `¬a`
(antecedent `a = ◯⊥` RefAt-refuted by the `◯`-clause over `⊥`). -/

def base2 : List Form :=
  joinCtxAtVBase (fun _ : Fin 1 => []) (fun _ : Fin 1 => Θax) .bot

def kept2 : List Form :=
  keptOf (upsilon (fun _ : Fin 1 => Form.bot)) base2
    (thPool (fun _ : Fin 1 => Θax))

def Γ2 : List Form := base2 ++ kept2

def R2 : FRJVr G1918 .barren Γ2 .bot :=
  .joinAt (n := 0) (F := .bot) (stab := fun _ => [])
    (th := fun _ => Θax) (rhs := fun _ => .bot) (kept := kept2)
    (fun _ => R1) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

/-- `· ; ρ19 → ¬¬a` — `¬¬a` fails at world 2 itself. -/
def i_nna : FRJVi G1918 [] [r19] nnaF :=
  .impNotIn R2 (by decide) (by decide) (by decide) (by decide)

/-- `· ; ¬a, b, ρ19 → a` — `a = ◯⊥` fails throughout world 2's cone. -/
def iA : FRJVi G1918 [] [naF, bF, r19] aF :=
  .circNotIn R2 (Or.inl rfl) (by decide) (by decide)

/-! World 1, the promise `⋈^∨`: premises `{iA, i_na}` (Υ = {a, ¬a}),
promise family `{R2}` (Rm 1→2).  The conclusion context keeps exactly
`b = ◯¬a`, because `Γ2 ≐ {¬a}` closes the body. -/

def rowiA : IRow G1918 := ⟨[], [naF, bF, r19], aF, iA⟩
def rowina : IRow G1918 := ⟨[], [bF, r19], naF, i_na⟩

def ΓQ : List Form :=
  joinCtxOrP (istF rowiA [rowina]) (ithF rowiA [rowina])
    (irhsF rowiA [rowina]) (fun _ : Fin 1 => Γ2)

def Q : FRJVr G1918 (.chain .bot) ΓQ r4 :=
  .joinOrP (k := 0) (tps := fun _ => .barren) (Δs := fun _ => Γ2)
    (Ds := fun _ => .bot)
    (ipremF rowiA [rowina]) (fun _ => R2) (by decide)
    (hJ2_of_impAnteB (by decide)) (hJ5_of_nil (by decide)) (by decide)
    (Or.inr ⟨rfl, fun _ => ⟨rfl, Or.inl rfl⟩⟩) ⟨by decide, by decide⟩
    (by decide) (CtxEq.refl _)

/-- `· ; ρ19 → ρ14` — ρ14's antecedent ρ9 holds at world 1 (`Clo {b}`,
left disjunct), its consequent ρ4 fails there. -/
def i14 : FRJVi G1918 [] [r19] r14 :=
  .impNotIn Q (by decide) (by decide) (by decide) (by decide)

/-- `· ; ρ19 → ρ11` — likewise with antecedent `b`. -/
def i11 : FRJVi G1918 [] [r19] r11 :=
  .impNotIn Q (by decide) (by decide) (by decide) (by decide)

/-! The root: barren `⋈^∨` concluding `ρ18 = ρ14 ∨ ρ9` over `{ρ19}`.
`Υ = {ρ14, ρ11, ¬a, ¬¬a}`; the kept chain adopts `ρ19` (antecedent
`ρ11 ∈ Υ`); the disjunct conditions are `RefAt ρ14` by `ups` and
`RefAt ρ9` by `or (circ (ups ¬a)) (ups ¬¬a)`. -/

def row14 : IRow G1918 := ⟨[], [r19], r14, i14⟩
def row11 : IRow G1918 := ⟨[], [r19], r11, i11⟩
def rowna : IRow G1918 := ⟨[], [bF, r19], naF, i_na⟩
def rownna : IRow G1918 := ⟨[], [r19], nnaF, i_nna⟩

def ROOT := FRJVr.joinOr (G := G1918) (C₁ := r14) (C₂ := r9)
    (ipremF row14 [row11, rowna, rownna]) (by decide)
    (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) ⟨by decide, by decide⟩ (by decide)
    (CtxEq.refl _)

def goal := FRJVr.impIn (G := G1918) (A := r19) (B := r18) ROOT
    (by decide) (by decide)

end W1918

/-! ## The witness -/

/-- **The repaired calculus derives the refutation sequent for
`ρ19 ⊢? ρ18`** — hand-built; through `soundnessV` this re-settles the
cell negatively, THROUGH the calculus. -/
theorem provableV_1918 : FRJ.ProvableV G1918 := ⟨.barren, _, ⟨W1918.goal⟩⟩

/-- info: 'FRJ.WitnessV1918.provableV_1918' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_1918

end FRJ.WitnessV1918
