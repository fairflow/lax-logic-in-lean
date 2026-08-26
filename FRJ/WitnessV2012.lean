/-
# The repaired calculus derives the ρ-order cell `[ρ20] ⊢? ρ12` — negative

    G2012 = (ρ11 ⊃ ρ6) ⊃ (ρ8 ⊃ b)

HAND-BUILT (2026-08-26) against the cell's banked 5-world Tab model
(`rho-0170`): root 0, bad world 1 (ρ8, ρ20, b true; ρ4 false), whose
cone holds the INTERIOR a-world 2 (Rm to the fallible top 3) and the
FINAL ¬a-world 4 (reflexive Rm only — refutes `a` genuinely).

The new device versus 1918/2018: the ¬a-world's kept chain adopts
**ρ8 = ¬¬a ⊃ a** as its second link — its antecedent `¬¬a` is
RefAt-refuted through the `imp`-clause once `¬a` is kept
(`Clo {¬a} ¬a`, then `RefAt ⊥`).  That puts `ρ8` into the world-4
context, whence it rides `Clo` through every Θ, the promise
restriction, and finally the two nested `impIn`s at the goal.  The
Υ-enrichment (orI + stable-`b` impInI, from 2018) again puts `ρ11`
into Υ so that `ρ20` survives the promise join's restricted zone.

Tree (contexts up to `≐`):

    R1    Ax^I ⊥              · ; Ĝ → ⊥
    Ta    ⊃∈ⁱ Λ={a}           a ; Ĝ∖{a} → ¬a
    R3a   ⋈^At_F {Ta}         [blocked] a, ¬¬a, b ⇒ ⊥      (world 2)
    i_na  ⊃∉ R3a (A=a)        · ; b, ρ8, ρ20 → ¬a
    R2    ⋈^At {R1}           [barren] ¬a, ρ8 ⇒ ⊥          (world 4;
                               kept: ¬a [◯-clause], ρ8 [imp-clause])
    i_a   ◯∉ R2               · ; b, ρ8, ρ20 → a
    i_nna ⊃∉ R2 (A=¬a)        · ; b, ρ8, ρ20 → ¬¬a
    iOr4  orI i_a i_na        · ; b, ρ8, ρ20 → ρ4
    i11s  ⊃∈ⁱ Λ={b} on iOr4   b ; ρ8, ρ20 → ρ11
    Q     ⋈^∨,p {i_a,i_na,i_nna,i11s} promise {R2}
                              [chain ⊥] ρ8, ρ20, b ⇒ ρ4    (world 1)
    ROOT  ⊃∈ Q (A=ρ8)         [chain ⊥] … ⇒ ρ8 ⊃ ρ4 (= ρ13)
    goal  ⊃∈ ROOT (A=ρ20)     [chain ⊥] … ⇒ G2012
-/
import FRJ.WitnessV1215
import FRJ.WitnessKit

set_option maxRecDepth 4000

open FRJ Form

namespace FRJ.WitnessV2012


/-! ## The cell -/

def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def nnaF : Form := .imp naF .bot
def r4 : Form := .or aF naF
def r6 : Form := .or naF nnaF
def r8 : Form := .imp nnaF aF
def r11 : Form := .imp bF r4
def r12 : Form := .imp r8 bF
def r20 : Form := .imp r11 r6
def G2012 : Form := .imp r20 r12

namespace W2012

def Θax : List Form := FRJ.rm (gAt G2012) .bot ++ gImp G2012 ++ gCirc G2012

def R1 : FRJVi G2012 [] Θax .bot :=
  .axI .bot (by decide) (by decide) (CtxEq.refl _)

def Ta : FRJVi G2012 [aF] (FRJ.sdiff Θax [aF]) naF :=
  .impInI (Th := FRJ.sdiff Θax [aF]) (Lam := [aF]) R1
    (zoneSplit (by decide)) cap_sdiff_eq_nil
    (by decide) (by decide) (CtxEq.refl _) (CtxEq.refl _)

def Γ3a : List Form :=
  joinCtxAtF (fun _ : Fin 1 => [aF]) (fun _ : Fin 1 => FRJ.sdiff Θax [aF])
    (fun _ : Fin 1 => naF) .bot

def R3a : FRJVr G2012 .blocked Γ3a .bot :=
  .joinAtF (n := 0) (F := .bot)
    (stab := fun _ => [aF]) (th := fun _ => FRJ.sdiff Θax [aF])
    (rhs := fun _ => naF)
    (fun _ => Ta) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (by decide) (by decide) (CtxEq.refl _)

def i_na : FRJVi G2012 [] [bF, r8, r20] naF :=
  .impNotIn R3a (by decide) (by decide) (by decide) (by decide)

def base2 : List Form :=
  joinCtxAtVBase (fun _ : Fin 1 => []) (fun _ : Fin 1 => Θax) .bot

def kept2 : List Form :=
  keptOf (upsilon (fun _ : Fin 1 => Form.bot)) base2
    (thPool (fun _ : Fin 1 => Θax))

def Γ2 : List Form := base2 ++ kept2

def R2 : FRJVr G2012 .barren Γ2 .bot :=
  .joinAt (n := 0) (F := .bot) (stab := fun _ => [])
    (th := fun _ => Θax) (rhs := fun _ => .bot) (kept := kept2)
    (fun _ => R1) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

def i_a : FRJVi G2012 [] [bF, r8, r20] aF :=
  .circNotIn R2 (Or.inl rfl) (by decide) (by decide)

def i_nna : FRJVi G2012 [] [bF, r8, r20] nnaF :=
  .impNotIn R2 (by decide) (by decide) (by decide) (by decide)

def iOr4 : FRJVi G2012 [] (FRJ.cap [bF, r8, r20] [bF, r8, r20]) r4 :=
  .orI i_a i_na (by decide) (by decide) (by decide)
    (CtxEq.refl _) (CtxEq.refl _)

def i11s : FRJVi G2012 [bF]
    (FRJ.sdiff (FRJ.cap [bF, r8, r20] [bF, r8, r20]) [bF]) r11 :=
  .impInI (Th := FRJ.sdiff (FRJ.cap [bF, r8, r20] [bF, r8, r20]) [bF])
    (Lam := [bF]) iOr4
    (zoneSplit (by decide)) cap_sdiff_eq_nil
    (by decide) (by decide) (CtxEq.refl _) (CtxEq.refl _)

def rowia : IRow G2012 := ⟨[], [bF, r8, r20], aF, i_a⟩
def rowina : IRow G2012 := ⟨[], [bF, r8, r20], naF, i_na⟩
def rowinna : IRow G2012 := ⟨[], [bF, r8, r20], nnaF, i_nna⟩
def rowi11s : IRow G2012 :=
  ⟨[bF], FRJ.sdiff (FRJ.cap [bF, r8, r20] [bF, r8, r20]) [bF], r11, i11s⟩

def ΓQ : List Form :=
  joinCtxOrP (istF rowia [rowina, rowinna, rowi11s])
    (ithF rowia [rowina, rowinna, rowi11s])
    (irhsF rowia [rowina, rowinna, rowi11s]) (fun _ : Fin 1 => Γ2)

theorem hJ5Q : ∀ Y : Form,
    Form.circ Y ∈
      unionAll (fun j => circPart (istF rowia [rowina, rowinna, rowi11s] j)) →
    ∃ i : Fin 1, Clo ((fun _ : Fin 1 => Γ2) i) Y := by
  intro Y hY
  rw [show (unionAll fun j =>
      circPart (istF rowia [rowina, rowinna, rowi11s] j)) = [bF]
    from by decide] at hY
  have h := List.mem_singleton.mp hY
  rw [show bF = Form.circ naF from rfl] at h
  injection h with h'
  subst h'
  exact ⟨0, cloB_iff.mp (by decide)⟩

def Q : FRJVr G2012 (.chain .bot) ΓQ r4 :=
  .joinOrP (k := 0) (tps := fun _ => .barren) (Δs := fun _ => Γ2)
    (Ds := fun _ => .bot)
    (ipremF rowia [rowina, rowinna, rowi11s]) (fun _ => R2) (by decide)
    (hJ2_of_impAnteB (by decide))
    hJ5Q (by decide)
    (Or.inr ⟨rfl, fun _ => ⟨rfl, Or.inl rfl⟩⟩) ⟨by decide, by decide⟩
    (by decide) (CtxEq.refl _)

/-- `· ; ρ8, ρ20 → ρ11` — ρ11's cone-failure through the world-1 join. -/
def i11r : FRJVi G2012 [] [r8, r20] r11 :=
  .impNotIn Q (by decide) (by decide) (by decide) (by decide)

/-! The root `b`-refuting join: barren `⋈^◯` over the four st-empty
rows.  Υ = {a, ¬a, ¬¬a, ρ11}; the kept chain adopts ρ8 (ante ¬¬a ∈ Υ)
and ρ20 (ante ρ11 ∈ Υ); the body condition is `RefAt ¬a` by `ups`. -/

def rowr11 : IRow G2012 := ⟨[], [r8, r20], r11, i11r⟩

def BROOT := FRJVr.joinCirc (G := G2012) (Z := naF)
    (ipremF rowia [rowina, rowinna, rowr11]) (by decide)
    (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide)
    (CtxEq.refl _)

def ROOT := FRJVr.impIn (G := G2012) (A := r8) (B := bF) BROOT
    (by decide) (by decide)

def goal := FRJVr.impIn (G := G2012) (A := r20) (B := r12) ROOT
    (by decide) (by decide)

end W2012

/-- **The repaired calculus derives the refutation sequent for
`ρ20 ⊢? ρ13`** — hand-built. -/
theorem provableV_2012 : FRJ.ProvableV G2012 := ⟨.barren, _, ⟨W2012.goal⟩⟩

/-- info: 'FRJ.WitnessV2012.provableV_2012' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_2012

end FRJ.WitnessV2012
