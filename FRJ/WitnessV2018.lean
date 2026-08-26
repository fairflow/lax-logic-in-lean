/-
# The repaired calculus derives the ρ-order cell `[ρ20] ⊢? ρ18` — negative

    G2018 = (ρ11 ⊃ ρ6) ⊃ (ρ14 ∨ ρ9)

HAND-BUILT (2026-08-26), same countermodel and top as `WitnessV1918`
(the two cells share the banked 5-world frame).  The one new device:
the hypothesis `ρ20 = ρ11 ⊃ ρ6` cannot ride the promise join's
Υ-restricted implication zone on its own (its antecedent `ρ11` is no
premise right formula there), so the world-1 join's premise family is
ENRICHED to put `ρ11` into Υ itself:

    iOr4 = orI iA i_na          · ; (Θ_iA ∩ Θ_ina) → a ∨ ¬a (= ρ4)
    i11s = ⊃∈ⁱ Λ={b} on iOr4    b ; … → (b ⊃ ρ4) (= ρ11)

`i11s` is a STABLE-`b` row; its `hJ5` obligation (the stable circ `b`)
is discharged by the promise closure `Clo Γ2 ¬a`.  With `ρ11 ∈ Υ` the
zone retains `ρ20`, which then rides `Clo` (consequent `ρ6`, either
disjunct) through every Θ up to the root's kept chain.  Everything else
is the 1918 tree verbatim.
-/
import FRJ.WitnessV1215

set_option maxRecDepth 4000

open FRJ Form

namespace FRJ.WitnessV2018

open FRJ.WitnessV1215 (decSubForm zoneSplit impAnteB hJ2_of_impAnteB
  hJ5_of_nil IRow istF ithF irhsF ipremF)

/-! ## The cell -/

def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def nnaF : Form := .imp naF .bot
def r4 : Form := .or aF naF
def r6 : Form := .or naF nnaF
def r9 : Form := .or bF nnaF
def r11 : Form := .imp bF r4
def r14 : Form := .imp r9 r4
def r18 : Form := .or r14 r9
def r20 : Form := .imp r11 r6
def G2018 : Form := .imp r20 r18

namespace W2018

def Θax : List Form := FRJ.rm (gAt G2018) .bot ++ gImp G2018 ++ gCirc G2018

def R1 : FRJVi G2018 [] Θax .bot :=
  .axI .bot (by decide) (by decide) (CtxEq.refl _)

def Ta : FRJVi G2018 [aF] (FRJ.sdiff Θax [aF]) naF :=
  .impInI (Th := FRJ.sdiff Θax [aF]) (Lam := [aF]) R1
    (zoneSplit (by decide)) cap_sdiff_eq_nil
    (by decide) (by decide) (CtxEq.refl _) (CtxEq.refl _)

def Γ3a : List Form :=
  joinCtxAtF (fun _ : Fin 1 => [aF]) (fun _ : Fin 1 => FRJ.sdiff Θax [aF])
    (fun _ : Fin 1 => naF) .bot

def R3a : FRJVr G2018 .blocked Γ3a .bot :=
  .joinAtF (n := 0) (F := .bot)
    (stab := fun _ => [aF]) (th := fun _ => FRJ.sdiff Θax [aF])
    (rhs := fun _ => naF)
    (fun _ => Ta) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (by decide) (by decide) (CtxEq.refl _)

def i_na : FRJVi G2018 [] [bF, r20] naF :=
  .impNotIn R3a (by decide) (by decide) (by decide) (by decide)

def base2 : List Form :=
  joinCtxAtVBase (fun _ : Fin 1 => []) (fun _ : Fin 1 => Θax) .bot

def kept2 : List Form :=
  keptOf (upsilon (fun _ : Fin 1 => Form.bot)) base2
    (thPool (fun _ : Fin 1 => Θax))

def Γ2 : List Form := base2 ++ kept2

def R2 : FRJVr G2018 .barren Γ2 .bot :=
  .joinAt (n := 0) (F := .bot) (stab := fun _ => [])
    (th := fun _ => Θax) (rhs := fun _ => .bot) (kept := kept2)
    (fun _ => R1) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

def i_nna : FRJVi G2018 [] [r20] nnaF :=
  .impNotIn R2 (by decide) (by decide) (by decide) (by decide)

def iA : FRJVi G2018 [] [naF, bF, r20] aF :=
  .circNotIn R2 (Or.inl rfl) (by decide) (by decide)

/-! The Υ-enrichment: merge, then stabilise `b`. -/

/-- `· ; b, ρ20 → a ∨ ¬a` — the merged `ρ4`-row. -/
def iOr4 : FRJVi G2018 [] (FRJ.cap [naF, bF, r20] [bF, r20]) r4 :=
  .orI iA i_na (by decide) (by decide) (by decide)
    (CtxEq.refl _) (CtxEq.refl _)

/-- `b ; ρ20 → ρ11` — the stable-`b` row that puts `ρ11` into Υ. -/
def i11s : FRJVi G2018 [bF]
    (FRJ.sdiff (FRJ.cap [naF, bF, r20] [bF, r20]) [bF]) r11 :=
  .impInI (Th := FRJ.sdiff (FRJ.cap [naF, bF, r20] [bF, r20]) [bF])
    (Lam := [bF]) iOr4
    (zoneSplit (by decide)) cap_sdiff_eq_nil
    (by decide) (by decide) (CtxEq.refl _) (CtxEq.refl _)

/-! World 1: the promise `⋈^∨` with the enriched family. -/

def rowiA : IRow G2018 := ⟨[], [naF, bF, r20], aF, iA⟩
def rowina : IRow G2018 := ⟨[], [bF, r20], naF, i_na⟩
def rowi11s : IRow G2018 :=
  ⟨[bF], FRJ.sdiff (FRJ.cap [naF, bF, r20] [bF, r20]) [bF], r11, i11s⟩

def ΓQ : List Form :=
  joinCtxOrP (istF rowiA [rowina, rowi11s]) (ithF rowiA [rowina, rowi11s])
    (irhsF rowiA [rowina, rowi11s]) (fun _ : Fin 1 => Γ2)

/-- The non-vacuous (J5): the joint stable modal zone is exactly `{b}`,
and the promise closure `Γ2 ≐ {¬a}` absorbs its body. -/
theorem hJ5Q : ∀ Y : Form,
    Form.circ Y ∈ unionAll (fun j => circPart (istF rowiA [rowina, rowi11s] j)) →
    ∃ i : Fin 1, Clo ((fun _ : Fin 1 => Γ2) i) Y := by
  intro Y hY
  rw [show (unionAll fun j => circPart (istF rowiA [rowina, rowi11s] j)) = [bF]
    from by decide] at hY
  have h := List.mem_singleton.mp hY
  rw [show bF = Form.circ naF from rfl] at h
  injection h with h'
  subst h'
  exact ⟨0, cloB_iff.mp (by decide)⟩

def Q : FRJVr G2018 (.chain .bot) ΓQ r4 :=
  .joinOrP (k := 0) (tps := fun _ => .barren) (Δs := fun _ => Γ2)
    (Ds := fun _ => .bot)
    (ipremF rowiA [rowina, rowi11s]) (fun _ => R2) (by decide)
    (hJ2_of_impAnteB (by decide))
    hJ5Q (by decide)
    (Or.inr ⟨rfl, fun _ => ⟨rfl, Or.inl rfl⟩⟩) ⟨by decide, by decide⟩
    (by decide) (CtxEq.refl _)

def i14 : FRJVi G2018 [] [r20] r14 :=
  .impNotIn Q (by decide) (by decide) (by decide) (by decide)

def i11top : FRJVi G2018 [] [r20] r11 :=
  .impNotIn Q (by decide) (by decide) (by decide) (by decide)

def row14 : IRow G2018 := ⟨[], [r20], r14, i14⟩
def row11 : IRow G2018 := ⟨[], [r20], r11, i11top⟩
def rowna : IRow G2018 := ⟨[], [bF, r20], naF, i_na⟩
def rownna : IRow G2018 := ⟨[], [r20], nnaF, i_nna⟩

def ROOT := FRJVr.joinOr (G := G2018) (C₁ := r14) (C₂ := r9)
    (ipremF row14 [row11, rowna, rownna]) (by decide)
    (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) ⟨by decide, by decide⟩ (by decide)
    (CtxEq.refl _)

def goal := FRJVr.impIn (G := G2018) (A := r20) (B := r18) ROOT
    (by decide) (by decide)

end W2018

/-- **The repaired calculus derives the refutation sequent for
`ρ20 ⊢? ρ18`** — hand-built. -/
theorem provableV_2018 : FRJ.ProvableV G2018 := ⟨.barren, _, ⟨W2018.goal⟩⟩

/-- info: 'FRJ.WitnessV2018.provableV_2018' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_2018

end FRJ.WitnessV2018
