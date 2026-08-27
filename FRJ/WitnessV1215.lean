/-
# The repaired calculus derives the ρ-order cell `[ρ12] ⊢ ρ15`

The single remaining open cell of the 462-cell ρ-order matrix is

    G1215 = ((¬¬◯⊥ ⊃ ◯⊥) ⊃ ◯¬◯⊥) ⊃ ((◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥)) ∨ ◯¬◯⊥)

This file hand-builds a kernel-checked derivation in the repaired
calculus `FRJVr`/`FRJVi` (`FRJ/CalculusV.lean`), following the
saturated-database tree of the `ρ12⊃ρ15` section of
`wip/frjx_cell1215_out.txt`, on the model of `wip/frjv_witness.lean`.

The load-bearing repairs on display:
* the kept zone of the barren `⋈^At` (`KeptChain` via the greedy
  `keptOf`), which at world `Rν` retains `¬◯⊥` from the `Ax^I` zone
  although its antecedent `◯⊥` is no premise right formula — the
  `RefAt` `◯`-clause certifies it at any barren root — and at `W1`
  retains `¬¬◯⊥` and then `ρ12`;
* the promise `⋈^∨` (`joinOrP`) over the barren world `Rν`, whose
  promise-kept modal zone carries `◯¬◯⊥` into the conclusion; and
* the `RefAt` disjunct condition of `⋈^∨` at the root, which certifies
  `◯¬◯⊥` through the `◯`-clause — the paper's `C ∈ Υ` cannot.

DEVIATION from the planned tree (reason recorded): the G80/G81 bottom
layer's `T2` (`ν ; Ĝ∖{ν} → δ`) is INADMISSIBLE at `G := G1215`, since
`δ = ¬¬◯⊥` is only a LEFT subformula here (`decide (δ ∈ sfR G1215) =
false`; in G80/G81 the right disjunct `δ` of `ρ9`/`ρ6` supplied the
right occurrence).  Hence `Rν` is not the planned `⋈^At {T2, R2}`: it
is `⋈^At {R1}` alone, with `ν` entering through the KEPT zone rather
than through `Σ^imp` — the same context up to `≐`, and `R2`/`T2` drop
out of the derivation entirely.

HOISTED from `wip/frjv_witness_1215.lean` (2026-08-25, same session) so
the consequence layer is admissible to wip-free closures (`RNDB.DB`).
-/
import FRJ.WitnessKit

set_option maxRecDepth 4000

open FRJ Form

namespace FRJ.WitnessV1215

/-! ## The cell -/

def β : Form := .circ .bot
def ν : Form := .imp β .bot
def σ : Form := .circ ν
def δ : Form := .imp ν .bot
def ι : Form := .imp δ β
def ρ12 : Form := .imp ι σ
def q8 : Form := .imp σ (.or β ν)
def ρ15 : Form := .or q8 σ
def G1215 : Form := .imp ρ12 ρ15

/-! ## Helpers — hoisted to `FRJ/WitnessKit.lean` (2026-08-26); this
file keeps only the witness itself. -/

/-! ## The witness

Bottom-up (all sequents at `G := G1215`; contexts up to `≐`):

    R1   Ax^I ⊥        · ; Ĝ → ⊥
    Tν   ⊃∈ⁱ Λ={β}     β ; Ĝ∖{β} → ν
    R3   ⋈^At_F {Tν}   [blocked] δ, β, σ ⇒ ⊥
    i1   ⊃∉ R3         · ; ρ12, δ, σ → ν
    Rν   ⋈^At {R1}     [barren] ν ⇒ ⊥          (kept chain: ν, via the
                        `RefAt` ◯-clause on its antecedent β = ◯⊥)
    iβ   ◯∉ Rν         · ; ρ12, ν, σ → ◯⊥ (= β)
    Q    ⋈^∨,p {iβ,i1} promise {Rν}
                        [chain ⊥] σ ⇒ ◯⊥ ∨ ¬◯⊥   (σ = the promise-kept
                        modal zone; Υ = {β, ν})
    i4   ⊃∉ Q          · ; ρ12 → q8
    W1   ⋈^At {i1}     [barren] ρ12, δ ⇒ ⊥      (kept chain: δ, then ρ12)
    W2   ◯∈ W1         [barren] ρ12, δ ⇒ ◯⊥ (= β)
    i3   ⊃∉ W2         · ; ρ12 → ι
    ROOT ⋈^∨ {i1,i4,i3} [barren] ρ12 ⇒ q8 ∨ σ (= ρ15)   (kept: ρ12;
         RefAt q8 by the Υ-clause, RefAt σ by the ◯-clause)
    goal ⊃∈ ROOT       [barren] ρ12 ⇒ G1215
-/

namespace W1215

/-- The `Ax^I` second zone of `G1215`. -/
def Θax : List Form := FRJ.rm (gAt G1215) .bot ++ gImp G1215 ++ gCirc G1215

def R1 : FRJVi G1215 [] Θax .bot :=
  .axI .bot (by decide) (by decide) (CtxEq.refl _)

def Tν : FRJVi G1215 [β] (FRJ.sdiff Θax [β]) ν :=
  .impInI (Th := FRJ.sdiff Θax [β]) (Lam := [β]) R1
    (zoneSplit (by decide)) cap_sdiff_eq_nil
    (by decide) (by decide) (CtxEq.refl _) (CtxEq.refl _)

def R3 := FRJVr.joinAtF (G := G1215) (n := 0)
    (stab := fun _ => [β]) (th := fun _ => FRJ.sdiff Θax [β])
    (rhs := fun _ => ν) (F := .bot)
    (fun _ => Tν) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (by decide) (by decide) (CtxEq.refl _)

def i1 : FRJVi G1215 [] [ρ12, δ, σ] ν :=
  .impNotIn R3 (by decide) (by decide) (by decide) (by decide)

/-! The barren world `Rν` (`[barren] ν ⇒ ⊥`): a single-premise `⋈^At`
over `R1` alone.  Its kept chain adopts `ν = ◯⊥ ⊃ ⊥` from the `Ax^I`
pool — the antecedent `◯⊥` is `RefAt`-refuted at any barren root by the
`◯`-clause over `⊥`.  This is the repair the paper's `Θ^⊃/Υ` cannot
imitate (`◯⊥` is no premise right formula), and the context `Γν ≐ {ν}`
is what makes `◯¬◯⊥` promise-keepable at `Q` below. -/

def baseν : List Form :=
  joinCtxAtVBase (fun _ : Fin 1 => []) (fun _ : Fin 1 => Θax) .bot

def keptν : List Form :=
  keptOf (upsilon (fun _ : Fin 1 => Form.bot)) baseν
    (thPool (fun _ : Fin 1 => Θax))

def Γν : List Form := baseν ++ keptν

def Rν : FRJVr G1215 .barren Γν .bot :=
  .joinAt (n := 0) (F := .bot) (stab := fun _ => [])
    (th := fun _ => Θax) (rhs := fun _ => .bot) (kept := keptν)
    (fun _ => R1) (by decide) (hJ2R_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

/-- The `◯∉` zone at `Rν`: everything of `Ĝ` the context `Γν ≐ {ν}`
closes over — `ν` itself, `σ = ◯ν`, and `ρ12` (whose consequent is
`σ`). -/
def Θβ : List Form := (gHat G1215).filter (cloB Γν)

def iβ : FRJVi G1215 [] Θβ β :=
  .circNotIn Rν (Or.inl rfl) (by decide) (by decide)

/-! The promise `⋈^∨`: premise family `{iβ, i1}` (so `Υ = {β, ν}`),
promise family `{Rν}` (rhs `⊥`, tag barren — so the conclusion's tag is
`chain ⊥`).  The conclusion context is the promise-restricted former;
its one member is `σ`, kept by the modal zone because `Rν`'s closure
contains the body `ν`. -/

def rowiβ : IRow G1215 := ⟨[], Θβ, β, iβ⟩
def rowi1 : IRow G1215 := ⟨[], [ρ12, δ, σ], ν, i1⟩

def ΓQ : List Form :=
  joinCtxOrP (istF rowiβ [rowi1]) (ithF rowiβ [rowi1]) (irhsF rowiβ [rowi1])
    (fun _ : Fin 1 => Γν)

def Q : FRJVr G1215 (.chain .bot) ΓQ (.or β ν) :=
  .joinOrP (k := 0) (tps := fun _ => .barren) (Δs := fun _ => Γν)
    (Ds := fun _ => .bot)
    (ipremF rowiβ [rowi1]) (fun _ => Rν) (by decide)
    (hJ2_of_impAnteB (by decide)) (hJ5_of_nil (by decide)) (by decide)
    (Or.inr ⟨rfl, fun _ => ⟨rfl, Or.inl rfl⟩⟩) ⟨by decide, by decide⟩
    (by decide) (CtxEq.refl _)

def i4 : FRJVi G1215 [] [ρ12] q8 :=
  .impNotIn Q (by decide) (by decide) (by decide) (by decide)

def W1 := FRJVr.joinAt (G := G1215) (n := 0) (F := .bot)
    (stab := fun _ => []) (th := fun _ => [ρ12, δ, σ]) (rhs := fun _ => ν)
    (fun _ => i1) (by decide) (hJ2R_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

def W2 := FRJVr.circIn W1 (Or.inl rfl) (by decide)

def i3 : FRJVi G1215 [] [ρ12] ι :=
  .impNotIn W2 (by decide) (by decide) (by decide) (by decide)

def row1 : IRow G1215 := ⟨[], [ρ12, δ, σ], ν, i1⟩
def row4 : IRow G1215 := ⟨[], [ρ12], q8, i4⟩
def row3 : IRow G1215 := ⟨[], [ρ12], ι, i3⟩

def ROOT := FRJVr.joinOr (G := G1215) (C₁ := q8) (C₂ := σ)
    (ipremF row1 [row4, row3]) (by decide) (hJ2R_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) ⟨by decide, by decide⟩ (by decide)
    (CtxEq.refl _)

def goal := FRJVr.impIn (G := G1215) (A := ρ12) (B := ρ15) ROOT
    (by decide) (by decide)

end W1215

/-! ## The witness -/

/-- **The repaired calculus derives the refutation sequent for the cell
`ρ12 ⊢? ρ15`** — the last open cell of the ρ-order matrix; through
`soundnessV` this settles the cell NEGATIVELY. -/
theorem provableV_1215 : FRJ.ProvableV G1215 := ⟨.barren, _, ⟨W1215.goal⟩⟩

/-- info: 'FRJ.WitnessV1215.provableV_1215' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_1215

end FRJ.WitnessV1215