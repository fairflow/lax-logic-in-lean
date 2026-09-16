/-
# The repaired calculus derives the incompleteness cells #80 and #81

HOISTED from `wip/frjv_witness.lean` (2026-08-25, same session) so the
consequence layer is admissible to wip-free closures (`RNDB.DB`).

The paper family `FRJr`/`FRJi` provably misses

    G80 = ((¬¬◯⊥ ⊃ ◯⊥) ⊃ ◯¬◯⊥) ⊃ (◯¬◯⊥ ∨ ¬¬◯⊥)
    G81 = ((¬¬◯⊥ ⊃ ◯⊥) ⊃ (◯⊥ ∨ ¬◯⊥)) ⊃ (¬◯⊥ ∨ ¬¬◯⊥)

(`wip/frj80_noprov.lean`, `wip/frj81_noprov.lean`).  This file hand-builds
kernel-checked derivations in the REPAIRED calculus `FRJVr`/`FRJVi`
(`FRJ/CalculusV.lean`), following the saturated-database trees of
`wip/frjx_cells_out.txt`: the `RefAt`-relaxed joins derive both cells.

The load-bearing repairs on display:
* the kept zone of the barren `⋈^At` (`KeptChain` via the greedy
  `keptOf`), which retains `δ` and then `ρ` at world `W1` although their
  antecedents are not premise right formulas; and
* the `RefAt` disjunct condition of `⋈^∨` at the root, which certifies
  `◯¬◯⊥` through the `◯`-clause (cell #80) — the paper's `C ∈ Υ` cannot.
-/
import FRJ.CalculusV

set_option maxRecDepth 4000

open FRJ Form

namespace FRJ.WitnessV

/-! ## The two cells -/

def β : Form := .circ .bot
def ν : Form := .imp β .bot
def σ : Form := .circ ν
def δ : Form := .imp ν .bot
def ι : Form := .imp δ β
def ρ12 : Form := .imp ι σ
def ρ9  : Form := .or σ δ
def G80 : Form := .imp ρ12 ρ9
def ρ13 : Form := .imp ι (.or β ν)
def ρ6  : Form := .or ν δ
def G81 : Form := .imp ρ13 ρ6

/-! ## Helpers -/

/-- Subset of formula lists is decidable (a bounded `∀`). -/
instance decSubForm (l m : List Form) : Decidable (l ⊆ m) :=
  decidable_of_iff (∀ x ∈ l, x ∈ m)
    ⟨fun h _ hx => h _ hx, fun h _ hx => h hx⟩

/-- Local copy of `FRJ.Search.zone_split` (importing the engine here would
drag the whole search stack into the witness). -/
theorem zoneSplit {Θ Λ : List Form} (hΛ : ∀ x ∈ Λ, x ∈ Θ) :
    Θ ≐ FRJ.sdiff Θ Λ ++ Λ := by
  intro x
  constructor
  · intro h
    by_cases hl : x ∈ Λ
    · exact List.mem_append_right _ hl
    · exact List.mem_append_left _ (mem_sdiff.mpr ⟨h, hl⟩)
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact (mem_sdiff.mp h).1
    · exact hΛ _ h

/-- Boolean form of the joins' (J2): every implication of `l` has its
antecedent in `Υ`. -/
def impAnteB (Υ l : List Form) : Bool :=
  l.all fun f => match f with | .imp A _ => decide (A ∈ Υ) | _ => true

theorem hJ2_of_impAnteB {Υ l : List Form} (h : impAnteB Υ l = true) :
    ∀ A B : Form, Form.imp A B ∈ l → A ∈ Υ := fun _ _ hm =>
  of_decide_eq_true (List.all_eq_true.mp h _ hm)

/-- A derived irregular row, packaged so a mixed premise family can be
indexed by `Fin (n+1)` definitionally (the engine's `stabF` pattern). -/
structure IRow (G : Form) where
  st : List Form
  th : List Form
  rhs : Form
  der : FRJVi G st th rhs

def istF {G : Form} (a : IRow G) (rest : List (IRow G)) :
    Fin (rest.length + 1) → List Form := fun j => ((a :: rest).get j).st

def ithF {G : Form} (a : IRow G) (rest : List (IRow G)) :
    Fin (rest.length + 1) → List Form := fun j => ((a :: rest).get j).th

def irhsF {G : Form} (a : IRow G) (rest : List (IRow G)) :
    Fin (rest.length + 1) → Form := fun j => ((a :: rest).get j).rhs

def ipremF {G : Form} (a : IRow G) (rest : List (IRow G)) :
    ∀ j, FRJVi G (istF a rest j) (ithF a rest j) (irhsF a rest j) :=
  fun j => ((a :: rest).get j).der

/-! ## Witness for cell #80

Bottom-up (all sequents at `G := G80`; contexts up to `≐`):

    R1   Ax^I ⊥        · ; Ĝ → ⊥
    T2   ⊃∈ⁱ Λ={ν}     ν ; Ĝ∖{ν} → δ
    Tν   ⊃∈ⁱ Λ={β}     β ; Ĝ∖{β} → ν
    R2   Ax^I◯ ⊥, ∅    · ; vacZone → ◯⊥ (= β)
    R3   ⋈^At_F {Tν}   [blocked] δ, β, σ ⇒ ⊥
    i1   ⊃∉ R3         · ; ρ12, δ, σ → ν
    R4   ⋈^At {T2,R2}  [barren] ν ⇒ ⊥
    i2   ⊃∉ R4         · ; ρ12, σ → δ
    W1   ⋈^At {i1}     [barren] ρ12, δ ⇒ ⊥      (kept chain: δ, then ρ12)
    W2   ◯∈ W1         [barren] ρ12, δ ⇒ ◯⊥ (= β)
    i3   ⊃∉ W2         · ; ρ12 → ι
    ROOT ⋈^∨ {i1,i2,i3} [barren] ρ12 ⇒ σ ∨ δ (= ρ9)   (kept: ρ12;
         RefAt σ by the ◯-clause, RefAt δ by the Υ-clause)
    goal ⊃∈ ROOT       [barren] ρ12 ⇒ G80
-/

namespace W80

/-- The `Ax^I` second zone of `G80`. -/
def Θax : List Form := FRJ.rm (gAt G80) .bot ++ gImp G80 ++ gCirc G80

def R1 : FRJVi G80 [] Θax .bot :=
  .axI .bot (by decide) (by decide) (CtxEq.refl _)

def T2 : FRJVi G80 [ν] (FRJ.sdiff Θax [ν]) δ :=
  .impInI (Th := FRJ.sdiff Θax [ν]) (Lam := [ν]) R1
    (zoneSplit (by decide)) cap_sdiff_eq_nil
    (by decide) (by decide) (CtxEq.refl _) (CtxEq.refl _)

def Tν : FRJVi G80 [β] (FRJ.sdiff Θax [β]) ν :=
  .impInI (Th := FRJ.sdiff Θax [β]) (Lam := [β]) R1
    (zoneSplit (by decide)) cap_sdiff_eq_nil
    (by decide) (by decide) (CtxEq.refl _) (CtxEq.refl _)

def R2 : FRJVi G80 [] (vacZoneA G80 []) (.circ .bot) :=
  .axIC .bot [] (by decide) (by decide) (by decide) (CtxEq.refl _)

def R3 := FRJVr.joinAtF (G := G80) (n := 0)
    (stab := fun _ => [β]) (th := fun _ => FRJ.sdiff Θax [β])
    (rhs := fun _ => ν) (F := .bot)
    (fun _ => Tν) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (by decide) (by decide) (CtxEq.refl _)

def i1 : FRJVi G80 [] [ρ12, δ, σ] ν :=
  .impNotIn R3 (by decide) (by decide) (by decide) (by decide)

def rowT2 : IRow G80 := ⟨[ν], FRJ.sdiff Θax [ν], δ, T2⟩
def rowR2 : IRow G80 := ⟨[], vacZoneA G80 [], .circ .bot, R2⟩

def R4 := FRJVr.joinAt (G := G80) (F := .bot)
    (ipremF rowT2 [rowR2]) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

def i2 : FRJVi G80 [] [ρ12, σ] δ :=
  .impNotIn R4 (by decide) (by decide) (by decide) (by decide)

def W1 := FRJVr.joinAt (G := G80) (n := 0) (F := .bot)
    (stab := fun _ => []) (th := fun _ => [ρ12, δ, σ]) (rhs := fun _ => ν)
    (fun _ => i1) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

def W2 := FRJVr.circIn W1 (Or.inl rfl) (by decide)

def i3 : FRJVi G80 [] [ρ12] ι :=
  .impNotIn W2 (by decide) (by decide) (by decide) (by decide)

def row1 : IRow G80 := ⟨[], [ρ12, δ, σ], ν, i1⟩
def row2 : IRow G80 := ⟨[], [ρ12, σ], δ, i2⟩
def row3 : IRow G80 := ⟨[], [ρ12], ι, i3⟩

def ROOT := FRJVr.joinOr (G := G80) (C₁ := σ) (C₂ := δ)
    (ipremF row1 [row2, row3]) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) ⟨by decide, by decide⟩ (by decide)
    (CtxEq.refl _)

def goal := FRJVr.impIn (G := G80) (A := ρ12) (B := ρ9) ROOT
    (by decide) (by decide)

end W80

/-! ## Witness for cell #81

The same tree shape at `G := G81` (`σ` is not in this cell's universe;
`ρ13` replaces `ρ12`, `ρ6 = ν ∨ δ` replaces `ρ9`, and at the root both
disjuncts are premise right formulas — no `◯`-clause needed). -/

namespace W81

def Θax : List Form := FRJ.rm (gAt G81) .bot ++ gImp G81 ++ gCirc G81

def R1 : FRJVi G81 [] Θax .bot :=
  .axI .bot (by decide) (by decide) (CtxEq.refl _)

def T2 : FRJVi G81 [ν] (FRJ.sdiff Θax [ν]) δ :=
  .impInI (Th := FRJ.sdiff Θax [ν]) (Lam := [ν]) R1
    (zoneSplit (by decide)) cap_sdiff_eq_nil
    (by decide) (by decide) (CtxEq.refl _) (CtxEq.refl _)

def Tν : FRJVi G81 [β] (FRJ.sdiff Θax [β]) ν :=
  .impInI (Th := FRJ.sdiff Θax [β]) (Lam := [β]) R1
    (zoneSplit (by decide)) cap_sdiff_eq_nil
    (by decide) (by decide) (CtxEq.refl _) (CtxEq.refl _)

def R2 : FRJVi G81 [] (vacZoneA G81 []) (.circ .bot) :=
  .axIC .bot [] (by decide) (by decide) (by decide) (CtxEq.refl _)

def R3 := FRJVr.joinAtF (G := G81) (n := 0)
    (stab := fun _ => [β]) (th := fun _ => FRJ.sdiff Θax [β])
    (rhs := fun _ => ν) (F := .bot)
    (fun _ => Tν) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (by decide) (by decide) (CtxEq.refl _)

def i1 : FRJVi G81 [] [ρ13, δ] ν :=
  .impNotIn R3 (by decide) (by decide) (by decide) (by decide)

def rowT2 : IRow G81 := ⟨[ν], FRJ.sdiff Θax [ν], δ, T2⟩
def rowR2 : IRow G81 := ⟨[], vacZoneA G81 [], .circ .bot, R2⟩

def R4 := FRJVr.joinAt (G := G81) (F := .bot)
    (ipremF rowT2 [rowR2]) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

def i2 : FRJVi G81 [] [ρ13] δ :=
  .impNotIn R4 (by decide) (by decide) (by decide) (by decide)

def W1 := FRJVr.joinAt (G := G81) (n := 0) (F := .bot)
    (stab := fun _ => []) (th := fun _ => [ρ13, δ]) (rhs := fun _ => ν)
    (fun _ => i1) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) (by decide) (by decide) (by decide)
    (CtxEq.refl _)

def W2 := FRJVr.circIn W1 (Or.inl rfl) (by decide)

def i3 : FRJVi G81 [] [ρ13] ι :=
  .impNotIn W2 (by decide) (by decide) (by decide) (by decide)

def row1 : IRow G81 := ⟨[], [ρ13, δ], ν, i1⟩
def row2 : IRow G81 := ⟨[], [ρ13], δ, i2⟩
def row3 : IRow G81 := ⟨[], [ρ13], ι, i3⟩

def ROOT := FRJVr.joinOr (G := G81) (C₁ := ν) (C₂ := δ)
    (ipremF row1 [row2, row3]) (by decide) (hJ2_of_impAnteB (by decide))
    (by decide) (keptOf_ok _ _ _) ⟨by decide, by decide⟩ (by decide)
    (CtxEq.refl _)

def goal := FRJVr.impIn (G := G81) (A := ρ13) (B := ρ6) ROOT
    (by decide) (by decide)

end W81

/-! ## The witnesses -/

/-- **The repaired calculus derives cell #80** — which the paper calculus
provably misses. -/
theorem provableV_G80 : FRJ.ProvableV G80 := ⟨.barren, _, ⟨W80.goal⟩⟩

/-- **The repaired calculus derives cell #81** — which the paper calculus
provably misses. -/
theorem provableV_G81 : FRJ.ProvableV G81 := ⟨.barren, _, ⟨W81.goal⟩⟩

/-- info: 'FRJ.WitnessV.provableV_G80' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_G80

/-- info: 'FRJ.WitnessV.provableV_G81' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_G81

end FRJ.WitnessV
