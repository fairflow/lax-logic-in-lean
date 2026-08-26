/-
# Interactive FRJ◯ construction, rules only: `[ρ11] ⊬ ρ4` inside FRJV

    G114 = (b ⊃ ρ4) ⊃ (a ∨ ¬a)        (a = ◯⊥, b = ◯¬a, ρ4 = a ∨ ¬a)

The exercise (Matthew, 2026-08-26): start from the goal — an element of
the inductive type of FRJ◯ derivations concluding the sequent to refute
— and assemble it rule by rule, choosing each rule by hand.  The
`trace_state` checkpoints print the ACTUAL proofview after each rule
application; the context of the root sequent starts as a metavariable
and is SOLVED by unification as the rules apply.

The plan (world-per-join, from the banked 2-layer countermodel: a root
forcing only ρ11 vacuously, one a-world above it whose cone ends
fallible):

    R1    Ax^I ⊥            · ; Ĝ → ⊥          (the fallible end)
    Ta    ⊃∈ⁱ Λ={a}         a ; Ĝ∖{a} → ¬a     (assume a)
    R3a   ⋈^At_F {Ta}       [blocked] a ⇒ ⊥    (the a-world)
    i_na  ⊃∉ R3a (A=a)      · ; ρ11 → ¬a       (¬a fails in its cone)
    ROOT  ⋈^∨ {i_na}        [barren] ρ11 ⇒ a ∨ ¬a
                             (RefAt a by the ◯-clause over ⊥;
                              RefAt ¬a by ups; kept chain adopts ρ11,
                              its antecedent b RefAt-refuted through
                              circ over ups ¬a)
    goal  ⊃∈ ROOT           [barren] ρ11 ⇒ G114
-/
import FRJ.WitnessV1215
import FRJ.WitnessKit

set_option maxRecDepth 4000

open FRJ Form

namespace FRJ.Interactive114


def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def r4 : Form := .or aF naF
def r11 : Form := .imp bF r4
def G114 : Form := .imp r11 r4

def Θax : List Form := FRJ.rm (gAt G114) .bot ++ gImp G114 ++ gCirc G114

/-! ## Stage 1 — the irregular substrate, built with the same
goal-first discipline (each is its own inductive-type inhabitation) -/

/-- `· ; Ĝ → ⊥` -/
def R1 : FRJVi G114 [] Θax .bot := by
  refine .axI .bot ?prime ?goal ?ctx
  case prime => decide      -- ⊥ is prime
  case goal => decide       -- ⊥ ∈ sfR G114
  case ctx => exact CtxEq.refl _

/-- `a ; Ĝ∖{a} → ¬a` — assume the antecedent `a`, retarget to `¬a`. -/
def Ta : FRJVi G114 [aF] (FRJ.sdiff Θax [aF]) naF := by
  refine .impInI (Th := FRJ.sdiff Θax [aF]) (Lam := [aF]) R1
    ?split ?disj ?ante ?goal ?st ?th
  case split => exact FRJ.zoneSplit (by decide)  -- Θax ≐ (Θax∖{a}) ++ {a}
  case disj => exact cap_sdiff_eq_nil        -- the split is disjoint
  case ante => decide                        -- Clo ({a}) a
  case goal => decide                        -- ¬a ∈ sfR G114
  case st => exact CtxEq.refl _
  case th => exact CtxEq.refl _

/-- `[blocked] a ⇒ ⊥` — the a-world; blocked because `a = ◯⊥`'s cone
ends fallible. -/
def R3a : FRJVr G114 .blocked
    (joinCtxAtF (fun _ : Fin 1 => [aF]) (fun _ : Fin 1 => FRJ.sdiff Θax [aF])
      (fun _ : Fin 1 => naF) .bot) .bot := by
  refine .joinAtF (n := 0) (F := .bot)
    (stab := fun _ => [aF]) (th := fun _ => FRJ.sdiff Θax [aF])
    (rhs := fun _ => naF) (fun _ => Ta) ?J1 ?J2 ?prime ?notat ?goal ?ctx
  case J1 => decide                          -- the one-row (J1) is refl
  case J2 => exact hJ2_of_impAnteB (by decide)  -- Σ^imp is empty
  case prime => decide
  case notat => decide                       -- ⊥ ∉ Σ^at
  case goal => decide
  case ctx => exact CtxEq.refl _

/-- `· ; ρ11 → ¬a` — `¬a` fails in the a-world's cone; the Θ-zone `{ρ11}`
is `Clo`-closed there (`a` gives `ρ4` by ∨-intro, then the consequent
clause). -/
def i_na : FRJVi G114 [] [r11] naF := by
  refine .impNotIn R3a ?Th ?ante ?antenot ?goal
  case Th => decide          -- Clo Γ3a ρ11 ∧ ρ11 ∈ Ĝ
  case ante => decide        -- Clo Γ3a a  (a is IN the blocked context)
  case antenot => decide     -- ¬ Clo {ρ11} a
  case goal => decide

/-! ## Stage 2 — THE GOAL, opened with metavariables

`ProvableV G114` asks for a tag, a context, and an inhabitant of the
derivation type concluding `G114`.  The context is a metavariable until
the join's `CtxEq.refl` solves it. -/

theorem provableV_114 : FRJ.ProvableV G114 := by
  refine ⟨.barren, ?Γ, ⟨?deriv⟩⟩
  case deriv =>
  -- ⊢ FRJVr G114 .barren ?Γ G114   — G114 is an implication: only ⊃∈
  --   concludes one, demanding its antecedent Clo-derivable in context
    refine .impIn (A := r11) (B := r4) ?root ?ante ?goal
    case goal => decide
    case root =>
    -- ⊢ FRJVr G114 .barren ?Γ (a ∨ ¬a) — an ∨-conclusion at barren tag:
    --   the V-join ⋈^∨, single-premise family {i_na}, kept via keptOf
      trace_state
      refine .joinOr (n := 0) (stab := fun _ => []) (th := fun _ => [r11])
        (rhs := fun _ => naF)
        (kept := keptOf (upsilon (fun _ : Fin 1 => naF))
          (joinCtxOrVBase (fun _ : Fin 1 => []) (fun _ : Fin 1 => [r11]))
          (thPool (fun _ : Fin 1 => [r11])))
        (fun _ => i_na)
        ?J1 ?J2 ?circ ?kept ?disj ?goal2 ?ctx
      case J1 => decide
      case J2 => exact hJ2_of_impAnteB (by decide)
      case circ => decide          -- no stable ◯-zone
      case kept => exact keptOf_ok _ _ _   -- greedy chain: adopts ρ11
      case disj =>
      -- ⊢ RefAt true Υ ctx a ∧ RefAt true Υ ctx ¬a,  Υ = {¬a}
        trace_state
        constructor
        · -- RefAt a = ◯⊥: the ◯-clause over the ⊥-clause — cone-refuted
          -- at ANY barren root, no premise needed
          exact .circ rfl .bot
        · -- RefAt ¬a: `ups` — ¬a IS the premise family's right formula
          exact .ups (by decide)
      case goal2 => decide
      case ctx => trace_state; exact CtxEq.refl _
    case ante =>
    -- ⊢ Clo ?Γ r11 — the context is NOW solved (base ++ keptOf …);
    --   the kept chain adopted ρ11, so `Clo` closes it from the base clause
      trace_state
      exact cloB_iff.mp (by decide)

/-- info: 'FRJ.Interactive114.provableV_114' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_114

end FRJ.Interactive114
