/-
# Interactive FRJ◯ construction II: `[ρ9] ⊬ ρ4` — promise join + Ax^I◯

    G94 = (b ∨ ¬¬a) ⊃ (a ∨ ¬a)

The second rules-only exercise, covering the two rule families the
first (`wip/frjv_interactive_114.lean`) did not touch:

* the PROMISE `⋈^∨` (`joinOrP`) as the load-bearing device — the root
  forces `ρ9` through `b = ◯¬a`, and only the promise join's modal kept
  zone can carry `b` into a context;
* the vacuous `Ax^I◯` (`axIC`) — the `a = ◯⊥`-row is built from the
  classical theory of the ⊥-refuting final world (`vacZoneA`), NOT from
  the `◯∉` route used before.  `classForce [] ⊥ = false` is its licence.

THE TACTIC KIT (the answer to "did any tactics emerge"): every side
condition in all five hand witnesses was discharged by one of seven
closed moves.  `frjv_side` packages them; a rule application is then
`refine Rule (…premises…) <;> all_goals frjv_side` — one line per node.

Tree (contexts up to `≐`):

    R1    Ax^I ⊥              · ; Ĝ → ⊥
    Ta    ⊃∈ⁱ Λ={a}           a ; Ĝ∖{a} → ¬a
    R3a   ⋈^At_F {Ta}         [blocked] ¬¬a, a, b ⇒ ⊥      (a-world)
    i_na  ⊃∉ R3a (A=a)        · ; b → ¬a
    R2    ⋈^At {R1}           [barren] ¬a ⇒ ⊥              (¬a-world)
    i_ac  Ax^I◯ ⊥             · ; ¬a, b → a                (VACUOUS)
    Q     ⋈^∨,p {i_ac,i_na} promise {R2}
                              [chain ⊥] b ⇒ a ∨ ¬a (= ρ4)  (root's row)
    goal  ⊃∈ Q (A=ρ9)         [chain ⊥] b ⇒ G94   (Clo {b} ρ9 by ∨-intro)
-/
import FRJ.WitnessV1215

set_option maxRecDepth 4000

open FRJ Form

namespace FRJ.Interactive94

open FRJ.WitnessV1215 (decSubForm zoneSplit impAnteB hJ2_of_impAnteB
  hJ5_of_nil IRow istF ithF irhsF ipremF)

def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def nnaF : Form := .imp naF .bot
def r4 : Form := .or aF naF
def r9 : Form := .or bF nnaF
def G94 : Form := .imp r9 r4

def Θax : List Form := FRJ.rm (gAt G94) .bot ++ gImp G94 ++ gCirc G94

/-! ## The tactic that fell out of the witness corpus -/

/-- The seven closed side-condition moves of the FRJV witness corpus, in
cheapest-first order.  Everything a hand witness ever needed that was
not a premise or a genuinely quantified statement. -/
macro "frjv_side" : tactic =>
  `(tactic| first
    | exact CtxEq.refl _
    | exact keptOf_ok _ _ _
    | exact cap_sdiff_eq_nil
    | exact FRJ.WitnessV1215.zoneSplit (by decide)
    | exact FRJ.WitnessV1215.hJ2_of_impAnteB (by decide)
    | exact FRJ.WitnessV1215.hJ5_of_nil (by decide)
    | exact cloB_iff.mp (by decide)
    | decide)

/-! ## The substrate, one line per node -/

def R1 : FRJVi G94 [] Θax .bot := by
  refine .axI .bot ?_ ?_ ?_ <;> all_goals frjv_side

def Ta : FRJVi G94 [aF] (FRJ.sdiff Θax [aF]) naF := by
  refine .impInI (Th := FRJ.sdiff Θax [aF]) (Lam := [aF]) R1 ?_ ?_ ?_ ?_ ?_ ?_ <;>
    all_goals frjv_side

def R3a : FRJVr G94 .blocked
    (joinCtxAtF (fun _ : Fin 1 => [aF]) (fun _ : Fin 1 => FRJ.sdiff Θax [aF])
      (fun _ : Fin 1 => naF) .bot) .bot := by
  refine .joinAtF (n := 0) (F := .bot)
    (stab := fun _ => [aF]) (th := fun _ => FRJ.sdiff Θax [aF])
    (rhs := fun _ => naF) (fun _ => Ta) ?_ ?_ ?_ ?_ ?_ ?_ <;>
    all_goals frjv_side

def i_na : FRJVi G94 [] [bF] naF := by
  refine .impNotIn R3a ?_ ?_ ?_ ?_ <;> all_goals frjv_side

def base2 : List Form :=
  joinCtxAtVBase (fun _ : Fin 1 => []) (fun _ : Fin 1 => Θax) .bot

def kept2 : List Form :=
  keptOf (upsilon (fun _ : Fin 1 => Form.bot)) base2
    (thPool (fun _ : Fin 1 => Θax))

def R2 : FRJVr G94 .barren (base2 ++ kept2) .bot := by
  refine .joinAt (n := 0) (F := .bot) (stab := fun _ => [])
    (th := fun _ => Θax) (rhs := fun _ => .bot) (kept := kept2)
    (fun _ => R1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> all_goals frjv_side

/-- THE Ax^I◯ ROW: `a = ◯⊥` refuted vacuously — its Θ is the classical
theory of the ⊥-refuting final world, `vacZoneA G94 [] ≐ {¬a, b}`. -/
def i_ac : FRJVi G94 [] (vacZoneA G94 []) aF := by
  refine .axIC .bot [] ?_ ?_ ?_ ?_ <;> all_goals frjv_side

/-! ## The goal, metavariable-first; the promise join solves the context -/

def rowac : IRow G94 := ⟨[], vacZoneA G94 [], aF, i_ac⟩
def rowna : IRow G94 := ⟨[], [bF], naF, i_na⟩

theorem provableV_94 : FRJ.ProvableV G94 := by
  refine ⟨.chain .bot, ?Γ, ⟨?deriv⟩⟩
  case deriv =>
    refine .impIn (A := r9) (B := r4) ?root ?ante ?goal
    case goal => frjv_side
    case root =>
    -- ⊢ FRJVr G94 (chain ⊥) ?Γ (a ∨ ¬a):  the PROMISE ⋈^∨ — family
    --   {i_ac, i_na} (Υ = {a, ¬a}), promise {R2} (the ¬a-world, Rm-target)
      trace_state
      refine .joinOrP (k := 0) (tps := fun _ => .barren)
        (Δs := fun _ => base2 ++ kept2) (Ds := fun _ => .bot)
        (ipremF rowac [rowna]) (fun _ => R2)
        ?J1 ?J2 ?J5 ?J7 ?tag ?disj ?goal2 ?ctx
      case J1 => frjv_side
      case J2 => frjv_side
      case J5 => frjv_side       -- hJ5_of_nil: no stable ◯-zone
      case J7 => frjv_side
      case tag => exact Or.inr ⟨rfl, fun _ => ⟨rfl, Or.inl rfl⟩⟩
      case disj =>
      -- ⊢ a ∈ Υ ∧ ¬a ∈ Υ — the promise join's disjunct condition is
      --   plain Υ-membership (no RefAt): both are premise right formulas
        trace_state
        exact ⟨by decide, by decide⟩
      case goal2 => frjv_side
      case ctx => trace_state; exact CtxEq.refl _
    case ante =>
    -- ⊢ Clo ?Γ r9 — ?Γ solved by the join: the promise-restricted
    --   context, whose one member is b; ∨-intro left closes ρ9
      trace_state
      frjv_side

/-- info: 'FRJ.Interactive94.provableV_94' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_94

end FRJ.Interactive94
