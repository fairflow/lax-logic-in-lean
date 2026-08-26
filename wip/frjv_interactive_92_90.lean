/-
# Interactive FRJ◯ construction III: the promise-At and promise-Circ joins

    G92 = (b ∨ ¬¬a) ⊃ ◯⊥        — [ρ9] ⊬ ρ2, forces `joinCircP`
    G90 = (b ∨ ¬¬a) ⊃ ⊥         — [ρ9] ⊬ ρ0, forces `joinAtP`

Both cells FORCE their promise join: the final `⊃∈` needs
`Clo ctx ρ9`, which needs `b = ◯¬a` in the refuting row's context, and
only the promise formers' modal kept zone can put a `◯`-formula there.
The conclusions (`◯⊥` prime-circ, `⊥` prime) rule out `joinOrP` — so
the missing two families are exactly what these trees must use.

Both trees are FOUR nodes (no a-world needed: `joinCircP`'s body
condition and `joinAtP`'s conclusion are `⊥`-flavoured, and `⊥ ∈ Υ` is
free through the `Ax^I` row):

    R1    Ax^I ⊥              · ; Ĝ → ⊥
    R2    ⋈^At {R1}           [barren] ¬a ⇒ ⊥       (the ¬a-world)
    ROW   ⋈^◯,p / ⋈^At,p {R1} promise {R2}
                              [chain ⊥] b ⇒ ◯⊥  /  b ⇒ ⊥
    goal  ⊃∈ ROW (A=ρ9)       [chain ⊥] b ⇒ G       (Clo {b} ρ9, ∨-intro)
-/
import FRJ.WitnessKit

set_option maxRecDepth 4000

open FRJ Form

namespace FRJ.Interactive9290

def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def nnaF : Form := .imp naF .bot
def r9 : Form := .or bF nnaF
def G92 : Form := .imp r9 aF
def G90 : Form := .imp r9 .bot

/-! ## `[ρ9] ⊬ ρ2` — the promise `⋈^◯` (`joinCircP`) -/

namespace W92

def Θax : List Form := FRJ.rm (gAt G92) .bot ++ gImp G92 ++ gCirc G92

def R1 : FRJVi G92 [] Θax .bot := by
  refine .axI .bot ?_ ?_ ?_ <;> all_goals frjv_side

def base2 : List Form :=
  joinCtxAtVBase (fun _ : Fin 1 => []) (fun _ : Fin 1 => Θax) .bot

def kept2 : List Form :=
  keptOf (upsilon (fun _ : Fin 1 => Form.bot)) base2
    (thPool (fun _ : Fin 1 => Θax))

def R2 : FRJVr G92 .barren (base2 ++ kept2) .bot := by
  refine .joinAt (n := 0) (F := .bot) (stab := fun _ => [])
    (th := fun _ => Θax) (rhs := fun _ => .bot) (kept := kept2)
    (fun _ => R1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> all_goals frjv_side

end W92

open W92 in
theorem provableV_92 : FRJ.ProvableV G92 := by
  refine ⟨.chain .bot, ?Γ, ⟨?deriv⟩⟩
  case deriv =>
    refine .impIn (A := r9) (B := aF) ?row ?ante ?goal
    case goal => frjv_side
    case row =>
    -- ⊢ FRJVr G92 (chain ⊥) ?Γ ◯⊥ — a ◯-conclusion whose context must
    --   carry b: the PROMISE ⋈^◯, family {R1} (Υ = {⊥}), promise {R2}
      trace_state
      refine .joinCircP (n := 0) (k := 0) (Z := .bot)
        (stab := fun _ => []) (th := fun _ => Θax) (rhs := fun _ => .bot)
        (tps := fun _ => .barren) (Δs := fun _ => base2 ++ kept2)
        (Ds := fun _ => .bot)
        (fun _ => R1) (fun _ => R2) ?J1 ?J2 ?J5 ?J7 ?Ds ?Z ?goal2 ?ctx
      case J1 => frjv_side
      case J2 => frjv_side
      case J5 => frjv_side
      case J7 => frjv_side
      case Ds => exact fun _ => ⟨rfl, Or.inl rfl⟩
      case Z =>
      -- ⊢ ⊥ ∈ Υ — the body condition of the promise ⋈^◯ is plain
      --   Υ-membership, and ⊥ is the Ax^I row's right formula
        trace_state
        frjv_side
      case goal2 => frjv_side
      case ctx => trace_state; exact CtxEq.refl _
    case ante =>
    -- ⊢ Clo ?Γ r9 — solved context = the promise-restricted formers;
    --   its modal zone carries b, and ∨-intro left closes ρ9
      trace_state
      frjv_side

/-! ## `[ρ9] ⊬ ρ0` — the promise `⋈^At` (`joinAtP`) -/

namespace W90

def Θax : List Form := FRJ.rm (gAt G90) .bot ++ gImp G90 ++ gCirc G90

def R1 : FRJVi G90 [] Θax .bot := by
  refine .axI .bot ?_ ?_ ?_ <;> all_goals frjv_side

def base2 : List Form :=
  joinCtxAtVBase (fun _ : Fin 1 => []) (fun _ : Fin 1 => Θax) .bot

def kept2 : List Form :=
  keptOf (upsilon (fun _ : Fin 1 => Form.bot)) base2
    (thPool (fun _ : Fin 1 => Θax))

def R2 : FRJVr G90 .barren (base2 ++ kept2) .bot := by
  refine .joinAt (n := 0) (F := .bot) (stab := fun _ => [])
    (th := fun _ => Θax) (rhs := fun _ => .bot) (kept := kept2)
    (fun _ => R1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> all_goals frjv_side

end W90

open W90 in
theorem provableV_90 : FRJ.ProvableV G90 := by
  refine ⟨.chain .bot, ?Γ, ⟨?deriv⟩⟩
  case deriv =>
    refine .impIn (A := r9) (B := .bot) ?row ?ante ?goal
    case goal => frjv_side
    case row =>
    -- ⊢ FRJVr G90 (chain ⊥) ?Γ ⊥ — a PRIME conclusion whose context
    --   must carry b: the PROMISE ⋈^At, family {R1}, promise {R2}
      trace_state
      refine .joinAtP (n := 0) (k := 0) (F := .bot)
        (stab := fun _ => []) (th := fun _ => Θax) (rhs := fun _ => .bot)
        (tps := fun _ => .barren) (Δs := fun _ => base2 ++ kept2)
        (Ds := fun _ => .bot)
        (fun _ => R1) (fun _ => R2) ?J1 ?J2 ?J5 ?J7 ?tag ?prime ?notat ?goal2 ?ctx
      case J1 => frjv_side
      case J2 => frjv_side
      case J5 => frjv_side
      case J7 => frjv_side
      case tag => exact Or.inr ⟨rfl, fun _ => ⟨rfl, Or.inl rfl⟩⟩
      case prime => frjv_side
      case notat =>
      -- ⊢ ⊥ ∉ Σ^at — the conclusion is no stable atom
        trace_state
        frjv_side
      case goal2 => frjv_side
      case ctx => trace_state; exact CtxEq.refl _
    case ante =>
      trace_state
      frjv_side

/-- info: 'FRJ.Interactive9290.provableV_92' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_92

/-- info: 'FRJ.Interactive9290.provableV_90' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_90

end FRJ.Interactive9290
