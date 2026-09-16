/-
# FRJ◯ W1 — goal-parametrised sequents, the closure, the zones

First stage of `docs/frjo-calculus-plan.md`: the sequent language the
indexed calculus (W2) is stated over.  Everything is parametrised by
the GOAL CELL `Γ₀ ⊢ C₀`, giving the Finite Rule Property for free:
every zone of every sequent is a subset of the finite subformula
closure `sfPlus`.

Design (plan §2, grounded in RK(Ξ) and FRJ(G)):

* `sfPlus`   — the subformula closure of the cell;
* `detPart`  — the DETERMINING part: atoms, ⊥, implications AND boxes
  (the `Cl` screen's forced repair: without boxes, 32 certified
  failures; with them, 0/156);
* `clB`      — the computable PLL-consequence closure over the
  closure, via the repo's bounded G4 searcher (UNTRUSTED here — its
  (Cl1)–(Cl6) properties are W1's named obligations, stated below);
* `Reg`/`Irr` — the two sequent forms with the modal zone `μ`.
-/
import LaxLogic.PLLSearch

namespace FRJO

open PLLND PLLFormula

/-! ## The goal cell and its closure -/

structure Cell where
  ctx : List PLLFormula
  goal : PLLFormula
deriving Repr, DecidableEq

/-- Subformulas, cumulative. -/
def sf : PLLFormula → List PLLFormula
  | .prop a => [.prop a]
  | .falsePLL => [.falsePLL]
  | .and φ ψ => .and φ ψ :: (sf φ ++ sf ψ)
  | .or φ ψ => .or φ ψ :: (sf φ ++ sf ψ)
  | .ifThen φ ψ => .ifThen φ ψ :: (sf φ ++ sf ψ)
  | .somehow φ => .somehow φ :: sf φ

/-- The cell's finite universe. -/
def sfPlus (G : Cell) : List PLLFormula :=
  ((G.goal :: G.ctx).flatMap sf).eraseDups

theorem sf_self (φ : PLLFormula) : φ ∈ sf φ := by
  cases φ <;> simp [sf]

theorem sfPlus_goal (G : Cell) : G.goal ∈ sfPlus G := by
  simp only [sfPlus, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨G.goal, by simp, sf_self _⟩

theorem sfPlus_ctx (G : Cell) : ∀ φ ∈ G.ctx, φ ∈ sfPlus G := by
  intro φ hφ
  simp only [sfPlus, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨φ, by simp [hφ], sf_self _⟩

/-! ## The determining part -/

/-- Non-∧/∨ formulas: atoms, ⊥, implications, boxes.  FRJ's `Λ*` with
the ◯-repair. -/
def determining : PLLFormula → Bool
  | .and _ _ => false
  | .or _ _ => false
  | _ => true

def detPart (Δ : List PLLFormula) : List PLLFormula := Δ.filter determining

/-! ## The computable closure -/

/-- Bounded PLL-consequence over the cell's universe: the formulas of
`sfPlus G` derivable from `Δ`.  UNTRUSTED (the searcher is the
oracle); the closure PROPERTIES are the obligations below, and
soundness of anything built on `clB` is delivered by the extraction
theorem (W3), never by trusting this function. -/
def clB (G : Cell) (budget : Nat) (Δ : List PLLFormula) : List PLLFormula :=
  (sfPlus G).filter fun φ =>
    match Search.decide { findBudget := some budget, emitClosureCap := 0 } Δ φ with
    | .proved _ => true
    | _ => false

/-- A zone is fallible when the closure reaches `⊥`. -/
def fallibleB (G : Cell) (budget : Nat) (Δ : List PLLFormula) : Bool :=
  (clB G budget Δ).contains .falsePLL

/-! ## The sequent forms (plan §2) -/

/-- Regular: "some world forces `stable` and refutes `goal`". -/
structure Reg (G : Cell) where
  stable : List PLLFormula
  goal : PLLFormula
deriving Repr, DecidableEq

/-- Irregular: `Σ ; Θ ; μ → C` — `sigma` holds at the root, `theta`
strictly above it, `mu` is the root's modal zone (on reduced
confluent frames: the maximum `Rₘ`-successor's theory, the promise
world). -/
structure Irr (G : Cell) where
  sigma : List PLLFormula
  theta : List PLLFormula
  mu : List PLLFormula
  goal : PLLFormula
deriving Repr, DecidableEq

/-- Zone discipline, decidably: all zones inside the universe. -/
def Reg.wfB (G : Cell) (S : Reg G) : Bool :=
  S.stable.all (sfPlus G).contains && (sfPlus G).contains S.goal

def Irr.wfB (G : Cell) (S : Irr G) : Bool :=
  S.sigma.all (sfPlus G).contains && S.theta.all (sfPlus G).contains &&
  S.mu.all (sfPlus G).contains && (sfPlus G).contains S.goal

/-! ## W1's named obligations (the (Cl1)–(Cl6) analogue), OPEN

Stated over an ABSTRACT closure so the eventual proofs are not tied
to the bounded searcher: any `cl` satisfying these supports the
calculus, and `clB` at sufficient budget is the intended instance. -/

structure ClProps (G : Cell) (cl : List PLLFormula → List PLLFormula) : Prop where
  extensive : ∀ Δ φ, φ ∈ Δ → φ ∈ sfPlus G → φ ∈ cl Δ
  monotone : ∀ Δ Δ', Δ ⊆ Δ' → cl Δ ⊆ cl Δ'
  idem : ∀ Δ, cl (cl Δ) ⊆ cl Δ
  inUniverse : ∀ Δ, cl Δ ⊆ sfPlus G
  sound : ∀ Δ φ, φ ∈ cl Δ → Nonempty (LaxND Δ φ)
  /-- Lemma 5's analogue, the screened GO: a world's theory is the
  closure of its determining part. -/
  determines : ∀ Δ, cl Δ ⊆ cl (detPart (cl Δ))

end FRJO
