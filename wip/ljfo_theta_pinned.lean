/-
The θ-family of the GZ-candidate cell, pinned.

Station `S = [◯p ⊃ r, ◯q]`, goal `↑↓◯p`, eliminated variable `p`; the
fuel chain of `interpF` (LaxLogic/LJFOFuel.lean) at that cell has the
closed form (read off in wip/ljfo_theta_print.lean, engine-verified in
wip/ljfo_theta_run.lean):

    π  =  (q ∧ r) ⊃ ◯⊥        ρ  =  ◯π        σ  =  q ∧ (◯⊥ ⊃ r)
    F(X)  =  ◯( (X ∧ ρ) ∨ (σ ⊃ ◯⊥) )

    θ₁ = ◯⊥,   θ₂ = ◯(◯⊥ ∨ (q ⊃ ◯⊥)),   θ_{k+1} = F(θ_k)  (k ≥ 2)

with `θ_k ⟛ A_{2k}` certified for k ≤ 3.

What is kernel-checked here:

* `theta2_not_theta1`, `theta3_not_theta2` — the two strict steps, by
  `FinCM.not_provable_of_check` on the emitted models (`by decide`);
* `Fmono` — `F` is monotone for `⊢`, as an explicit `LaxND` term;
* `theta_stab` — **the ascent is NOT strict beyond k = 3**: given the two
  engine certificates `θ₄ ⊢ θ₃` and `θ₃ ⊢ θ₄`, every later θ is
  interderivable with `θ₃`.  So the fixpoint of the retention crank at
  this cell is reached at the third rung.
-/
import LaxLogic.PLLCountermodelEmit
import LaxLogic.PLLSearch

open PLLND

namespace ThetaPin

/-! ## The family -/

def cbot : PLLFormula := .somehow .falsePLL
def fq : PLLFormula := .prop "q"
def fr : PLLFormula := .prop "r"
/-- `π = (q ∧ r) ⊃ ◯⊥`. -/
def piF : PLLFormula := .ifThen (.and fq fr) cbot
/-- `ρ = ◯π`. -/
def rhoF : PLLFormula := .somehow piF
/-- `σ = q ∧ (◯⊥ ⊃ r)`. -/
def sigF : PLLFormula := .and fq (.ifThen cbot fr)

/-- One turn of the retention crank: `F(X) = ◯((X ∧ ρ) ∨ (σ ⊃ ◯⊥))`. -/
def F (X : PLLFormula) : PLLFormula :=
  .somehow (.or (.and X rhoF) (.ifThen sigF cbot))

def theta : Nat → PLLFormula
  | 0 => .falsePLL
  | 1 => cbot
  | 2 => .somehow (.or cbot (.ifThen fq cbot))
  | k+1 => F (theta k)

example : theta 4 = F (theta 3) := rfl
theorem theta_succ (n : Nat) : theta (n + 3) = F (theta (n + 2)) := rfl

/-! ## The two strict steps, as certified countermodels

`M₁` is the one-point model with no fallible world: `◯⊥` fails there while
`◯(q ⊃ ◯⊥)` holds vacuously (`q` is not forced).  `M₂` is the three-point
`Rᵢ`-chain `w₀ ⊑ w₁ ⊑ w₂` with `w₂` fallible, `w₁ ⊳ w₂`, and `q` forced at
`w₀` and `w₁`: `◯⊥` is first true at `w₁`, so `q ⊃ ◯⊥` fails at `w₀` while
`σ ⊃ ◯⊥` holds. -/

def M1 : FinCM := ⟨1, [], [], [], []⟩

theorem theta2_not_theta1 : [theta 2] ⊬ theta 1 :=
  FinCM.not_provable_of_check (M := M1) (w := 0) (by decide)

def M2 : FinCM :=
  ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], [(0, "q"), (1, "q")]⟩

theorem theta3_not_theta2 : [theta 3] ⊬ theta 2 :=
  FinCM.not_provable_of_check (M := M2) (w := 0) (by decide)

/-! ## Transitivity and monotonicity -/

def transD {A B C : PLLFormula} (p : LaxND [A] B) (q : LaxND [B] C) :
    LaxND [A] C :=
  .impElim (.impIntro (q.rename (by intro ψ h; simp at h; subst h; simp))) p

/-- `F` is monotone: `X ⊢ Y` gives `F X ⊢ F Y`.  The lax hypothesis is
opened by `laxElim`, the disjunction by `orElim`; on the left branch the
`X` conjunct feeds `d` through a `⊃`-detour, on the right branch the
`σ ⊃ ◯⊥` disjunct is passed through unchanged. -/
def Fmono {X Y : PLLFormula} (d : LaxND [X] Y) : LaxND [F X] (F Y) :=
  .laxElim (.iden (List.mem_cons_self ..))
    (.orElim (.iden (List.mem_cons_self ..))
      (.laxIntro (.orIntro1 (.andIntro
        (.impElim
          (.impIntro
            (d.rename (by intro ψ h; simp at h; subst h; simp)))
          (.andElim1 (.iden (List.mem_cons_self ..))))
        (.andElim2 (.iden (List.mem_cons_self ..))))))
      (.laxIntro (.orIntro2 (.iden (List.mem_cons_self ..)))))

/-! ## The stabilisation

`θ₄ ⊢ θ₃` is the fact that kills the strict-ascent conjecture; it is an
engine certificate (`PLLND.Search.prove?Bounded`, wip/ljfo_theta_run.lean,
budget 400 000), taken here as a hypothesis so that the induction is
kernel-checked independently of how the two base certificates are
obtained. -/

theorem theta_stab
    (h43 : Nonempty (LaxND [theta 4] (theta 3)))
    (h34 : Nonempty (LaxND [theta 3] (theta 4))) :
    ∀ n, Nonempty (LaxND [theta (n + 3)] (theta 3)) ∧
         Nonempty (LaxND [theta 3] (theta (n + 3))) := by
  intro n
  induction n with
  | zero =>
      exact ⟨⟨.iden (List.mem_cons_self ..)⟩, ⟨.iden (List.mem_cons_self ..)⟩⟩
  | succ m ih =>
      obtain ⟨⟨f⟩, ⟨g⟩⟩ := ih
      obtain ⟨a⟩ := h43
      obtain ⟨b⟩ := h34
      exact ⟨⟨transD (Fmono f) a⟩, ⟨transD b (Fmono g)⟩⟩

/-- The headline, contrapositive form: the ascent is **not** strict at any
rung past the third. -/
theorem theta_not_strict
    (h43 : Nonempty (LaxND [theta 4] (theta 3)))
    (h34 : Nonempty (LaxND [theta 3] (theta 4))) :
    ∀ n, Nonempty (LaxND [theta (n + 4)] (theta (n + 3))) := by
  intro n
  obtain ⟨u⟩ := (theta_stab h43 h34 (n + 1)).1
  obtain ⟨v⟩ := (theta_stab h43 h34 n).2
  exact ⟨transD u v⟩

end ThetaPin
