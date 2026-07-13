import LaxLogic.PLLFrames

/-!
# The closed lax fragment RN(◯,{}) is a rich intuitionistic structure

The closed lax fragment RN(◯,{}) is the Lindenbaum algebra of variable-free PLL
formulas (`⊥, ∧, ∨, ⊃, ◯`) — the free Heyting-algebra-with-nucleus on 0 generators.

## What is proved here (fully mechanised)

1. `not_entails_of_force` / `Ineq` / `ineq_imp_notEquiv` — a **reusable separation
   tool**: a single finite constraint model that forces one closed formula and
   refutes another witnesses their non-⊣⊢-equivalence (via `soundness`).

2. `closed_lax_ge_eight` — an explicit list of **eight pairwise ⊣⊢-inequivalent
   closed lax formulas**, separated by one finite constraint model `MC`.  In
   particular `◯(¬◯⊥)` is a genuinely new closed element, distinct from
   `⊥, ◯⊥, ¬◯⊥, ¬¬◯⊥, ¬¬◯⊥⊃◯⊥, ¬◯⊥∨¬¬◯⊥, ⊤`.  (The `◯`-free closed IPL fragment
   collapses to `{⊥,⊤}`; RN(p) shows only 7 classes up to Dyckhoff weight 8.)

## The model `MC` (comb + fallible top)

`MC` realises `◯⊥` as an RN-style generator.  Worlds `Fin 7`:
`A₁ A₂ A₃` (a "spine of a-points") and `B₁ B₂ B₃` (a linear b-spine) form the
finite Rieger–Nishimura comb of height 3, with a fallible top `f`.  `⊑_m` steps
only `B₁ ⤳ f`, so `MC ⊨ ◯⊥` exactly at `{B₁}` (plus the fallible `f`) — i.e. `◯⊥`
behaves as the free-generator upset `↑B₁`.

## Full infinitude

RN(◯,{}) is in fact **infinite**: the map `p ↦ ◯⊥` embeds the free Heyting
algebra on one generator RN({p}) (the infinite Rieger–Nishimura lattice) into
RN(◯,{}).  Given an intuitionistic model `(P,≤,U)` (`U` an upset), adjoin one
fallible world `f` above `↓U`, set `⊑_m = diag ∪ {(v,f) : v∈U}`, `F={f}`; then
`force w (◯⊥) = [w∈U]` for `w∈P`, and by induction `force w (γ(◯⊥)) = force_P w (γ(p))`
for every IPL `γ` (the added successor `f` is fallible, hence trivial for `⊃`).
So two IPL formulas separated in `P` give their `◯⊥`-substitutions separated in
the adjoined model, and RN(◯,{}) ⊇ RN({p}) is infinite.  Mechanising the
unbounded family requires the generic-height comb `Cₙ` and the Rieger–Nishimura
adequacy induction; the finite witness below (`MC = C₃`) is the base instance.
-/

open PLLFormula

namespace PLLND
namespace LaxInfinite

/-! ### The comb-plus-fallible model `MC` -/

-- Fin 7:  0=A₁ 1=A₂ 2=A₃ | 3=B₁ 4=B₂ 5=B₃ | 6=f (fallible).
def ile (x y : Fin 7) : Prop :=
  x = y ∨
  (y.val = 6 ∧ x.val ≠ 0) ∨
  (x.val ≤ 2 ∧ y.val ≤ 2 ∧ y.val ≤ x.val) ∨
  (x.val ≤ 2 ∧ 3 ≤ y.val ∧ y.val ≤ 5 ∧ y.val < x.val + 3) ∨
  (3 ≤ x.val ∧ x.val ≤ 5 ∧ 3 ≤ y.val ∧ y.val ≤ 5 ∧ y.val ≤ x.val)
instance : DecidableRel ile := fun x y => by unfold ile; infer_instance

def ilm (x y : Fin 7) : Prop := x = y ∨ (x.val = 3 ∧ y.val = 6)
instance : DecidableRel ilm := fun x y => by unfold ilm; infer_instance

@[reducible] def MC : ConstraintModel where
  W := Fin 7
  Ri := ile
  Rm := ilm
  F := {x | x.val = 6}
  V _ := {x | x.val = 6}
  refl_i _ := .inl rfl
  trans_i {x y z} h h' := by
    revert h h'; exact (by decide : ∀ x y z : Fin 7, ile x y → ile y z → ile x z) x y z
  trans_m {x y z} h h' := by
    revert h h'; exact (by decide : ∀ x y z : Fin 7, ilm x y → ilm y z → ilm x z) x y z
  refl_m _ := .inl rfl
  sub_mi {x y} h := by
    revert h; exact (by decide : ∀ x y : Fin 7, ilm x y → ile x y) x y
  hered_F {x y} h hw := by
    revert h hw; exact (by decide : ∀ x y : Fin 7, ile x y → x.val = 6 → y.val = 6) x y
  hered_V {_ x y} h hw := by
    revert h hw; exact (by decide : ∀ x y : Fin 7, ile x y → x.val = 6 → y.val = 6) x y
  full_F hw := hw

instance (φ : PLLFormula) (w : MC.W) : Decidable (MC.force w φ) := MC.decForce φ w

/-! ### Reusable separation tool -/

/-- If a model forces `a` and refutes `b` at some world, then `a ⊬ b`. -/
theorem not_entails_of_force {C : ConstraintModel} (w : C.W) {a b : PLLFormula}
    (ha : C.force w a) (hb : ¬ C.force w b) : ¬ Nonempty (LaxND [a] b) := by
  rintro ⟨p⟩
  refine hb (soundness p C w ?_)
  intro ψ hψ
  rw [List.mem_singleton.mp hψ]; exact ha

/-- Two formulas are non-⊣⊢-equivalent: not derivable in both directions. -/
def NotEquiv (a b : PLLFormula) : Prop :=
  ¬ (Nonempty (LaxND [a] b) ∧ Nonempty (LaxND [b] a))

/-- Decidable, `MC`-checkable witness of inequivalence. -/
def Ineq (a b : PLLFormula) : Prop :=
  (∃ w : Fin 7, MC.force w a ∧ ¬ MC.force w b) ∨
  (∃ w : Fin 7, MC.force w b ∧ ¬ MC.force w a)

instance (a b : PLLFormula) : Decidable (Ineq a b) := by unfold Ineq; infer_instance

theorem ineq_imp_notEquiv {a b : PLLFormula} (h : Ineq a b) : NotEquiv a b := by
  intro hh
  rcases h with ⟨w, ha, hb⟩ | ⟨w, hb, ha⟩
  · exact not_entails_of_force (C := MC) w ha hb hh.1
  · exact not_entails_of_force (C := MC) w hb ha hh.2

/-! ### Eight pairwise-inequivalent closed lax formulas -/

def bot : PLLFormula := falsePLL
def Ob : PLLFormula := bot.somehow                  -- ◯⊥
def neg (x : PLLFormula) : PLLFormula := x.ifThen bot

/-- No propositional atoms occur (the formula is *closed*). -/
def atomFree : PLLFormula → Bool
  | .prop _ => false
  | .falsePLL => true
  | .and a b => atomFree a && atomFree b
  | .or a b => atomFree a && atomFree b
  | .ifThen a b => atomFree a && atomFree b
  | .somehow a => atomFree a

/-- The eight closed witnesses, each with a distinct `MC`-forcing pattern. -/
def witnesses : List PLLFormula :=
  [ bot,                                 -- ⊥
    Ob,                                  -- ◯⊥
    neg Ob,                              -- ¬◯⊥
    neg (neg Ob),                        -- ¬¬◯⊥
    (neg Ob).somehow,                    -- ◯(¬◯⊥)   ← the genuinely new element
    (neg (neg Ob)).ifThen Ob,            -- ¬¬◯⊥ ⊃ ◯⊥
    (neg Ob).or (neg (neg Ob)),          -- ¬◯⊥ ∨ ¬¬◯⊥
    neg bot ]                            -- ⊤

/-- All witnesses are closed (atom-free). -/
theorem witnesses_atomFree : witnesses.all atomFree = true := by decide

/-- **Eight pairwise ⊣⊢-inequivalent closed lax formulas.**  The closed lax
fragment RN(◯,{}) therefore has at least eight elements, and `◯(¬◯⊥)` is a new
closed element beyond `{⊥, ◯⊥, ¬◯⊥, ¬¬◯⊥, ¬¬◯⊥⊃◯⊥, ¬◯⊥∨¬¬◯⊥, ⊤}`. -/
theorem closed_lax_ge_eight : witnesses.Pairwise NotEquiv := by
  have h : witnesses.Pairwise Ineq := by decide
  exact h.imp (fun hab => ineq_imp_notEquiv hab)

/-- `◯(¬◯⊥)` is inequivalent to each of the seven other closed witnesses. -/
theorem somehow_neg_box_new :
    ∀ ψ ∈ [bot, Ob, neg Ob, neg (neg Ob), (neg (neg Ob)).ifThen Ob,
            (neg Ob).or (neg (neg Ob)), neg bot],
      NotEquiv ((neg Ob).somehow) ψ := by
  intro ψ hψ
  fin_cases hψ <;> exact ineq_imp_notEquiv (by decide)

end LaxInfinite
end PLLND

#print axioms PLLND.LaxInfinite.closed_lax_ge_eight
#print axioms PLLND.LaxInfinite.somehow_neg_box_new
