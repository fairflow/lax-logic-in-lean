/-
THE CANONICALISER, lifted out of `nfc` (wip/closed_frag.lean) and
CERTIFIED.

`nfc` was a per-probe function whose rewrites were *commented* as
plain-PLL interderivabilities.  Here each law is PROVED, so
`canon_interd` certifies the whole normal form, and the canonicaliser
composes with the certified simpset.

Why it matters: `Interd` rules match SYNTACTICALLY.  The screen
measured 41% of cells rewritten when written in the dictionary's own
form against 13% otherwise — the gap was argument order and
definitional shape, not weak rules.  Canonicalising first closes it.
-/
import Rewrite.Core
import Rewrite.Set

namespace Rewrite

open PLLND PLLND.SemUI

/-- `⊤`. -/
def topF : PLLFormula := .ifThen .falsePLL .falsePLL

/-- `⊤` is derivable from any context. -/
def topD (Γ : List PLLFormula) : LaxND Γ topF :=
  .impIntro (.iden (.head _))

/-! ## The laws, each certified -/

theorem and_bot_l (b : PLLFormula) : Interd (.and .falsePLL b) .falsePLL :=
  ⟨⟨.andElim1 (.iden (.head _))⟩, ⟨.falsoElim _ (.iden (.head _))⟩⟩

theorem and_bot_r (a : PLLFormula) : Interd (.and a .falsePLL) .falsePLL :=
  ⟨⟨.andElim2 (.iden (.head _))⟩, ⟨.falsoElim _ (.iden (.head _))⟩⟩

theorem and_top_l (b : PLLFormula) : Interd (.and topF b) b :=
  ⟨⟨.andElim2 (.iden (.head _))⟩, ⟨.andIntro (topD _) (.iden (.head _))⟩⟩

theorem and_top_r (a : PLLFormula) : Interd (.and a topF) a :=
  ⟨⟨.andElim1 (.iden (.head _))⟩, ⟨.andIntro (.iden (.head _)) (topD _)⟩⟩

theorem and_idem (a : PLLFormula) : Interd (.and a a) a :=
  ⟨⟨.andElim1 (.iden (.head _))⟩,
   ⟨.andIntro (.iden (.head _)) (.iden (.head _))⟩⟩

theorem and_comm (a b : PLLFormula) : Interd (.and a b) (.and b a) :=
  ⟨⟨.andIntro (.andElim2 (.iden (.head _))) (.andElim1 (.iden (.head _)))⟩,
   ⟨.andIntro (.andElim2 (.iden (.head _))) (.andElim1 (.iden (.head _)))⟩⟩

theorem or_bot_l (b : PLLFormula) : Interd (.or .falsePLL b) b :=
  ⟨⟨.orElim (.iden (.head _)) (.falsoElim _ (.iden (.head _)))
      (.iden (.head _))⟩,
   ⟨.orIntro2 (.iden (.head _))⟩⟩

theorem or_bot_r (a : PLLFormula) : Interd (.or a .falsePLL) a :=
  ⟨⟨.orElim (.iden (.head _)) (.iden (.head _))
      (.falsoElim _ (.iden (.head _)))⟩,
   ⟨.orIntro1 (.iden (.head _))⟩⟩

theorem or_top_l (b : PLLFormula) : Interd (.or topF b) topF :=
  ⟨⟨topD _⟩, ⟨.orIntro1 (topD _)⟩⟩

theorem or_top_r (a : PLLFormula) : Interd (.or a topF) topF :=
  ⟨⟨topD _⟩, ⟨.orIntro2 (topD _)⟩⟩

theorem or_idem (a : PLLFormula) : Interd (.or a a) a :=
  ⟨⟨.orElim (.iden (.head _)) (.iden (.head _)) (.iden (.head _))⟩,
   ⟨.orIntro1 (.iden (.head _))⟩⟩

theorem or_comm (a b : PLLFormula) : Interd (.or a b) (.or b a) :=
  ⟨⟨.orElim (.iden (.head _)) (.orIntro2 (.iden (.head _)))
      (.orIntro1 (.iden (.head _)))⟩,
   ⟨.orElim (.iden (.head _)) (.orIntro2 (.iden (.head _)))
      (.orIntro1 (.iden (.head _)))⟩⟩

theorem imp_bot_l (b : PLLFormula) : Interd (.ifThen .falsePLL b) topF :=
  ⟨⟨topD _⟩, ⟨.impIntro (.falsoElim _ (.iden (.head _)))⟩⟩

theorem imp_top_r (a : PLLFormula) : Interd (.ifThen a topF) topF :=
  ⟨⟨topD _⟩, ⟨.impIntro (topD _)⟩⟩

theorem imp_top_l (b : PLLFormula) : Interd (.ifThen topF b) b :=
  ⟨⟨.impElim (.iden (.head _)) (topD _)⟩,
   ⟨.impIntro (.iden (.tail _ (.head _)))⟩⟩

theorem imp_self (a : PLLFormula) : Interd (.ifThen a a) topF :=
  ⟨⟨topD _⟩, ⟨.impIntro (.iden (.head _))⟩⟩

/-! ## The smart constructors, and their correctness -/

/-- Injective prefix-code key: the canonical order for the ∧/∨ sort
(lifted from `wip/closed_frag.lean`). -/
def keyF : PLLFormula → String
  | .falsePLL => "F"
  | .prop s => "P" ++ s ++ ";"
  | .and a b => "A" ++ keyF a ++ "," ++ keyF b ++ ";"
  | .or a b => "O" ++ keyF a ++ "," ++ keyF b ++ ";"
  | .ifThen a b => "I" ++ keyF a ++ "," ++ keyF b ++ ";"
  | .somehow a => "S" ++ keyF a ++ ";"

def mkAnd (a b : PLLFormula) : PLLFormula :=
  if a = .falsePLL then .falsePLL
  else if b = .falsePLL then .falsePLL
  else if a = topF then b
  else if b = topF then a
  else if a = b then a
  else if keyF a ≤ keyF b then .and a b else .and b a

theorem mkAnd_interd (a b : PLLFormula) : Interd (.and a b) (mkAnd a b) := by
  unfold mkAnd
  split
  · next h => exact h ▸ and_bot_l b
  split
  · next h => exact h ▸ and_bot_r a
  split
  · next h => exact h ▸ and_top_l b
  split
  · next h => exact h ▸ and_top_r a
  split
  · next h => exact h ▸ and_idem a
  split
  · exact Interd.refl _
  · exact and_comm a b

def mkOr (a b : PLLFormula) : PLLFormula :=
  if a = .falsePLL then b
  else if b = .falsePLL then a
  else if a = topF then topF
  else if b = topF then topF
  else if a = b then a
  else if keyF a ≤ keyF b then .or a b else .or b a

theorem mkOr_interd (a b : PLLFormula) : Interd (.or a b) (mkOr a b) := by
  unfold mkOr
  split
  · next h => exact h ▸ or_bot_l b
  split
  · next h => exact h ▸ or_bot_r a
  split
  · next h => exact h ▸ or_top_l b
  split
  · next h => exact h ▸ or_top_r a
  split
  · next h => exact h ▸ or_idem a
  split
  · exact Interd.refl _
  · exact or_comm a b

def mkImp (a b : PLLFormula) : PLLFormula :=
  if a = .falsePLL then topF
  else if b = topF then topF
  else if a = topF then b
  else if a = b then topF
  else .ifThen a b

theorem mkImp_interd (a b : PLLFormula) : Interd (.ifThen a b) (mkImp a b) := by
  unfold mkImp
  split
  · next h => exact h ▸ imp_bot_l b
  split
  · next h => exact h ▸ imp_top_r a
  split
  · next h => exact h ▸ imp_top_l b
  split
  · next h => exact h ▸ imp_self a
  · exact Interd.refl _

def mkBox (a : PLLFormula) : PLLFormula :=
  if a = topF then topF
  else match a with
    | .somehow _ => a
    | _ => .somehow a

theorem mkBox_interd (a : PLLFormula) : Interd (.somehow a) (mkBox a) := by
  unfold mkBox
  split
  · next h => rw [h]; exact box_top
  · split
    · next x _ => exact box_idem x
    · exact Interd.refl _

/-! ## The canonicaliser -/

/-- Bottom-up canonical form: constant folding, idempotence, canonical
∧/∨ argument order, `◯◯φ = ◯φ`, `◯⊤ = ⊤`. -/
def canon : PLLFormula → PLLFormula
  | .and a b => mkAnd (canon a) (canon b)
  | .or a b => mkOr (canon a) (canon b)
  | .ifThen a b => mkImp (canon a) (canon b)
  | .somehow a => mkBox (canon a)
  | F => F

/-- **The canonicaliser is certified.** -/
theorem canon_interd : ∀ φ : PLLFormula, Interd φ (canon φ) := by
  intro φ
  induction φ with
  | prop a => exact Interd.refl _
  | falsePLL => exact Interd.refl _
  | and a b iha ihb =>
      exact (Interd.and_congr iha ihb).trans (mkAnd_interd _ _)
  | or a b iha ihb =>
      exact (Interd.or_congr iha ihb).trans (mkOr_interd _ _)
  | ifThen a b iha ihb =>
      exact (Interd.imp_congr iha ihb).trans (mkImp_interd _ _)
  | somehow a iha =>
      exact (Interd.box_congr iha).trans (mkBox_interd _)

/-- **The pipeline**: canonicalise, then rewrite by the certified
simpset.  Interderivable with the input. -/
def simplify (rs : List RwRule) (n : Nat) (φ : PLLFormula) : PLLFormula :=
  norm rs n (canon φ)

theorem simplify_interd (rs : List RwRule) (n : Nat) (φ : PLLFormula) :
    Interd φ (simplify rs n φ) :=
  (canon_interd φ).trans (norm_interd rs n _)

/-! ## Pins -/

/--
info: 'Rewrite.canon_interd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms canon_interd

/--
info: 'Rewrite.simplify_interd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms simplify_interd

end Rewrite
