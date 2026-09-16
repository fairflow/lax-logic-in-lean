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

/-! ## Absorption of `◯` under an outer `◯`, through `∧`/`∨`

Under an outer box an inner box in `∧`/`∨`-positive position is
redundant: `◯(a ∨ ◯b) ⊣⊢ ◯(a ∨ b)` and `◯(a ∧ ◯b) ⊣⊢ ◯(a ∧ b)` — the
goal is already lax, so the inner box can be opened.  NOT through `⊃`,
in either position: `◯(a ⊃ ◯b) ⊬ ◯(a ⊃ b)` and `◯(a ⊃ b) ⊬ ◯(◯a ⊃ b)`
(G4c countermodels, 2026-09-04), because an implication goal under a
box is proved in true mode, where the inner box cannot be opened.
`stripBox` deletes every `◯` reachable from the root through `∧`/`∨`
alone; it subsumes `◯◯φ = ◯φ` (`box_idem`), which was the only case
`mkBox` folded before. -/

/-- Delete every `◯` reachable from the root through `∧`/`∨`. -/
def stripBox : PLLFormula → PLLFormula
  | .somehow a => stripBox a
  | .and a b => .and (stripBox a) (stripBox b)
  | .or a b => .or (stripBox a) (stripBox b)
  | F => F

/-- `[a] ⊢ ◯(stripBox a)`: a box met through `∧`/`∨` is opened into
the lax goal. -/
def stripBox_fwd : ∀ a : PLLFormula, LaxND [a] (.somehow (stripBox a))
  | .somehow a =>
      .laxElim (.iden (.head _))
        ((stripBox_fwd a).rename (fun _ h => by simp at h; simp [h, stripBox]))
  | .and a b =>
      let da : LaxND [.and a b] (.somehow (stripBox a)) :=
        .impElim (.impIntro ((stripBox_fwd a).rename (fun _ h => by simp at h; simp [h, stripBox])))
          (.andElim1 (.iden (.head _)))
      let db : LaxND [.and a b] (.somehow (stripBox b)) :=
        .impElim (.impIntro ((stripBox_fwd b).rename (fun _ h => by simp at h; simp [h, stripBox])))
          (.andElim2 (.iden (.head _)))
      .laxElim da (.laxElim (db.rename (fun _ h => by simp at h; simp [h, stripBox]))
        (.laxIntro (.andIntro (.iden (.tail _ (.head _))) (.iden (.head _)))))
  | .or a b =>
      .orElim (.iden (.head _))
        (.laxElim ((stripBox_fwd a).rename (fun _ h => by simp at h; simp [h, stripBox]))
          (.laxIntro (.orIntro1 (.iden (.head _)))))
        (.laxElim ((stripBox_fwd b).rename (fun _ h => by simp at h; simp [h, stripBox]))
          (.laxIntro (.orIntro2 (.iden (.head _)))))
  | .prop _ => .laxIntro (.iden (.head _))
  | .falsePLL => .laxIntro (.iden (.head _))
  | .ifThen _ _ => .laxIntro (.iden (.head _))

/-- `[stripBox a] ⊢ ◯a`: the deleted boxes are restored by `laxIntro`,
lifted through `∧`/`∨`. -/
def stripBox_bwd : ∀ a : PLLFormula, LaxND [stripBox a] (.somehow a)
  | .somehow a => .laxIntro (stripBox_bwd a)
  | .and a b =>
      let da : LaxND [.and (stripBox a) (stripBox b)] (.somehow a) :=
        .impElim (.impIntro ((stripBox_bwd a).rename (fun _ h => by simp at h; simp [h, stripBox])))
          (.andElim1 (.iden (.head _)))
      let db : LaxND [.and (stripBox a) (stripBox b)] (.somehow b) :=
        .impElim (.impIntro ((stripBox_bwd b).rename (fun _ h => by simp at h; simp [h, stripBox])))
          (.andElim2 (.iden (.head _)))
      .laxElim da (.laxElim (db.rename (fun _ h => by simp at h; simp [h, stripBox]))
        (.laxIntro (.andIntro (.iden (.tail _ (.head _))) (.iden (.head _)))))
  | .or a b =>
      .orElim (.iden (.head _))
        (.laxElim ((stripBox_bwd a).rename (fun _ h => by simp at h; simp [h, stripBox]))
          (.laxIntro (.orIntro1 (.iden (.head _)))))
        (.laxElim ((stripBox_bwd b).rename (fun _ h => by simp at h; simp [h, stripBox]))
          (.laxIntro (.orIntro2 (.iden (.head _)))))
  | .prop _ => .laxIntro (.iden (.head _))
  | .falsePLL => .laxIntro (.iden (.head _))
  | .ifThen _ _ => .laxIntro (.iden (.head _))

/-- `◯a ⊣⊢ ◯(stripBox a)`. -/
theorem box_strip (a : PLLFormula) :
    Interd (.somehow a) (.somehow (stripBox a)) :=
  ⟨⟨.laxElim (.iden (.head _))
      ((stripBox_fwd a).rename (fun _ h => by simp at h; simp [h, stripBox]))⟩,
   ⟨.laxElim (.iden (.head _))
      ((stripBox_bwd a).rename (fun _ h => by simp at h; simp [h, stripBox]))⟩⟩

def mkBox (a : PLLFormula) : PLLFormula :=
  if a = topF then topF
  else .somehow (stripBox a)

theorem mkBox_interd (a : PLLFormula) : Interd (.somehow a) (mkBox a) := by
  unfold mkBox
  split
  · next h => rw [h]; exact box_top
  · exact box_strip a

/-! ## `◯⊥` is the least boxed formula

`◯⊥ ⊢ ◯ψ` for every `ψ`, so `◯⊥ ∨ ◯ψ ⊣⊢ ◯ψ`.  `absorbsBoxBot` is a
syntactic sufficient condition for `◯⊥ ⊢ Y`; `dropBoxBot` deletes the
`◯⊥` disjuncts along the right spine of an ∨-chain, and the chain is
replaced by the result only when the result absorbs `◯⊥`. -/

def boxBot : PLLFormula := .somehow .falsePLL

def absorbsBoxBot : PLLFormula → Bool
  | .somehow _ => true
  | .or a b => absorbsBoxBot a || absorbsBoxBot b
  | .and a b => absorbsBoxBot a && absorbsBoxBot b
  | .ifThen _ b => absorbsBoxBot b
  | _ => false

/-- `[◯⊥] ⊢ Y` whenever `absorbsBoxBot Y`. -/
def boxBot_deriv : ∀ Y : PLLFormula, absorbsBoxBot Y = true → LaxND [boxBot] Y
  | .somehow _, _ =>
      .laxElim (.iden (.head _)) (.falsoElim _ (.iden (.head _)))
  | .or a b, h =>
      if ha : absorbsBoxBot a = true then .orIntro1 (boxBot_deriv a ha)
      else .orIntro2 (boxBot_deriv b (by simpa [absorbsBoxBot, ha] using h))
  | .and a b, h =>
      .andIntro (boxBot_deriv a (by simp [absorbsBoxBot] at h; exact h.1))
                (boxBot_deriv b (by simp [absorbsBoxBot] at h; exact h.2))
  | .ifThen _ b, h =>
      .impIntro ((boxBot_deriv b h).rename (fun _ h => by simp at h; simp [h, stripBox]))
  | .prop _, h => by simp [absorbsBoxBot] at h
  | .falsePLL, h => by simp [absorbsBoxBot] at h

/-- Delete the `◯⊥` disjuncts along the right spine of an ∨-chain. -/
def dropBoxBot : PLLFormula → PLLFormula
  | .or y rest =>
      if y = boxBot then dropBoxBot rest
      else if rest = boxBot then y
      else .or y (dropBoxBot rest)
  | F => F

/-- `dropBoxBot c ⊢ c`: deleting a disjunct is weakening. -/
theorem dropBoxBot_bwd : ∀ c : PLLFormula, Nonempty (LaxND [dropBoxBot c] c) := by
  intro c
  induction c with
  | or y rest _ ih =>
      by_cases hy : y = boxBot
      · rw [dropBoxBot, if_pos hy]
        obtain ⟨d⟩ := ih
        exact ⟨.orIntro2 d⟩
      · by_cases hr : rest = boxBot
        · rw [dropBoxBot, if_neg hy, if_pos hr]
          exact ⟨.orIntro1 (.iden (.head _))⟩
        · rw [dropBoxBot, if_neg hy, if_neg hr]
          obtain ⟨d⟩ := ih
          exact ⟨.orElim (.iden (.head _)) (.orIntro1 (.iden (.head _)))
            (.orIntro2 (d.rename (by intro ψ h; simp at h; simp [h, stripBox])))⟩
  | prop _ => exact ⟨.iden (.head _)⟩
  | falsePLL => exact ⟨.iden (.head _)⟩
  | and _ _ _ _ => exact ⟨.iden (.head _)⟩
  | ifThen _ _ _ _ => exact ⟨.iden (.head _)⟩
  | somehow _ _ => exact ⟨.iden (.head _)⟩

/-- `c ⊢ Z` given `◯⊥ ⊢ Z` and `dropBoxBot c ⊢ Z`: every disjunct of
`c` is either a deleted `◯⊥` or a disjunct of `dropBoxBot c`. -/
theorem dropBoxBot_elim : ∀ (c Z : PLLFormula),
    Nonempty (LaxND [c, .ifThen boxBot Z, .ifThen (dropBoxBot c) Z] Z) := by
  intro c
  induction c with
  | or y rest _ ih =>
      intro Z
      by_cases hy : y = boxBot
      · rw [dropBoxBot, if_pos hy]
        obtain ⟨d⟩ := ih Z
        subst hy
        exact ⟨.orElim (.iden (.head _))
          (.impElim (.iden (by simp)) (.iden (.head _)))
          (d.rename (by intro ψ h; simp at h; rcases h with rfl | rfl | rfl <;> simp))⟩
      · by_cases hr : rest = boxBot
        · rw [dropBoxBot, if_neg hy, if_pos hr]
          subst hr
          exact ⟨.orElim (.iden (.head _))
            (.impElim (.iden (by simp)) (.iden (.head _)))
            (.impElim (.iden (by simp)) (.iden (.head _)))⟩
        · rw [dropBoxBot, if_neg hy, if_neg hr]
          obtain ⟨d⟩ := ih Z
          -- `d`, weakened into the second `orElim` branch under the
          -- assumption `dropBoxBot rest ⊃ Z`
          have d' : LaxND [.ifThen (dropBoxBot rest) Z, rest, .or y rest,
              .ifThen boxBot Z, .ifThen (.or y (dropBoxBot rest)) Z] Z :=
            d.rename (by intro ψ h; simp at h; rcases h with rfl | rfl | rfl <;> simp)
          exact ⟨.orElim (.iden (.head _))
            (.impElim (.iden (.tail _ (.tail _ (.tail _ (.head _)))))
              (.orIntro1 (.iden (.head _))))
            (.impElim (.impIntro d')
              (.impIntro (.impElim
                (.iden (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
                (.orIntro2 (.iden (.head _))))))⟩
  | prop _ => intro Z; exact ⟨.impElim (.iden (.tail _ (.tail _ (.head _)))) (.iden (.head _))⟩
  | falsePLL => intro Z; exact ⟨.impElim (.iden (.tail _ (.tail _ (.head _)))) (.iden (.head _))⟩
  | and _ _ _ _ => intro Z; exact ⟨.impElim (.iden (.tail _ (.tail _ (.head _)))) (.iden (.head _))⟩
  | ifThen _ _ _ _ => intro Z; exact ⟨.impElim (.iden (.tail _ (.tail _ (.head _)))) (.iden (.head _))⟩
  | somehow _ _ => intro Z; exact ⟨.impElim (.iden (.tail _ (.tail _ (.head _)))) (.iden (.head _))⟩

/-- `c ⊣⊢ dropBoxBot c` whenever the result absorbs `◯⊥`. -/
theorem dropBoxBot_interd (c : PLLFormula)
    (h : absorbsBoxBot (dropBoxBot c) = true) : Interd c (dropBoxBot c) := by
  obtain ⟨d⟩ := dropBoxBot_elim c (dropBoxBot c)
  obtain ⟨b⟩ := dropBoxBot_bwd c
  refine ⟨⟨?_⟩, ⟨b⟩⟩
  have d' : LaxND [.ifThen (dropBoxBot c) (dropBoxBot c),
      .ifThen boxBot (dropBoxBot c), c] (dropBoxBot c) :=
    d.rename (by intro ψ h; simp at h; rcases h with rfl | rfl | rfl <;> simp)
  have e : LaxND [boxBot, c] (dropBoxBot c) :=
    (boxBot_deriv _ h).rename (by intro ψ h; simp at h; simp [h])
  exact .impElim (.impElim (.impIntro (.impIntro d')) (.impIntro e))
    (.impIntro (.iden (.head _)))

/-- Does the ∧-spine of `c` carry `◯⊥` as a conjunct? -/
def hasBoxBotConj : PLLFormula → Bool
  | .and a rest => (a = boxBot) || hasBoxBotConj rest
  | c => c = boxBot

/-- `[c] ⊢ ◯⊥` when `◯⊥` is a conjunct of `c`. -/
theorem conjBoxBot : ∀ c : PLLFormula,
    hasBoxBotConj c = true → Nonempty (LaxND [c] boxBot) := by
  intro c
  induction c with
  | and a rest _ ih =>
      intro h
      simp [hasBoxBotConj] at h
      rcases h with rfl | h
      · exact ⟨.andElim1 (.iden (.head _))⟩
      · obtain ⟨d⟩ := ih h
        exact ⟨.impElim (.impIntro (d.rename (by intro ψ h; simp at h; simp [h])))
          (.andElim2 (.iden (.head _)))⟩
  | somehow a _ =>
      intro h
      simp [hasBoxBotConj, boxBot] at h
      subst h
      exact ⟨.iden (.head _)⟩
  | prop _ => intro h; simp [hasBoxBotConj, boxBot] at h
  | falsePLL => intro h; simp [hasBoxBotConj, boxBot] at h
  | or _ _ _ _ => intro h; simp [hasBoxBotConj, boxBot] at h
  | ifThen _ _ _ _ => intro h; simp [hasBoxBotConj, boxBot] at h

/-- Collapse an ∧-chain to `◯⊥` when it carries `◯⊥` and every
conjunct absorbs it: `◯⊥ ∧ ◯ψ ⊣⊢ ◯⊥`. -/
def collapseBoxBotAnd (c : PLLFormula) : PLLFormula :=
  if hasBoxBotConj c && absorbsBoxBot c then boxBot else c

theorem collapseBoxBotAnd_interd (c : PLLFormula) :
    Interd c (collapseBoxBotAnd c) := by
  unfold collapseBoxBotAnd
  split
  · next h =>
      simp at h
      obtain ⟨d⟩ := conjBoxBot c h.1
      exact ⟨⟨d⟩, ⟨boxBot_deriv c h.2⟩⟩
  · exact Interd.refl _

/-- Drop the `◯⊥` disjuncts of an ∨-chain when the remainder absorbs them. -/
def dropBoxBotIf (c : PLLFormula) : PLLFormula :=
  if absorbsBoxBot (dropBoxBot c) then dropBoxBot c else c

theorem dropBoxBotIf_interd (c : PLLFormula) : Interd c (dropBoxBotIf c) := by
  unfold dropBoxBotIf
  split
  · next h => exact dropBoxBot_interd c h
  · exact Interd.refl _


/-! ## Associativity and flattening

Binary commutativity leaves `(a∧b)∧c` and `a∧(b∧c)` distinct.  The fix
is to treat an ∧-tree as a SORTED RIGHT-NESTED CHAIN and insert into
it — one mechanism that subsumes associativity, commutativity and
deduplication.  `consAnd`/`consOr` do the constant folding WITHOUT
reordering (so the sort is not fought by the smart constructor), and
`insAnd`/`insAll` maintain the invariant. -/

theorem and_assoc' (a b c : PLLFormula) :
    Interd (.and (.and a b) c) (.and a (.and b c)) :=
  ⟨⟨.andIntro (.andElim1 (.andElim1 (.iden (.head _))))
      (.andIntro (.andElim2 (.andElim1 (.iden (.head _))))
        (.andElim2 (.iden (.head _))))⟩,
   ⟨.andIntro (.andIntro (.andElim1 (.iden (.head _)))
      (.andElim1 (.andElim2 (.iden (.head _)))))
      (.andElim2 (.andElim2 (.iden (.head _))))⟩⟩

theorem and_swap (a b c : PLLFormula) :
    Interd (.and a (.and b c)) (.and b (.and a c)) :=
  ⟨⟨.andIntro (.andElim1 (.andElim2 (.iden (.head _))))
      (.andIntro (.andElim1 (.iden (.head _)))
        (.andElim2 (.andElim2 (.iden (.head _)))))⟩,
   ⟨.andIntro (.andElim1 (.andElim2 (.iden (.head _))))
      (.andIntro (.andElim1 (.iden (.head _)))
        (.andElim2 (.andElim2 (.iden (.head _)))))⟩⟩

theorem or_assoc' (a b c : PLLFormula) :
    Interd (.or (.or a b) c) (.or a (.or b c)) :=
  ⟨⟨.orElim (.iden (.head _))
      (.orElim (.iden (.head _)) (.orIntro1 (.iden (.head _)))
        (.orIntro2 (.orIntro1 (.iden (.head _)))))
      (.orIntro2 (.orIntro2 (.iden (.head _))))⟩,
   ⟨.orElim (.iden (.head _))
      (.orIntro1 (.orIntro1 (.iden (.head _))))
      (.orElim (.iden (.head _))
        (.orIntro1 (.orIntro2 (.iden (.head _))))
        (.orIntro2 (.iden (.head _))))⟩⟩

theorem or_swap (a b c : PLLFormula) :
    Interd (.or a (.or b c)) (.or b (.or a c)) :=
  ⟨⟨.orElim (.iden (.head _))
      (.orIntro2 (.orIntro1 (.iden (.head _))))
      (.orElim (.iden (.head _)) (.orIntro1 (.iden (.head _)))
        (.orIntro2 (.orIntro2 (.iden (.head _)))))⟩,
   ⟨.orElim (.iden (.head _))
      (.orIntro2 (.orIntro1 (.iden (.head _))))
      (.orElim (.iden (.head _)) (.orIntro1 (.iden (.head _)))
        (.orIntro2 (.orIntro2 (.iden (.head _)))))⟩⟩

/-- Constant folding WITHOUT reordering (so sortedness survives). -/
def consAnd (x c : PLLFormula) : PLLFormula :=
  if x = .falsePLL then .falsePLL
  else if c = .falsePLL then .falsePLL
  else if x = topF then c
  else if c = topF then x
  else if x = c then x
  else .and x c

theorem consAnd_interd (x c : PLLFormula) :
    Interd (.and x c) (consAnd x c) := by
  unfold consAnd
  split
  · next h => exact h ▸ and_bot_l c
  split
  · next h => exact h ▸ and_bot_r x
  split
  · next h => exact h ▸ and_top_l c
  split
  · next h => exact h ▸ and_top_r x
  split
  · next h => exact h ▸ and_idem x
  · exact Interd.refl _

def consOr (x c : PLLFormula) : PLLFormula :=
  if x = .falsePLL then c
  else if c = .falsePLL then x
  else if x = topF then topF
  else if c = topF then topF
  else if x = c then x
  else .or x c

theorem consOr_interd (x c : PLLFormula) :
    Interd (.or x c) (consOr x c) := by
  unfold consOr
  split
  · next h => exact h ▸ or_bot_l c
  split
  · next h => exact h ▸ or_bot_r x
  split
  · next h => exact h ▸ or_top_l c
  split
  · next h => exact h ▸ or_top_r x
  split
  · next h => exact h ▸ or_idem x
  · exact Interd.refl _

/-- `x ∧ (x ∧ t) ⊣⊢ x ∧ t`: a duplicate chain head. -/
theorem and_head_idem (x t : PLLFormula) :
    Interd (.and x (.and x t)) (.and x t) :=
  ⟨⟨.andElim2 (.iden (.head _))⟩,
   ⟨.andIntro (.andElim1 (.iden (.head _))) (.iden (.head _))⟩⟩

/-- `x ∨ (x ∨ t) ⊣⊢ x ∨ t`: a duplicate chain head. -/
theorem or_head_idem (x t : PLLFormula) :
    Interd (.or x (.or x t)) (.or x t) :=
  ⟨⟨.orElim (.iden (.head _)) (.orIntro1 (.iden (.head _))) (.iden (.head _))⟩,
   ⟨.orIntro2 (.iden (.head _))⟩⟩

/-- Insert `x` into a sorted ∧-chain.  An element equal to the head is
dropped (`consAnd` only compares `x` with the whole chain, so without
this test `r ∧ (r ∧ t)` survived — found 2026-09-04 on the interpolant
chains). -/
def insAnd (x : PLLFormula) : PLLFormula → PLLFormula
  | .and h t =>
      if x = h then .and h t
      else if keyF x ≤ keyF h then consAnd x (.and h t) else consAnd h (insAnd x t)
  | c => if keyF x ≤ keyF c then consAnd x c else consAnd c x

theorem insAnd_interd (x : PLLFormula) :
    ∀ c : PLLFormula, Interd (.and x c) (insAnd x c) := by
  intro c
  induction c with
  | and h t _ iht =>
      unfold insAnd
      split
      · next hx => subst hx; exact and_head_idem _ _
      · split
        · exact consAnd_interd _ _
        · exact ((and_swap x h t).trans
            (Interd.and_congr (Interd.refl h) iht)).trans (consAnd_interd _ _)
  | prop a => unfold insAnd; split
              · exact consAnd_interd _ _
              · exact (and_comm _ _).trans (consAnd_interd _ _)
  | falsePLL => unfold insAnd; split
                · exact consAnd_interd _ _
                · exact (and_comm _ _).trans (consAnd_interd _ _)
  | or a b _ _ => unfold insAnd; split
                  · exact consAnd_interd _ _
                  · exact (and_comm _ _).trans (consAnd_interd _ _)
  | ifThen a b _ _ => unfold insAnd; split
                      · exact consAnd_interd _ _
                      · exact (and_comm _ _).trans (consAnd_interd _ _)
  | somehow a _ => unfold insAnd; split
                   · exact consAnd_interd _ _
                   · exact (and_comm _ _).trans (consAnd_interd _ _)

/-- Insert every conjunct of `a` into the chain `c` — flattening. -/
def insAllAnd : PLLFormula → PLLFormula → PLLFormula
  | .and a1 a2, c => insAllAnd a1 (insAllAnd a2 c)
  | x, c => insAnd x c

theorem insAllAnd_interd :
    ∀ (a c : PLLFormula), Interd (.and a c) (insAllAnd a c) := by
  intro a
  induction a with
  | and a1 a2 ih1 ih2 =>
      intro c
      exact ((and_assoc' a1 a2 c).trans
        (Interd.and_congr (Interd.refl a1) (ih2 c))).trans (ih1 _)
  | prop x => intro c; exact insAnd_interd _ _
  | falsePLL => intro c; exact insAnd_interd _ _
  | or a b _ _ => intro c; exact insAnd_interd _ _
  | ifThen a b _ _ => intro c; exact insAnd_interd _ _
  | somehow a _ => intro c; exact insAnd_interd _ _

/-- Insert `x` into a sorted ∨-chain; an element equal to the head is
dropped (see `insAnd`). -/
def insOr (x : PLLFormula) : PLLFormula → PLLFormula
  | .or h t =>
      if x = h then .or h t
      else if keyF x ≤ keyF h then consOr x (.or h t) else consOr h (insOr x t)
  | c => if keyF x ≤ keyF c then consOr x c else consOr c x

theorem insOr_interd (x : PLLFormula) :
    ∀ c : PLLFormula, Interd (.or x c) (insOr x c) := by
  intro c
  induction c with
  | or h t _ iht =>
      unfold insOr
      split
      · next hx => subst hx; exact or_head_idem _ _
      · split
        · exact consOr_interd _ _
        · exact ((or_swap x h t).trans
            (Interd.or_congr (Interd.refl h) iht)).trans (consOr_interd _ _)
  | prop a => unfold insOr; split
              · exact consOr_interd _ _
              · exact (or_comm _ _).trans (consOr_interd _ _)
  | falsePLL => unfold insOr; split
                · exact consOr_interd _ _
                · exact (or_comm _ _).trans (consOr_interd _ _)
  | and a b _ _ => unfold insOr; split
                   · exact consOr_interd _ _
                   · exact (or_comm _ _).trans (consOr_interd _ _)
  | ifThen a b _ _ => unfold insOr; split
                      · exact consOr_interd _ _
                      · exact (or_comm _ _).trans (consOr_interd _ _)
  | somehow a _ => unfold insOr; split
                   · exact consOr_interd _ _
                   · exact (or_comm _ _).trans (consOr_interd _ _)

def insAllOr : PLLFormula → PLLFormula → PLLFormula
  | .or a1 a2, c => insAllOr a1 (insAllOr a2 c)
  | x, c => insOr x c

theorem insAllOr_interd :
    ∀ (a c : PLLFormula), Interd (.or a c) (insAllOr a c) := by
  intro a
  induction a with
  | or a1 a2 ih1 ih2 =>
      intro c
      exact ((or_assoc' a1 a2 c).trans
        (Interd.or_congr (Interd.refl a1) (ih2 c))).trans (ih1 _)
  | prop x => intro c; exact insOr_interd _ _
  | falsePLL => intro c; exact insOr_interd _ _
  | and a b _ _ => intro c; exact insOr_interd _ _
  | ifThen a b _ _ => intro c; exact insOr_interd _ _
  | somehow a _ => intro c; exact insOr_interd _ _

/-! ## The canonicaliser -/

/-- Bottom-up canonical form: constant folding, idempotence, canonical
∧/∨ argument order, `◯⊤ = ⊤`, `◯`-absorption through `∧`/`∨` under a
box (`stripBox`, subsuming `◯◯φ = ◯φ`), and `◯⊥ ∨ ◯ψ = ◯ψ`
(`dropBoxBotIf`).  The last two can leave a chain non-canonical
(`stripBox` changes `keyF`s); `simpIter` re-canonicalises. -/
def canon : PLLFormula → PLLFormula
  | .and a b => collapseBoxBotAnd (insAllAnd (canon a) (canon b))
  | .or a b => dropBoxBotIf (insAllOr (canon a) (canon b))
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
      exact ((Interd.and_congr iha ihb).trans (insAllAnd_interd _ _)).trans
        (collapseBoxBotAnd_interd _)
  | or a b iha ihb =>
      exact ((Interd.or_congr iha ihb).trans (insAllOr_interd _ _)).trans
        (dropBoxBotIf_interd _)
  | ifThen a b iha ihb =>
      exact (Interd.imp_congr iha ihb).trans (mkImp_interd _ _)
  | somehow a iha =>
      exact (Interd.box_congr iha).trans (mkBox_interd _)

/-! ## Canonicalising the RULES

The first cut of `simplify` was `norm rs n (canon φ)`, and it was
measurably crippled: only 47 of the 237 cells the dictionary PROVES
were closed by it (`lean_exe rnextend`, the control).  The reason is
that `canon` sorts ∧/∨ arguments by `keyF` while the harvested rules
were stated in the DICTIONARY's argument order, so canonicalising the
goal moved it out of reach of the very rules meant to fire on it.

The fix is to put the rules through the same canonicaliser.  Sound
for free: a rule is a certified `Interd`, and `canon` is certified,
so the canonicalised rule is `canon lhs ⊣⊢ lhs ⊣⊢ rhs ⊣⊢ canon rhs`.
-/

/-- Both sides of a rule through the canonicaliser. -/
def canonRule (r : RwRule) : RwRule :=
  ⟨canon r.lhs, canon r.rhs,
   ((canon_interd r.lhs).symm.trans r.ok).trans (canon_interd r.rhs)⟩

/-- Canonicalise a whole simpset.  Do this ONCE, at a top-level
`def`, not per goal. -/
def canonSet (rs : List RwRule) : List RwRule := rs.map canonRule

/-- Rewriting a canonical term can leave it non-canonical: a rewrite
inside an ∧-chain replaces a conjunct whose `keyF` no longer sorts
where it sat, and flattening can expose new conjuncts.  So alternate
`norm` and `canon` to a fixpoint rather than running each once. -/
def simpIter (rs : List RwRule) (n : Nat) : Nat → PLLFormula → PLLFormula
  | 0, φ => φ
  | k + 1, φ =>
      if canon (norm rs n φ) = φ then φ
      else simpIter rs n k (canon (norm rs n φ))

theorem simpIter_interd (rs : List RwRule) (n : Nat) :
    ∀ (k : Nat) (φ : PLLFormula), Interd φ (simpIter rs n k φ) := by
  intro k
  induction k with
  | zero => intro φ; exact Interd.refl φ
  | succ k ih =>
      intro φ
      by_cases h : canon (norm rs n φ) = φ
      · rw [simpIter, if_pos h]; exact Interd.refl φ
      · rw [simpIter, if_neg h]
        exact ((norm_interd rs n φ).trans (canon_interd _)).trans (ih _)

/-- Rounds of `norm`/`canon` alternation.  Three was empirically a
fixpoint on every corpus screened before the `◯`-absorption passes;
with them, each round strips one box level and folds the constants it
exposes, so the fixpoint needs about as many rounds as the box-nesting
depth (the fuel-20 interpolant chains of 2026-09-04 needed more than
four).  The iteration stops early whenever the form is stable, so a
larger bound costs nothing on cells that settle. -/
def simpRounds : Nat := 32

/-- **The pipeline**: canonicalise, then alternate rewriting and
re-canonicalising to a fixpoint.  Interderivable with the input,
unconditionally.

`rs` is expected to be ALREADY canonicalised (`canonSet`); passing a
raw set is sound but much less effective. -/
def simplifyWith (rs : List RwRule) (n : Nat) (φ : PLLFormula) : PLLFormula :=
  simpIter rs n simpRounds (canon φ)

theorem simplifyWith_interd (rs : List RwRule) (n : Nat) (φ : PLLFormula) :
    Interd φ (simplifyWith rs n φ) :=
  (canon_interd φ).trans (simpIter_interd rs n _ _)

/-- The convenience form: canonicalises the rule set on the spot.
Prefer `simplifyWith` against a top-level canonicalised set in any
sweep — this recomputes `canonSet rs` on every call. -/
def simplify (rs : List RwRule) (n : Nat) (φ : PLLFormula) : PLLFormula :=
  simplifyWith (canonSet rs) n φ

theorem simplify_interd (rs : List RwRule) (n : Nat) (φ : PLLFormula) :
    Interd φ (simplify rs n φ) :=
  simplifyWith_interd _ n φ

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

/--
info: 'Rewrite.simplifyWith_interd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms simplifyWith_interd

end Rewrite
