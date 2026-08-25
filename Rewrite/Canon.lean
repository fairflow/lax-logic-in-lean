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

/-- Insert `x` into a sorted ∧-chain. -/
def insAnd (x : PLLFormula) : PLLFormula → PLLFormula
  | .and h t =>
      if keyF x ≤ keyF h then consAnd x (.and h t) else consAnd h (insAnd x t)
  | c => if keyF x ≤ keyF c then consAnd x c else consAnd c x

theorem insAnd_interd (x : PLLFormula) :
    ∀ c : PLLFormula, Interd (.and x c) (insAnd x c) := by
  intro c
  induction c with
  | and h t _ iht =>
      unfold insAnd
      split
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

def insOr (x : PLLFormula) : PLLFormula → PLLFormula
  | .or h t =>
      if keyF x ≤ keyF h then consOr x (.or h t) else consOr h (insOr x t)
  | c => if keyF x ≤ keyF c then consOr x c else consOr c x

theorem insOr_interd (x : PLLFormula) :
    ∀ c : PLLFormula, Interd (.or x c) (insOr x c) := by
  intro c
  induction c with
  | or h t _ iht =>
      unfold insOr
      split
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
∧/∨ argument order, `◯◯φ = ◯φ`, `◯⊤ = ⊤`. -/
def canon : PLLFormula → PLLFormula
  | .and a b => insAllAnd (canon a) (canon b)
  | .or a b => insAllOr (canon a) (canon b)
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
      exact (Interd.and_congr iha ihb).trans (insAllAnd_interd _ _)
  | or a b iha ihb =>
      exact (Interd.or_congr iha ihb).trans (insAllOr_interd _ _)
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

/-- Rounds of `norm`/`canon` alternation.  Three is empirically a
fixpoint on every corpus screened so far; the iteration stops early
whenever the form is stable, so a larger number costs nothing on
cells that settle. -/
def simpRounds : Nat := 4

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
