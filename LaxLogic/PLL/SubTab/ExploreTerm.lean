import LaxLogic.PLL.SubTab.ExploreTest
import LaxLogic.PLL.Normalisation.Confluence

/-!
# From a derivation of the explorer to a proof term, and to its normal form

2026-11-20.  A spike, asked for by Matthew as a check: a derivation of the
explorer (`Explore.Der STab s`) is a tree of moves, with no reduction of its
own; the reductions of PLL are those of the proof terms `Tm Γ φ`
(`ND/Terms.lean`, `Normalisation/`).  The two are joined here by the maps
there already were:

    term   : Explore.Der STab ⟨false, [], [φ]⟩ → [] ⊢ φ       (Explore.lean)
    ndToTm : LaxND Γ φ → Tm Γ φ                                (ND/Terms.lean)
    tm d  := ndToTm (term d)                                   (here)

**PROVED, for every derivation `d` of `⊢ φ`** (with the normaliser and the
confluence of `Normalisation/`, whose axioms these two inherit):

    Steps (tm d) (nf d) ∧ Nf (nf d)                            (nf_spec)
    Steps (tm d) u → Nf u → u = nf d                           (nf_unique)

**PROVED, for the derivations pinned in `ExploreTest.lean`**, by running the
fuelled reducer `Tm.reduceFuel` in the kernel (`nf_of_reduceFuel`), within
`[propext, Quot.sound]`: the four laws of `◯` have as normal forms the terms
of the monad,

    unit       p ↠ ◯p                   λx. val x
    mult       ◯◯p ↠ ◯p                 λx. let y ⇐ x in let z ⇐ y in val z
    functor    (p ↠ q) ↠ (◯p ↠ ◯q)      λf. λx. let y ⇐ x in val (f y)
    strength   (◯p ∧ ◯q) ↠ ◯(p ∧ q)     λx. let y ⇐ fst x in let z ⇐ snd x in val ⟨y, z⟩

**REFUTED**: that the derivations of one sequent have one normal form.
`functor2` makes the move `boxL p` twice where `functor` makes it once; both
are derivations of `⊢ (p ↠ q) ↠ (◯p ↠ ◯q)`, and their proof terms are not
convertible (`functor_not_conv`):

    functor     λf. λx. let y ⇐ x in val (f y)
    functor2    λf. λx. let y ⇐ x in let z ⇐ x in val (f z)

A move made twice is a computation run twice.  The search's closed tableaux
show the same: for three of the eight formulas below the search's derivation
and the one by hand have different normal forms, and they differ by such
repeated `let`s only (for the chain, 403 moves against 16; five `let`s
against one).

**What the runs show, not stated as theorems** (pinned below as output):

* No proof term of a derivation here is normal as it comes: the reading of a
  sequent (`⋁Δ`, or `◯⋁Δ`) is translated through derived rules, which leave
  `case inl … of …` and `(λx. …) …` behind.
* Every one reduces to a normal form in a few steps; all but one are the
  term one would write.  The exception is `exFalso`: `Step` has no commuting
  conversion for `abort`, so a `case` of the reading stays under it.
* A sequent with two hypotheses of one formula (`twoHyps`) has the term that
  uses the later one; nothing in the derivation chose it (`varOfMem` takes
  the first occurrence in the context).

Not in the default build; in the library `SubTabExplore`.
-/

open PLLFormula ProofTools

set_option apply_move.tryThis false

namespace PLLND

/-! ## Reading a term -/

/-- The de Bruijn index of a variable. -/
def Var.idx : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Var Γ φ → Nat
  | _, _, .here => 0
  | _, _, .there v => v.idx + 1

/-- The number of constructors of a term. -/
def Tm.size : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Tm Γ φ → Nat
  | _, _, .var _ => 1
  | _, _, .abort _ t => t.size + 1
  | _, _, .lam t => t.size + 1
  | _, _, .app t s => t.size + s.size + 1
  | _, _, .pair t s => t.size + s.size + 1
  | _, _, .fst t => t.size + 1
  | _, _, .snd t => t.size + 1
  | _, _, .inl t => t.size + 1
  | _, _, .inr t => t.size + 1
  | _, _, .case t u₁ u₂ => t.size + u₁.size + u₂.size + 1
  | _, _, .val t => t.size + 1
  | _, _, .bind t u => t.size + u.size + 1

private def wrap (arg : Bool) (s : String) : String := if arg then "(" ++ s ++ ")" else s

/-- A term in writing.  A binder met at depth `n` is named `xn`; `arg` asks
for brackets round a compound term. -/
def Tm.write : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Nat → Bool → Tm Γ φ → String
  | _, _, n, _, .var v => s!"x{n - 1 - v.idx}"
  | _, _, n, a, .abort _ t => wrap a s!"abort {t.write n true}"
  | _, _, n, a, .lam t => wrap a s!"λx{n}. {t.write (n + 1) false}"
  | _, _, n, a, .app t s => wrap a s!"{t.write n true} {s.write n true}"
  | _, _, n, _, .pair t s => s!"⟨{t.write n false}, {s.write n false}⟩"
  | _, _, n, a, .fst t => wrap a s!"fst {t.write n true}"
  | _, _, n, a, .snd t => wrap a s!"snd {t.write n true}"
  | _, _, n, a, .inl t => wrap a s!"inl {t.write n true}"
  | _, _, n, a, .inr t => wrap a s!"inr {t.write n true}"
  | _, _, n, a, .case t u₁ u₂ =>
      wrap a (s!"case {t.write n false} of x{n}. {u₁.write (n + 1) false} " ++
        s!"| x{n}. {u₂.write (n + 1) false}")
  | _, _, n, a, .val t => wrap a s!"val {t.write n true}"
  | _, _, n, a, .bind t u =>
      wrap a s!"let x{n} ⇐ {t.write n false} in {u.write (n + 1) false}"

/-- Reduce by `Tm.step?`, counting: the term reached, the steps taken, and
whether the term reached is normal. -/
def Tm.reduceCount : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    Nat → Tm Γ φ → Tm Γ φ × Nat × Bool
  | _, _, 0, t => (t, 0, false)
  | _, _, fuel + 1, t =>
      match t.step? with
      | some ⟨t', _⟩ => let r := t'.reduceCount fuel; (r.1, r.2.1 + 1, r.2.2)
      | none => (t, 0, true)

namespace SubTab

/-! ## The proof term of a derivation, and its normal form -/

/-- **The proof term of a derivation of `⊢ φ`.** -/
def tm {φ : PLLFormula} (d : Explore.Der STab ⟨false, [], [φ]⟩) : Tm [] φ :=
  ndToTm (term d)

/-- **Its normal form**, by the total normaliser. -/
def nf {φ : PLLFormula} (d : Explore.Der STab ⟨false, [], [φ]⟩) : Tm [] φ :=
  (tm d).normalize

/-- The normal form is reached by reduction from the proof term, and is
normal. -/
theorem nf_spec {φ : PLLFormula} (d : Explore.Der STab ⟨false, [], [φ]⟩) :
    Steps (tm d) (nf d) ∧ Nf (nf d) :=
  Tm.normalize_spec _

/-- It is the only normal term the proof term reduces to. -/
theorem nf_unique {φ : PLLFormula} (d : Explore.Der STab ⟨false, [], [φ]⟩) {u : Tm [] φ}
    (h : Steps (tm d) u) (hu : Nf u) : u = nf d :=
  normal_form_unique h (nf_spec d).1 hu (nf_spec d).2

/-- **A normal form by running the fuelled reducer**: the term it reaches,
when it reports that term normal.  No strong normalisation is used. -/
theorem nf_of_reduceFuel {φ : PLLFormula} (d : Explore.Der STab ⟨false, [], [φ]⟩) (n : Nat)
    {u : Tm [] φ} (h : (tm d).reduceFuel n = (u, true)) : Steps (tm d) u ∧ Nf u := by
  have hs := Tm.reduceFuel_sound n (tm d)
  rw [h] at hs
  exact ⟨hs.1, hs.2 rfl⟩

/-- What the spike reports of a derivation: its moves, the size of its proof
term and whether that is normal, the steps to a normal form, and that form. -/
def report {φ : PLLFormula} (name : String) (d : Explore.Der STab ⟨false, [], [φ]⟩) : String :=
  let t := tm d
  let r := t.reduceCount 100000
  s!"{name}: {d.script.length} moves; term of size {t.size}, normal: {t.step?.isNone}; " ++
  s!"{r.2.1} steps to a term of size {r.1.size}, normal: {r.2.2}\n" ++
  s!"  normal form: {r.1.write 0 false}"

namespace ExploreTest

/-! ## The pinned derivations -/

/-- `p ↠ (p ↠ p)`: two hypotheses of one formula. -/
def twoHyps : Explore.Der STab (goal (p ↠ (p ↠ p))) := by
  subtab impR p (p ↠ p)
  subtab impR p p
  subtab ax p

/-- Functoriality again, with the move `boxL p` made twice. -/
def functor2 : Explore.Der STab (goal ((p ↠ q) ↠ (◯p ↠ ◯q))) := by
  subtab impR (p ↠ q) (◯p ↠ ◯q)
  subtab impR (◯p) (◯q)
  subtab boxR q
  subtab boxL p
  subtab boxL p
  subtab impL p q
  subtab ax p
  subtab ax q

-- the proof term of a derivation, as it comes
/--
info: case inl (λx0. case inl (let x1 ⇐ val (inl x0) in case x1 of x2. val x2 | x2. abort x2) of x1. x1 | x1. abort x1) of x0. x0 | x0. abort x0
-/
#guard_msgs in
#eval IO.println ((tm unit).write 0 false)

/--
info: unit: 3 moves; term of size 21, normal: false; 4 steps to a term of size 3, normal: true
  normal form: λx0. val x0
-/
#guard_msgs in
#eval IO.println (report "unit" unit)

/--
info: mult: 5 moves; term of size 25, normal: false; 6 steps to a term of size 7, normal: true
  normal form: λx0. let x1 ⇐ x0 in let x2 ⇐ x1 in val x2
-/
#guard_msgs in
#eval IO.println (report "mult" mult)

/--
info: functor: 7 moves; term of size 48, normal: false; 10 steps to a term of size 8, normal: true
  normal form: λx0. λx1. let x2 ⇐ x1 in val (x0 x2)
-/
#guard_msgs in
#eval IO.println (report "functor" functor)

/--
info: functor2: 8 moves; term of size 50, normal: false; 11 steps to a term of size 10, normal: true
  normal form: λx0. λx1. let x2 ⇐ x1 in let x3 ⇐ x1 in val (x0 x3)
-/
#guard_msgs in
#eval IO.println (report "functor2" functor2)

/--
info: strength: 8 moves; term of size 63, normal: false; 14 steps to a term of size 11, normal: true
  normal form: λx0. let x1 ⇐ fst x0 in let x2 ⇐ snd x0 in val ⟨x1, x2⟩
-/
#guard_msgs in
#eval IO.println (report "strength" strength)

/--
info: kAxiom: 8 moves; term of size 50, normal: false; 11 steps to a term of size 10, normal: true
  normal form: λx0. λx1. let x2 ⇐ x0 in let x3 ⇐ x1 in val (x2 x3)
-/
#guard_msgs in
#eval IO.println (report "kAxiom" kAxiom)

/--
info: exFalso: 4 moves; term of size 22, normal: false; 3 steps to a term of size 12, normal: true
  normal form: λx0. let x1 ⇐ x0 in let x2 ⇐ abort x1 in case x2 of x3. val x3 | x3. abort x3
-/
#guard_msgs in
#eval IO.println (report "exFalso" exFalso)

/--
info: twoHyps: 3 moves; term of size 18, normal: false; 3 steps to a term of size 3, normal: true
  normal form: λx0. λx1. x1
-/
#guard_msgs in
#eval IO.println (report "twoHyps" twoHyps)

/--
info: chain4: 16 moves; term of size 123, normal: false; 25 steps to a term of size 17, normal: true
  normal form: λx0. λx1. λx2. λx3. λx4. let x5 ⇐ x4 in val (x3 (x2 (x1 (x0 x5))))
-/
#guard_msgs in
#eval IO.println (report "chain4" chain4Der)

/-! ## The four laws of `◯`: their normal forms, in the kernel -/

/-- `λx. val x`: the unit. -/
def unitTm : Tm [] (p ↠ ◯p) := .lam (.val (.var .here))

/-- `λx. let y ⇐ x in let z ⇐ y in val z`: the multiplication. -/
def multTm : Tm [] (◯◯p ↠ ◯p) :=
  .lam (.bind (.var .here) (.bind (.var .here) (.val (.var .here))))

/-- `λf. λx. let y ⇐ x in val (f y)`: the action on a function. -/
def functorTm : Tm [] ((p ↠ q) ↠ (◯p ↠ ◯q)) :=
  .lam (.lam (.bind (.var .here) (.val (.app (.var (.there (.there .here))) (.var .here)))))

/-- `λx. let y ⇐ fst x in let z ⇐ snd x in val ⟨y, z⟩`: the strength. -/
def strengthTm : Tm [] ((◯p ∧ ◯q) ↠ ◯(p ∧ q)) :=
  .lam (.bind (.fst (.var .here)) (.bind (.snd (.var (.there .here)))
    (.val (.pair (.var (.there .here)) (.var .here)))))

/-- `λf. λx. let y ⇐ x in let z ⇐ x in val (f z)`: `x` run twice. -/
def functor2Tm : Tm [] ((p ↠ q) ↠ (◯p ↠ ◯q)) :=
  .lam (.lam (.bind (.var .here) (.bind (.var (.there .here))
    (.val (.app (.var (.there (.there (.there .here)))) (.var .here))))))

/-- The proof term of `unit` reduces to `λx. val x`, which is normal. -/
theorem unit_nf : Steps (tm unit) unitTm ∧ Nf unitTm := nf_of_reduceFuel unit 100 rfl

/-- The proof term of `mult` reduces to the multiplication, which is normal. -/
theorem mult_nf : Steps (tm mult) multTm ∧ Nf multTm := nf_of_reduceFuel mult 100 rfl

/-- The proof term of `functor` reduces to the action on a function, which is
normal. -/
theorem functor_nf : Steps (tm functor) functorTm ∧ Nf functorTm :=
  nf_of_reduceFuel functor 100 rfl

/-- The proof term of `strength` reduces to the strength, which is normal. -/
theorem strength_nf : Steps (tm strength) strengthTm ∧ Nf strengthTm :=
  nf_of_reduceFuel strength 100 rfl

/-- The proof term of `functor2` reduces to the term that runs `x` twice,
which is normal. -/
theorem functor2_nf : Steps (tm functor2) functor2Tm ∧ Nf functor2Tm :=
  nf_of_reduceFuel functor2 100 rfl

/-! ## Two derivations of one sequent, two normal forms -/

/-- The two normal forms are different terms. -/
theorem functorTm_ne : functorTm ≠ functor2Tm := by
  intro h
  simp [functorTm, functor2Tm] at h

/-- **The proof terms of two derivations of one sequent need not be
convertible.** -/
theorem functor_not_conv : ¬ Conv (tm functor) (tm functor2) := fun h =>
  functorTm_ne (conv_nf_eq ((functor_nf.1.conv.symm.trans h).trans functor2_nf.1.conv)
    functor_nf.2 functor2_nf.2)

/-! ## The search's derivation against the one by hand -/

/-- The derivation of the search's closed tableau. -/
def searchDer (φ : PLLFormula) : Option (Explore.Der STab (goal φ)) :=
  match _root_.SubTab.solve φ with
  | .ok c => if h : check (goal φ) c = true then some (ofCert c (goal φ) h) else none
  | .error _ => none

/-- The normal form of a derivation, in writing. -/
def nfText {φ : PLLFormula} (d : Explore.Der STab (goal φ)) : String :=
  ((tm d).reduceCount 100000).1.write 0 false

/-- The search's derivation against one by hand: the moves of each, the
search's proof term and its steps, and whether the two normal forms are the
same. -/
def compare {φ : PLLFormula} (name : String) (d : Explore.Der STab (goal φ)) : String :=
  match searchDer φ with
  | none => s!"{name}: the search finds no closed tableau"
  | some e =>
    let r := (tm e).reduceCount 100000
    s!"{name}: by hand {d.script.length} moves, search {e.script.length} moves; " ++
    s!"search term of size {(tm e).size}, {r.2.1} steps, normal: {r.2.2}; " ++
    s!"same normal form: {nfText d == nfText e}" ++
    (if nfText d == nfText e then "" else s!"\n  search normal form: {nfText e}")

/--
info: unit: by hand 3 moves, search 3 moves; search term of size 21, 4 steps, normal: true; same normal form: true
-/
#guard_msgs in
#eval IO.println (compare "unit" unit)

/--
info: mult: by hand 5 moves, search 5 moves; search term of size 25, 6 steps, normal: true; same normal form: true
-/
#guard_msgs in
#eval IO.println (compare "mult" mult)

/--
info: functor: by hand 7 moves, search 17 moves; search term of size 106, 23 steps, normal: true; same normal form: false
  search normal form: λx0. λx1. let x2 ⇐ x1 in let x3 ⇐ x1 in val (x0 x2)
-/
#guard_msgs in
#eval IO.println (compare "functor" functor)

/--
info: strength: by hand 8 moves, search 9 moves; search term of size 71, 16 steps, normal: true; same normal form: true
-/
#guard_msgs in
#eval IO.println (compare "strength" strength)

/--
info: kAxiom: by hand 8 moves, search 9 moves; search term of size 52, 13 steps, normal: true; same normal form: false
  search normal form: λx0. λx1. let x2 ⇐ x0 in let x3 ⇐ x1 in let x4 ⇐ x1 in val (x2 x3)
-/
#guard_msgs in
#eval IO.println (compare "kAxiom" kAxiom)

/--
info: exFalso: by hand 4 moves, search 4 moves; search term of size 22, 3 steps, normal: true; same normal form: true
-/
#guard_msgs in
#eval IO.println (compare "exFalso" exFalso)

/--
info: twoHyps: by hand 3 moves, search 3 moves; search term of size 23, 4 steps, normal: true; same normal form: true
-/
#guard_msgs in
#eval IO.println (compare "twoHyps" twoHyps)

/--
info: chain4: by hand 16 moves, search 403 moves; search term of size 3263, 638 steps, normal: true; same normal form: false
  search normal form: λx0. λx1. λx2. λx3. λx4. let x5 ⇐ x4 in let x6 ⇐ x4 in let x7 ⇐ x4 in let x8 ⇐ x4 in let x9 ⇐ x4 in val (x3 (x2 (x1 (x0 x5))))
-/
#guard_msgs in
#eval IO.println (compare "chain4" chain4Der)

end ExploreTest
end SubTab
end PLLND

/-! ## The axioms

Upper bounds.  `nf`, `nf_spec` and `nf_unique` take `Classical.choice` from
the strong normalisation and the confluence of `Normalisation/`, pinned
there with it; the statements about the pinned derivations do without. -/

#axioms_within PLLND.SubTab.tm [propext]
#axioms_within PLLND.SubTab.nf_of_reduceFuel [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.unit_nf [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.mult_nf [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.functor_nf [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.strength_nf [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.functor2_nf [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.functorTm_ne [propext, Quot.sound]
#axioms_within PLLND.SubTab.ExploreTest.functor_not_conv [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.SubTab.nf [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.SubTab.nf_spec [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.SubTab.nf_unique [propext, Classical.choice, Quot.sound]
