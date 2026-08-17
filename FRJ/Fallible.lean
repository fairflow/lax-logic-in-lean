/-
# Fallible worlds: what they buy, and what they do not

**W3, second half.**  `FRJ/Basic.lean` gave `Kripke` the fallible worlds
of Fairtlough–Mendler's constraint models — the worlds at which `⊥` holds.
This file says exactly what they contribute.

Two constructions, pulling in opposite directions:

* `Mod(D)` (`FRJ/Extract.lean`) is BARREN — `Rm` is equality, so `◯` is the
  identity there.  That is what makes the modal introduction rule `◯∈`
  sound, and it is a ceiling: `Mod(D)` is always infallible, so soundness
  can only ever conclude `¬ IPL G`.
* `K.falTop` (here) adds a fallible world above `K`, modally visible from
  EVERY world.  In it `◯` is trivially true everywhere, `⊥` is forced at
  the top, and the model is a countermodel for `G` exactly when `K` is one
  for the `◯`-trivialisation `triv G`.

The correction that shapes the whole file: **a fallible world lying
`≤`-above `α` does not make `K,α ⊩ ◯A`.**  The `◯`-clause quantifies over
the whole `≤`-cone above `α` and asks for an `Rm`-successor of each world
in it, and `Rm` is in general a PROPER subrelation of `≤`.  `Screen.silent`
below is the two-world countermodel to the tempting claim: it HAS a
fallible top, and it still refutes `◯⊥` at the root and validates `¬◯⊥`.
What makes `falTop` work is not the fallible world's position in `≤` but
its `Rm`-visibility from everywhere.
-/
import FRJ.Sound

namespace FRJ

open Form

/-! ## The `◯`-trivialisation of a formula -/

/-- `triv A` replaces every `◯`-subformula of `A` by `⊤ = ⊥ ⊃ ⊥`.  It is
`◯`-free, so `FRJ(G)` applies to it as a goal, and by `falTop_force` it
says exactly what `A` says at the old worlds of a model with a modally
visible fallible top. -/
def triv : Form → Form
  | .atom p => .atom p
  | .bot => .bot
  | .and A B => .and (triv A) (triv B)
  | .or A B => .or (triv A) (triv B)
  | .imp A B => .imp (triv A) (triv B)
  | .circ _ => .imp .bot .bot

theorem triv_circFree : ∀ A : Form, (triv A).isCirc = false
  | .atom _ => rfl
  | .bot => rfl
  | .and _ _ => rfl
  | .or _ _ => rfl
  | .imp _ _ => rfl
  | .circ _ => rfl

/-! ## `K.falTop`: a fallible world on top, visible from everywhere -/

/-- The order of `K.falTop`: `K`'s own order, with a new top `none`. -/
inductive FTle (K : Kripke) : Option K.W → Option K.W → Prop
  | top (x : Option K.W) : FTle K x none
  | comp {a b : K.W} : K.le a b → FTle K (some a) (some b)

/-- The modal relation of `K.falTop`: `K`'s own, plus the new top seen
from EVERY world.  This — not the position of the new world in the order
— is what makes every `◯`-formula true in `K.falTop`. -/
inductive FTrm (K : Kripke) : Option K.W → Option K.W → Prop
  | top (x : Option K.W) : FTrm K x none
  | comp {a b : K.W} : K.Rm a b → FTrm K (some a) (some b)

/-- **`K` with a fallible world on top, modally visible from every
world.**  The old worlds keep their order, their valuation and their
fallibility; the new world `none` is the maximum, is fallible, and
satisfies every variable. -/
def Kripke.falTop (K : Kripke) : Kripke where
  W := Option K.W
  elems := none :: K.elems.map some
  complete := by
    rintro (_ | a)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, K.complete a, rfl⟩)
  decEq := by
    have : DecidableEq K.W := K.decEq
    exact inferInstanceAs (DecidableEq (Option K.W))
  le := FTle K
  le_refl := by rintro (_ | a); · exact .top _
                · exact .comp (K.le_refl a)
  le_trans := by
    rintro _ _ _ h₁ h₂
    cases h₂ with
    | top _ => exact .top _
    | comp hbc => cases h₁ with
      | comp hab => exact .comp (K.le_trans hab hbc)
  le_antisymm := by
    rintro _ _ h₁ h₂
    cases h₁ with
    | top _ => cases h₂ with
      | top _ => rfl
    | comp hab => cases h₂ with
      | comp hba => exact congrArg _ (K.le_antisymm hab hba)
  root := some K.root
  root_le := by
    rintro (_ | b)
    · exact .top _
    · exact .comp (K.root_le b)
  V := fun x p => match x with
    | none => True
    | some a => K.V a p
  V_mono := by
    rintro _ _ h p hp
    cases h with
    | top _ => exact trivial
    | comp hab => exact K.V_mono hab p hp
  Rm := FTrm K
  rm_refl := by rintro (_ | a); · exact .top _
                · exact .comp (K.rm_refl a)
  rm_trans := by
    rintro _ _ _ h₁ h₂
    cases h₂ with
    | top _ => exact .top _
    | comp hbc => cases h₁ with
      | comp hab => exact .comp (K.rm_trans hab hbc)
  sub_mi := by
    rintro _ _ h
    cases h with
    | top _ => exact .top _
    | comp hab => exact .comp (K.sub_mi hab)
  Fal := fun x => match x with
    | none => True
    | some a => K.Fal a
  fal_mono := by
    rintro _ _ h hf
    cases h with
    | top _ => exact trivial
    | comp hab => exact K.fal_mono hab hf
  fal_V := by
    rintro (_ | a) hf p
    · exact trivial
    · exact K.fal_V hf p
  decLe := by
    rintro (_ | a) (_ | b)
    · exact isTrue (.top _)
    · exact isFalse (fun h => by cases h)
    · exact isTrue (.top _)
    · have : Decidable (K.le a b) := K.decLe a b
      exact decidable_of_iff (K.le a b) ⟨fun h => .comp h, fun h => by cases h; assumption⟩
  decV := by
    rintro (_ | a) p
    · exact isTrue trivial
    · exact K.decV a p
  decRm := by
    rintro (_ | a) (_ | b)
    · exact isTrue (.top _)
    · exact isFalse (fun h => by cases h)
    · exact isTrue (.top _)
    · have : Decidable (K.Rm a b) := K.decRm a b
      exact decidable_of_iff (K.Rm a b) ⟨fun h => .comp h, fun h => by cases h; assumption⟩
  decFal := by
    rintro (_ | a)
    · exact isTrue trivial
    · exact K.decFal a

/-- The new top is fallible, hence forces every formula. -/
theorem falTop_top_force (K : Kripke) (A : Form) : K.falTop.force none A :=
  K.falTop.fal_force A trivial

/-- **In `K.falTop` every world forces every `◯`-formula.**  Not because
the fallible world is on top, but because it is `Rm`-visible from every
world of the cone. -/
theorem falTop_force_circ (K : Kripke) (x : K.falTop.W) (A : Form) :
    K.falTop.force x (.circ A) :=
  fun y _ => ⟨none, .top y, falTop_top_force K A⟩

/-- **The transfer theorem.**  At an old world, `K.falTop` forces `A`
exactly when `K` forces the `◯`-trivialisation of `A`.  So `K.falTop` is a
model in which the modality has been made vacuously true, and reasoning in
it is reasoning about `triv`. -/
theorem falTop_force (K : Kripke) : ∀ (A : Form) (a : K.W),
    K.falTop.force (some a) A ↔ K.force a (triv A)
  | .atom p, _ => Iff.rfl
  | .bot, _ => Iff.rfl
  | .and A B, a => by
      simp only [Kripke.force_and, triv, falTop_force K A a, falTop_force K B a]
  | .or A B, a => by
      simp only [Kripke.force_or, triv, falTop_force K A a, falTop_force K B a]
  | .imp A B, a => by
      simp only [Kripke.force_imp, triv]
      constructor
      · intro hf b hab hA
        exact (falTop_force K B b).mp
          (hf (some b) (.comp hab) ((falTop_force K A b).mpr hA))
      · intro hf y hy hA
        cases hy with
        | top _ => exact falTop_top_force K B
        | comp hab =>
            exact (falTop_force K B _).mpr (hf _ hab ((falTop_force K A _).mp hA))
  | .circ A, a => by
      constructor
      · intro _
        exact fun b _ hb => hb
      · intro _
        exact falTop_force_circ K (some a) A

/-- A countermodel for `triv G` becomes a countermodel for `G` itself once
a modally visible fallible world is put on top. -/
theorem falTop_countermodel {K : Kripke} {G : Form}
    (h : Countermodel K (triv G)) : Countermodel K.falTop G :=
  fun hv => h ((falTop_force K G K.root).mp hv)

/-- **Soundness of the fallible route.**  An `FRJ(triv G)`-derivation of
`triv G` refutes the validity of `G` in all constraint models.

This is what fallible worlds buy, and it needs no new rule: the `◯`-free
calculus refutes the trivialisation, and `falTop` turns its countermodel
into a countermodel for the modal formula.  It is a genuine addition — the
barren calculus of `FRJ/Calculus.lean` cannot reach these formulas
(`not_provable_neg_circ_bot`) — and it is also strictly weaker than a
promise rule would be, since it can only ever make `◯` vacuous. -/
theorem not_PLL_of_provable_triv {G : Form} (h : Provable (triv G)) : ¬ PLL G := by
  obtain ⟨t, Γ, ⟨d⟩⟩ := h
  exact not_PLL_of_countermodel (falTop_countermodel (modR_countermodel d))

/-! ## `¬◯⊥`: why the fallible worlds are not optional -/

/-- **Every infallible model validates `¬◯⊥`.**  `α ⊩ ◯⊥` asks for a modal
successor forcing `⊥`, i.e. for a fallible world. -/
theorem valid_neg_circ_bot_of_infallible {K : Kripke} (hK : K.Infallible) :
    K.valid (Form.neg (.circ .bot)) := by
  intro v _ hv
  obtain ⟨u, _, hu⟩ := hv v (K.le_refl v)
  exact absurd hu (hK u)

/-- Hence `¬◯⊥` is valid in the paper's sense. -/
theorem IPL_neg_circ_bot : IPL (Form.neg (.circ .bot)) :=
  fun _ hK => valid_neg_circ_bot_of_infallible hK

/-- **`FRJ(G)` cannot refute `¬◯⊥`** — nor can any extension of it whose
extracted models are infallible.  This is a genuine incompleteness, not an
accident of the rules: soundness concludes `¬ IPL G`, and `¬◯⊥` has `IPL`.
Together with `not_PLL_neg_circ_bot` below it says that the formula is not
valid in the logic and is out of the calculus's reach. -/
theorem not_provable_barren_neg_circ_bot {t : Tag} {Γ : List Form}
    (d : FRJr (Form.neg (.circ .bot)) t Γ (Form.neg (.circ .bot))) :
    ¬ (modR d).Infallible := fun hinf =>
  modR_countermodel d
    (valid_neg_circ_bot_of_infallible (K := modR d) hinf)

/-! ## Two models

`point` is the one-world infallible model; `point.falTop` is the two-world
fallible one that does the refuting. -/

/-- The one-world model, no variable true, no fallible world. -/
def Kripke.point : Kripke where
  W := Unit
  elems := [()]
  complete := fun _ => List.mem_cons_self
  decEq := inferInstance
  le := fun _ _ => True
  le_refl := fun _ => trivial
  le_trans := fun _ _ => trivial
  le_antisymm := fun {a b} _ _ => Subsingleton.elim a b
  root := ()
  root_le := fun _ => trivial
  V := fun _ _ => False
  V_mono := fun _ _ h => h
  Rm := fun _ _ => True
  rm_refl := fun _ => trivial
  rm_trans := fun _ _ => trivial
  sub_mi := fun _ => trivial
  Fal := fun _ => False
  fal_mono := fun _ h => h
  fal_V := fun h => h.elim
  decLe := fun _ _ => isTrue trivial
  decV := fun _ _ => isFalse (fun h => h)
  decRm := fun _ _ => isTrue trivial
  decFal := fun _ => isFalse (fun h => h)

theorem point_infallible : Kripke.point.Infallible := fun _ h => h

/-- **`¬◯⊥` is not valid in all constraint models.**  In `point.falTop` the
root forces `◯⊥` — the fallible top is one of its modal successors — and
refutes `⊥`. -/
theorem not_PLL_neg_circ_bot : ¬ PLL (Form.neg (.circ .bot)) := by
  refine not_PLL_of_countermodel (K := Kripke.point.falTop) ?_
  intro hv
  exact hv Kripke.point.falTop.root (Kripke.point.falTop.le_refl _)
    (falTop_force_circ Kripke.point _ .bot)

/-- **`◯p ⊃ p` is not valid either**, by the same model: the root forces
`◯p` and refutes `p`. -/
theorem not_PLL_circ_imp (p : String) :
    ¬ PLL (Form.imp (.circ (.atom p)) (.atom p)) := by
  refine not_PLL_of_countermodel (K := Kripke.point.falTop) ?_
  intro hv
  exact hv Kripke.point.falTop.root (Kripke.point.falTop.le_refl _)
    (falTop_force_circ Kripke.point _ (.atom p))

/-! ## The screen for the correction

A fallible world `≤`-above a world says NOTHING about `◯` there.  The
model below has a fallible top and still refutes `◯⊥` at the root — and so
validates `¬◯⊥`, exactly as `valid_neg_circ_bot_of_infallible` would if it
were about `≤` rather than about `Rm`. -/

namespace Screen

/-- Two worlds: `w` below the fallible `f`. -/
inductive WF where | w | f
  deriving DecidableEq, Repr

/-- The order on `WF`, as a `Bool`. -/
def leF : WF → WF → Bool
  | .w, _ => true
  | .f, .f => true
  | .f, .w => false

/-- `w < f` with `f` fallible, and `Rm` EQUALITY: the fallible world is
above `w` in the order but is not a modal successor of it. -/
abbrev silent : Kripke where
  W := WF
  elems := [.w, .f]
  complete := by intro x; cases x <;> simp
  decEq := inferInstance
  le := fun a b => leF a b = true
  le_refl := by intro a; cases a <;> rfl
  le_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [leF]
  le_antisymm := by intro a b h₁ h₂; cases a <;> cases b <;> simp_all [leF]
  root := .w
  root_le := by intro a; cases a <;> rfl
  V := fun x _ => x = .f
  V_mono := by intro a b h s hs; cases a <;> cases b <;> simp_all [leF]
  Rm := fun a b => a = b
  rm_refl := fun _ => rfl
  rm_trans := fun h₁ h₂ => h₁.trans h₂
  sub_mi := by rintro a b rfl; cases a <;> rfl
  Fal := fun x => x = .f
  fal_mono := by intro a b h hf; cases a <;> cases b <;> simp_all [leF]
  fal_V := by intro a hf p; exact hf
  decLe := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decV := fun _ _ => inferInstanceAs (Decidable (_ = _))
  decRm := fun _ _ => inferInstanceAs (Decidable (_ = _))
  decFal := fun _ => inferInstanceAs (Decidable (_ = _))

/-- **The correction, machine-checked.**  `silent` HAS a fallible world,
and it lies above the root in the order; the root nevertheless refutes
`◯⊥` and `◯p`, and validates `¬◯⊥`.  So "a model with a fallible top
forces every `◯`-formula" is FALSE: what is needed is `Rm`-visibility of
the fallible world from the whole cone, which `Kripke.falTop` arranges and
`silent` does not. -/
example :
    ¬ silent.force .w (.circ .bot)
    ∧ ¬ silent.force .w (.circ (.atom "p"))
    ∧ silent.force .w (Form.neg (.circ .bot))
    ∧ silent.Fal .f := by decide

/-- The same model shows fallibility is not vacuous either: at the
fallible world every formula holds. -/
example : silent.force .f (.circ .bot) ∧ silent.force .f .bot := by decide

end Screen

/-! ## The two routes are incomparable

Both are machine-checked below, on the two formulas that separate them.

The BARREN route (`◯∈`, `Mod(D)`) refutes `◯p`: `Ax^R` refutes `p` at a
world whose only modal successor is itself.  The fallible route cannot,
because `triv (◯p) = ⊤` is valid and has no derivation.

The FALLIBLE route (`triv`, `falTop`) refutes `¬◯⊥` and `◯p ⊃ p`.  The
barren route cannot refute the first — that is `not_provable_neg_circ_bot`,
which holds for every extension whose models are infallible. -/

/-- The barren route on `◯p`: `Ax^R` then `◯∈`. -/
theorem provable_circ_atom (p : String) : Provable (Form.circ (.atom p)) :=
  ⟨.barren, _, ⟨FRJr.circIn (FRJr.axR (.atom p) rfl (by simp [sfR, sfPos]))
    (Or.inl rfl) (sfR_self _)⟩⟩

theorem not_PLL_circ_atom (p : String) : ¬ PLL (Form.circ (.atom p)) :=
  soundness (provable_circ_atom p)

/-- The fallible route cannot reach `◯p`: its trivialisation is `⊤`. -/
theorem not_provable_triv_circ_atom (p : String) :
    ¬ Provable (triv (Form.circ (.atom p))) :=
  fun h => soundness h (fun _ _ _ hb => hb)

/-- **The fallible route on `¬◯⊥`, as an actual derivation.**  `Ax^I` at
`⊥` puts `⊥ ⊃ ⊥` in the irregular zone, the join keeps it by the
restriction (its antecedent `⊥` is the premise's right formula), and `⊃∈`
discharges it from the closure. -/
theorem provable_triv_neg_circ_bot : Provable (triv (Form.neg (.circ .bot))) := by
  have hax : FRJi (Form.imp (Form.imp .bot .bot) .bot) []
      (nf (Form.imp (Form.imp .bot .bot) .bot)
        ((rm (gAt (Form.imp (Form.imp .bot .bot) .bot)) .bot)
          ++ gImp (Form.imp (Form.imp .bot .bot) .bot) ++ gCirc (Form.imp (Form.imp .bot .bot) .bot))) .bot :=
    FRJi.axI .bot rfl (by decide)
  have hjoin := FRJr.joinAt (G := Form.imp (Form.imp .bot .bot) .bot) (n := 0)
      (stab := fun _ => []) (rhs := fun _ => .bot) (F := .bot)
      (fun _ => hax)
      (by intro i j h; exact absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) h)
      (by intro A B h; simp [unionAll, impPart] at h)
      (by simp [unionAll, circPart])
      rfl
      (by simp [unionAll, atPart])
      (by decide)
  exact ⟨.barren, _, ⟨FRJr.impIn hjoin (Clo.base (by decide)) (by decide)⟩⟩

/-- The same for `◯p ⊃ p`, the formula that made the promise problem
concrete in `docs/frj-modal-rules.md` §4.3. -/
theorem provable_triv_circ_imp :
    Provable (triv (Form.imp (.circ (.atom "p")) (.atom "p"))) := by
  have hax : FRJi (Form.imp (Form.imp .bot .bot) (.atom "p")) []
      (nf (Form.imp (Form.imp .bot .bot) (.atom "p"))
        ((rm (gAt (Form.imp (Form.imp .bot .bot) (.atom "p"))) .bot)
          ++ gImp (Form.imp (Form.imp .bot .bot) (.atom "p")) ++ gCirc (Form.imp (Form.imp .bot .bot) (.atom "p")))) .bot :=
    FRJi.axI .bot rfl (by decide)
  have hjoin := FRJr.joinAt (G := Form.imp (Form.imp .bot .bot) (.atom "p")) (n := 0)
      (stab := fun _ => []) (rhs := fun _ => .bot) (F := .atom "p")
      (fun _ => hax)
      (by intro i j h; exact absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) h)
      (by intro A B h; simp [unionAll, impPart] at h)
      (by simp [unionAll, circPart])
      rfl
      (by simp [unionAll, atPart])
      (by decide)
  exact ⟨.barren, _, ⟨FRJr.impIn hjoin (Clo.base (by decide)) (by decide)⟩⟩

/-- **`¬◯⊥` refuted through the calculus**, not merely by exhibiting a
model: `provable_triv_neg_circ_bot` is an `FRJ`-derivation, and `falTop`
turns its countermodel into a countermodel for `¬◯⊥`.  Compare
`not_provable_neg_circ_bot`: the barren calculus cannot do this. -/
theorem not_PLL_neg_circ_bot_via_calculus : ¬ PLL (Form.neg (.circ .bot)) :=
  not_PLL_of_provable_triv provable_triv_neg_circ_bot

theorem not_PLL_circ_imp_via_calculus :
    ¬ PLL (Form.imp (.circ (.atom "p")) (.atom "p")) :=
  not_PLL_of_provable_triv provable_triv_circ_imp

/-! ## What the choice of modal relation costs

Each uniform choice of `Rm` realises a NUCLEUS, and the calculus then
refutes `G` exactly when the image of `G` under that nucleus is
IPC-refutable.  Three choices are available here, and they are the three
simplest nuclei:

    Rm := Eq         ◯A ≡ A          the identity
    Rm := ≤          ◯A ≡ ¬¬A        double negation (infallible models)
    K.falTop         ◯A ≡ ⊤          the trivialisation

None of them is generic, and no two are comparable.  Each therefore has a
blind spot that is a THEOREM about the construction, not an accident of the
rules: the identity choice validates `◯A ⊃ A`, the double-negation choice
validates `¬¬A ⊃ ◯A`, and neither formula is valid in the logic.  Both
blind spots are proved below. -/

/-- **`Rm = Eq` makes the modality the identity.**  Stated for an arbitrary
model, so that it is a fact about the CHOICE and not about `toKripke`. -/
theorem force_circ_iff_self {K : Kripke} (hRm : ∀ a b, K.Rm a b ↔ a = b)
    (w : K.W) (A : Form) : K.force w (.circ A) ↔ K.force w A := by
  constructor
  · intro h
    obtain ⟨c, hc, hcA⟩ := h w (K.le_refl w)
    have hwc : w = c := (hRm w c).mp hc
    subst hwc; exact hcA
  · intro h b hb
    exact ⟨b, (hRm b b).mpr rfl, K.force_mono hb h⟩

/-- **`Rm = ≤` makes the modality double negation**, in an infallible
model.  This is W1's choice, the one W3 replaced; the reverse implication
needs no `Classical.choice`, because forcing is decidable and the world
enumeration is finite. -/
theorem force_circ_iff_nn {K : Kripke} (hRm : ∀ a b, K.Rm a b ↔ K.le a b)
    (hinf : K.Infallible) (w : K.W) (A : Form) :
    K.force w (.circ A) ↔ K.force w (Form.neg (Form.neg A)) := by
  constructor
  · intro h v hwv hv
    obtain ⟨c, hmc, hc⟩ := h v hwv
    exact absurd (hv c ((hRm v c).mp hmc) hc) (hinf c)
  · intro h v hwv
    have hdec : Decidable (∃ u, K.le v u ∧ K.force u A) :=
      decidable_of_iff (∃ u ∈ K.elems, K.le v u ∧ K.force u A)
        ⟨fun ⟨u, _, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, K.complete u, hu⟩⟩
    have key : ∃ u, K.le v u ∧ K.force u A :=
      @Decidable.byContradiction _ hdec (fun hcon =>
        hinf v (h v hwv (fun u hvu hu => absurd
          (⟨u, hvu, hu⟩ : ∃ u, K.le v u ∧ K.force u A) hcon)))
    obtain ⟨u, hvu, hu⟩ := key
    exact ⟨u, (hRm v u).mpr hvu, hu⟩

/-- **The fallible JOIN reaches `¬◯⊥` inside the calculus.**  `Ax^I` at
`⊥` puts `◯⊥` (now in `Ĝ_◯`) into the irregular zone, the fallible join
keeps the whole modal zone and declares a fallible modal successor for
the new world, and `⊃∈` discharges `◯⊥` from the closure.  Under W3's
uniform identity choice this was PROVABLY out of reach
(`not_provable_barren_neg_circ_bot` is what remains of that fact: any
derivation of `¬◯⊥` has a fallible world in its extracted model). -/
theorem provable_neg_circ_bot : Provable (Form.neg (.circ .bot)) := by
  have hax : FRJi (Form.neg (.circ .bot)) []
      (nf (Form.neg (.circ .bot))
        ((rm (gAt (Form.neg (.circ .bot))) .bot)
          ++ gImp (Form.neg (.circ .bot)) ++ gCirc (Form.neg (.circ .bot)))) .bot :=
    FRJi.axI .bot rfl (by decide)
  have hjoin := FRJr.joinAtF (G := Form.neg (.circ .bot)) (n := 0)
      (stab := fun _ => []) (rhs := fun _ => .bot) (F := .bot)
      (fun _ => hax)
      (by intro i j h; exact absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) h)
      (by intro A B h; simp [unionAll, impPart] at h)
      rfl
      (by simp [unionAll, atPart])
      (by decide)
  exact ⟨.blocked, _, ⟨FRJr.impIn hjoin (Clo.base (by decide)) (by decide)⟩⟩

/-- The same for `◯p ⊃ p` — the sharp instance of the design discussion,
now refuted by the calculus itself. -/
theorem provable_circ_imp : Provable (Form.imp (.circ (.atom "p")) (.atom "p")) := by
  have hax : FRJi (Form.imp (.circ (.atom "p")) (.atom "p")) []
      (nf (Form.imp (.circ (.atom "p")) (.atom "p"))
        ((rm (gAt (Form.imp (.circ (.atom "p")) (.atom "p"))) (.atom "p"))
          ++ gImp (Form.imp (.circ (.atom "p")) (.atom "p"))
          ++ gCirc (Form.imp (.circ (.atom "p")) (.atom "p")))) (.atom "p") :=
    FRJi.axI (.atom "p") rfl (by decide)
  have hjoin := FRJr.joinAtF (G := Form.imp (.circ (.atom "p")) (.atom "p")) (n := 0)
      (stab := fun _ => []) (rhs := fun _ => .atom "p") (F := .atom "p")
      (fun _ => hax)
      (by intro i j h; exact absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) h)
      (by intro A B h; simp [unionAll, impPart] at h)
      rfl
      (by simp [unionAll, atPart])
      (by decide)
  exact ⟨.blocked, _, ⟨FRJr.impIn hjoin (Clo.base (by decide)) (by decide)⟩⟩

/-- **The `◯∉` witness cell** (W4): `(◯p ⊃ q) ⊃ q` is reached by the
calculus.  Under the W3 rule set no irregular sequent had a modal right
formula — right formulas originated prime at the axioms and grew only by
`∧`, `∨`, `⊃` on the irregular side — so `Υ` never contained a
`◯`-formula and the context restriction could never keep an implication
with modal antecedent: every context containing `◯p ⊃ q` was
unreachable, and with it this goal.  `◯∉` repairs exactly that
(`docs/frj-w4.md` §1 (D2)): `Ax^R` at `p` gives a barren `⇒ p`, `◯∉`
turns it into `[] ; [◯p ⊃ q] → ◯p` (the zone lands in `Cl` by
`Clo.imp` from `q`), the join at `q` now sees `◯p ∈ Υ` and keeps
`◯p ⊃ q`, and `⊃∈` discharges. -/
theorem provable_circ_peirce :
    Provable (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q")) := by
  have haxp : FRJr (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q"))
      .barren
      (rm (gAt (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q")))
        (.atom "p"))
      (.atom "p") :=
    FRJr.axR (.atom "p") rfl (by decide)
  have hnotin : FRJi (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q"))
      [] [Form.imp (.circ (.atom "p")) (.atom "q")] (.circ (.atom "p")) :=
    FRJi.circNotIn haxp (Or.inl rfl)
      (by
        intro Y hY
        have hYX : Y = Form.imp (.circ (.atom "p")) (.atom "q") := by simpa using hY
        subst hYX
        exact ⟨Clo.imp (Clo.base (by decide)), by decide⟩)
      (by decide)
  have haxq : FRJi (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q"))
      []
      (nf (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q"))
        ((rm (gAt (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q")))
            (.atom "q"))
          ++ gImp (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q"))
          ++ gCirc (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q"))))
      (.atom "q") :=
    FRJi.axI (.atom "q") rfl (by decide)
  have hjoin := FRJr.joinAt
      (G := Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q")) (n := 1)
      (stab := fun _ => [])
      (th := fun j => match j with
        | ⟨0, _⟩ =>
            nf (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q"))
              ((rm (gAt (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q")))
                  (.atom "q"))
                ++ gImp (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q"))
                ++ gCirc (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q")))
        | ⟨1, _⟩ => [Form.imp (.circ (.atom "p")) (.atom "q")])
      (rhs := fun j => match j with
        | ⟨0, _⟩ => .atom "q"
        | ⟨1, _⟩ => .circ (.atom "p"))
      (F := .atom "q")
      (fun j => match j with
        | ⟨0, _⟩ => haxq
        | ⟨1, _⟩ => hnotin)
      (by intro i j _ x hx; simp at hx)
      (by intro A B h; simp [unionAll, impPart] at h)
      (by decide)
      rfl
      (by decide)
      (by decide)
  exact ⟨.barren, _, ⟨FRJr.impIn hjoin (Clo.base (by decide)) (by decide)⟩⟩

theorem not_PLL_circ_peirce_by_calculus :
    ¬ PLL (Form.imp (Form.imp (.circ (.atom "p")) (.atom "q")) (.atom "q")) :=
  soundness provable_circ_peirce

/-- Hence the two standing cells, straight from soundness. -/
theorem not_PLL_neg_circ_bot_by_calculus : ¬ PLL (Form.neg (.circ .bot)) :=
  soundness provable_neg_circ_bot

theorem not_PLL_circ_imp_by_calculus :
    ¬ PLL (Form.imp (.circ (.atom "p")) (.atom "p")) :=
  soundness provable_circ_imp

/-- **The blind spot of the double-negation choice**, for comparison: a
model whose modal relation is its order validates `¬¬A ⊃ ◯A`, which is not
valid in the logic either.  So reverting `Rm` to `≤` would trade one blind
spot for another rather than remove it. -/
theorem valid_nn_imp_circ {K : Kripke} (hRm : ∀ a b, K.Rm a b ↔ K.le a b)
    (hinf : K.Infallible) (A : Form) :
    K.valid (Form.imp (Form.neg (Form.neg A)) (.circ A)) :=
  fun v _ hv => (force_circ_iff_nn hRm hinf v A).mpr hv

/-- **The `Ax^I◯` witness cell**: `¬¬◯⊥`, the standing flag of the
saturation corpus (`docs/frj-w4.md` §7) — underivable before the axiom was
added (the `◯∉` cycle: `Cl(∅)` cannot see vacuous forcing), derivable now.
The join marries the classical axiom `Ax^I` for `⊥` with the mounted BARE
final world of `Ax^I◯`.  Semantically (Matthew's reading): `◯⊥` behaves as
an ATOM — valuation-free, persistent, forced at `u` iff hereditarily every
`v ≥ u` has `v Rm f` for some fallible `f` — and the maximal infallible
worlds split into the two species bare/`◯⊥`-false vs decorated/`◯⊥`-true;
this axiom supplies the bare half of that seed enumeration, the fallible
join the decorated half. -/
theorem provable_nn_circ_bot :
    Provable (Form.neg (Form.neg (.circ .bot))) := by
  have haxb : FRJi (Form.neg (Form.neg (.circ .bot))) []
      (nf (Form.neg (Form.neg (.circ .bot)))
        ((rm (gAt (Form.neg (Form.neg (.circ .bot)))) .bot)
          ++ gImp (Form.neg (Form.neg (.circ .bot)))
          ++ gCirc (Form.neg (Form.neg (.circ .bot)))))
      .bot :=
    FRJi.axI .bot rfl (by decide)
  have haxc : FRJi (Form.neg (Form.neg (.circ .bot))) []
      (vacZone (Form.neg (Form.neg (.circ .bot))) .bot) (.circ .bot) :=
    FRJi.axIC .bot (rm (gAt (Form.neg (Form.neg (.circ .bot)))) .bot)
      (fun _ h => rm_subset h) rfl (by decide)
  have hjoin := FRJr.joinAt
      (G := Form.neg (Form.neg (.circ .bot))) (n := 1)
      (stab := fun _ => [])
      (th := fun j => match j with
        | ⟨0, _⟩ =>
            nf (Form.neg (Form.neg (.circ .bot)))
              ((rm (gAt (Form.neg (Form.neg (.circ .bot)))) .bot)
                ++ gImp (Form.neg (Form.neg (.circ .bot)))
                ++ gCirc (Form.neg (Form.neg (.circ .bot))))
        | ⟨1, _⟩ => vacZone (Form.neg (Form.neg (.circ .bot))) .bot)
      (rhs := fun j => match j with
        | ⟨0, _⟩ => .bot
        | ⟨1, _⟩ => .circ .bot)
      (F := .bot)
      (fun j => match j with
        | ⟨0, _⟩ => haxb
        | ⟨1, _⟩ => haxc)
      (by intro i j _ x hx; simp at hx)
      (by intro A B h; simp [unionAll, impPart] at h)
      (by decide)
      rfl
      (by decide)
      (by decide)
  exact ⟨.barren, _, ⟨FRJr.impIn hjoin (Clo.base (by decide)) (by decide)⟩⟩

theorem not_PLL_nn_circ_bot_by_calculus :
    ¬ PLL (Form.neg (Form.neg (.circ .bot))) :=
  soundness provable_nn_circ_bot

/-! ## Axiom audit -/

/-- info: 'FRJ.falTop_force' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms falTop_force

/-- info: 'FRJ.not_PLL_of_provable_triv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_PLL_of_provable_triv

/-- info: 'FRJ.IPL_neg_circ_bot' does not depend on any axioms -/
#guard_msgs in
#print axioms IPL_neg_circ_bot

/-- info: 'FRJ.provable_neg_circ_bot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provable_neg_circ_bot

/-- info: 'FRJ.not_PLL_neg_circ_bot_by_calculus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_PLL_neg_circ_bot_by_calculus

/-- info: 'FRJ.provable_circ_imp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provable_circ_imp

/-- info: 'FRJ.provable_circ_peirce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provable_circ_peirce

/-- info: 'FRJ.not_PLL_circ_peirce_by_calculus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_PLL_circ_peirce_by_calculus

/-- info: 'FRJ.not_PLL_neg_circ_bot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_PLL_neg_circ_bot

/-- info: 'FRJ.provable_triv_neg_circ_bot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provable_triv_neg_circ_bot

/-- info: 'FRJ.not_PLL_neg_circ_bot_via_calculus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_PLL_neg_circ_bot_via_calculus

/-- info: 'FRJ.provable_circ_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provable_circ_atom

/-- info: 'FRJ.force_circ_iff_nn' does not depend on any axioms -/
#guard_msgs in
#print axioms force_circ_iff_nn

/-- info: 'FRJ.not_provable_barren_neg_circ_bot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_provable_barren_neg_circ_bot

/-- info: 'FRJ.provable_nn_circ_bot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provable_nn_circ_bot

/-- info: 'FRJ.not_PLL_nn_circ_bot_by_calculus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_PLL_nn_circ_bot_by_calculus

end FRJ
