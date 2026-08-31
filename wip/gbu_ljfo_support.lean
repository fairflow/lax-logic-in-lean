/-
# LJF◯ → Gbu◯: the support layer (stage F3 of the route change)

`docs/frjw-plan.md` "Route change" section.  The translation
`wip/gbu_ljfo.lean` needs:

* the formula maps `pf`/`nf` from polarised LJF◯ syntax into `FRJ.Form`,
  with `nf (negOfO φ) = ofPLL φ` so the final composition with
  `bridge_iff` is definitional;
* the `Clo`-INVERSION lemmas (read off `cloB`): they drive the
  hoist-pass's member-vs-derived case splits;
* `regOfIrr`: the irregular judgment of `Gbu◯(G)` is SUBSUMED by the
  regular one, constructor by constructor.

## Screening record (F2, counterexample-first)

Two design-forcing facts, both established here as kernel-checked
refutations:

* **`GbuIC` is NOT monotone** (`gbuIC_not_monotone`):
  `[] →g (x∨y) ⊃ (y∨x)` is derivable (`R⊃ₙᵢ` releases to the regular
  judgment, which case-splits), but `[x∨y] →g (x∨y) ⊃ (y∨x)` is NOT —
  `R⊃ᵢ` demands an irregular `y∨x`, and the irregular judgment cannot
  case-split at a non-`◯` goal; `R⊃ₙᵢ` is blocked because the
  antecedent is now in the closure.  Consequence: the translation must
  never transport an irregular derivation across context growth — it
  re-produces them at their consumption context (the `ib` family).
* **The irregular judgment has no modus ponens**
  (`gbuIC_no_mp`): `[q ⊃ p, q] →g p` is underivable — at an atomic
  irregular goal only `Ax` applies.  Consequence: left activity
  (including every `L⊃` step of an LJF◯ derivation) must be HOISTED to
  the regular judgment (the `hp` family); the size-conditioned `L⊃ᵢ`
  is never used, and the `|◯C|`-adaptation licence is not exercised.
-/
import LJF.OBridge
import wip.gbu_circ

namespace FRJ.Gbu.LJFT

open FRJ Form LJFO

/-! ## The formula maps -/

/-- A positive LJF◯ proposition as an `FRJ.Form`: erase, then cross the
`PLLFormula ≃ Form` isomorphism. -/
def pf (P : LJFO.Pos) : Form := ofPLL (LJFO.erasePos P)

/-- A negative LJF◯ proposition as an `FRJ.Form`. -/
def nf (N : LJFO.Neg) : Form := ofPLL (LJFO.eraseNeg N)

@[simp] theorem pf_atom {a : String} : pf (.atom a) = .atom a := rfl
@[simp] theorem pf_fls : pf .fls = .bot := rfl
@[simp] theorem pf_or {P Q : Pos} : pf (.or P Q) = .or (pf P) (pf Q) := rfl
@[simp] theorem pf_down {N : Neg} : pf (.down N) = nf N := rfl
@[simp] theorem nf_up {P : Pos} : nf (.up P) = pf P := rfl
@[simp] theorem nf_imp {Q : Pos} {N : Neg} :
    nf (.imp Q N) = .imp (pf Q) (nf N) := rfl
@[simp] theorem nf_and {M N : Neg} : nf (.and M N) = .and (nf M) (nf N) := rfl
@[simp] theorem nf_circ {P : Pos} : nf (.circ P) = .circ (pf P) := rfl

/-- The composition fact the final theorem rests on. -/
theorem nf_negOfO (φ : PLLFormula) : nf (negOfO φ) = ofPLL φ := by
  unfold nf; rw [(erase_polarise φ).2]

/-! ## `Clo` inversion

`Clo`'s constructors are syntax-directed on the head, so each shape
inverts by one `cases`. -/

theorem clo_atom_mem {Ψ : List Form} {a : String}
    (h : Clo Ψ (.atom a)) : Form.atom a ∈ Ψ := by
  cases h with | base h => exact h

theorem clo_bot_mem {Ψ : List Form} (h : Clo Ψ .bot) : Form.bot ∈ Ψ := by
  cases h with | base h => exact h

theorem clo_and_inv {Ψ : List Form} {A B : Form}
    (h : Clo Ψ (.and A B)) : Form.and A B ∈ Ψ ∨ (Clo Ψ A ∧ Clo Ψ B) := by
  cases h with
  | base h => exact Or.inl h
  | and h₁ h₂ => exact Or.inr ⟨h₁, h₂⟩

theorem clo_or_inv {Ψ : List Form} {A B : Form}
    (h : Clo Ψ (.or A B)) : Form.or A B ∈ Ψ ∨ Clo Ψ A ∨ Clo Ψ B := by
  cases h with
  | base h => exact Or.inl h
  | orR h => exact Or.inr (Or.inr h)
  | orL h => exact Or.inr (Or.inl h)

theorem clo_imp_inv {Ψ : List Form} {A B : Form}
    (h : Clo Ψ (.imp A B)) : Form.imp A B ∈ Ψ ∨ Clo Ψ B := by
  cases h with
  | base h => exact Or.inl h
  | imp h => exact Or.inr h

theorem clo_circ_inv {Ψ : List Form} {Z : Form}
    (h : Clo Ψ (.circ Z)) : Form.circ Z ∈ Ψ ∨ Clo Ψ Z := by
  cases h with
  | base h => exact Or.inl h
  | circ h => exact Or.inr h

/-! ## The irregular judgment is subsumed by the regular one -/

/-- Every `Gbu◯(G)` irregular derivation is a regular one: each `GbuIC`
constructor has a `GbuRC` counterpart with the same premises (and the
regular counterparts of the `◯`-goal left rules carry FEWER side
conditions — `limpL` drops `L⊃ᵢ`'s size condition). -/
def regOfIrr {G : Form} : ∀ {Ψ : List Form} {C : Form},
    GbuIC G Ψ C → GbuRC G Ψ C
  | _, _, .ax A hΓ => .ax A hΓ
  | _, _, .randI d₁ d₂ => .randR (regOfIrr d₁) (regOfIrr d₂)
  | _, _, .rorI1 d => .rorR1 d
  | _, _, .rorI2 d => .rorR2 d
  | _, _, .rimpII d hA => .rimpI (regOfIrr d) hA
  | _, _, .rimpNII d hA => .rimpNI d hA
  | _, _, .lcircI d hprin hΓ => .lcirc (regOfIrr d) hprin hΓ
  | _, _, .limpLI d₁ d₂ _ _ hΓ => .limpL d₁ (regOfIrr d₂) hΓ
  | _, _, .lbotI _ hΓ => .lbot _ hΓ
  | _, _, .landLI d _ hΓ => .landL (regOfIrr d) hΓ
  | _, _, .lorLI d₁ d₂ _ hΓ => .lorL (regOfIrr d₁) (regOfIrr d₂) hΓ
  | _, _, .rcircI d hgoal => .rcirc d hgoal

/-! ## The screening refutations -/

private def xv : Form := .atom "x"
private def yv : Form := .atom "y"

/-- `[] →g (x∨y) ⊃ (y∨x)` IS derivable: `R⊃ₙᵢ` releases to the regular
judgment, and the regular judgment case-splits. -/
def irrFlip_nil {G : Form} :
    GbuIC G [] (.imp (.or xv yv) (.or yv xv)) :=
  .rimpNII
    (.lorL (.rorR2 (.ax xv (CtxEq.refl _)))
      (.rorR1 (.ax yv (CtxEq.refl _)))
      (CtxEq.refl _))
    (fun h => by
      rcases clo_or_inv h with h | h | h
      · exact absurd h List.not_mem_nil
      · exact absurd (clo_atom_mem h) List.not_mem_nil
      · exact absurd (clo_atom_mem h) List.not_mem_nil)

/-- **`GbuIC` is not monotone**: the same formula has NO irregular
derivation once `x∨y` joins the context.  Exhaustive: the goal is an
implication, so only `Ax`, `R⊃ᵢ`, `R⊃ₙᵢ` can conclude it; `Ax` fails on
membership, `R⊃ₙᵢ` on the closure side condition, and `R⊃ᵢ` demands an
irregular `y∨x` over `[x∨y]`, where only `R∨ₖ`/`Ax` apply and both
disjunct goals are atoms absent from the context. -/
theorem gbuIC_not_monotone {G : Form} :
    ¬ Nonempty (GbuIC G [.or xv yv] (.imp (.or xv yv) (.or yv xv))) := by
  rintro ⟨d⟩
  cases d with
  | ax _ hΓ =>
      have := (hΓ (.imp (.or xv yv) (.or yv xv))).mpr List.mem_cons_self
      simp [xv, yv] at this
  | rimpNII _ hA => exact hA (.base List.mem_cons_self)
  | rimpII d _ =>
      cases d with
      | ax _ hΓ =>
          have := (hΓ (.or yv xv)).mpr List.mem_cons_self
          simp [xv, yv] at this
      | rorI1 d =>
          cases d with
          | ax _ hΓ =>
              have := (hΓ yv).mpr List.mem_cons_self
              simp [xv, yv] at this
      | rorI2 d =>
          cases d with
          | ax _ hΓ =>
              have := (hΓ xv).mpr List.mem_cons_self
              simp [xv, yv] at this

private def qv' : Form := .atom "q"
private def pv' : Form := .atom "p"

/-- **The irregular judgment has no modus ponens**: `[q ⊃ p, q] →g p`
is underivable — at an atomic irregular goal only `Ax` applies. -/
theorem gbuIC_no_mp {G : Form} :
    ¬ Nonempty (GbuIC G [.imp qv' pv', qv'] pv') := by
  rintro ⟨d⟩
  cases d with
  | ax _ hΓ =>
      have := (hΓ pv').mpr List.mem_cons_self
      simp [pv', qv'] at this

end FRJ.Gbu.LJFT
