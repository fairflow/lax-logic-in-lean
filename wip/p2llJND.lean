import wip.p2llSyntax
import wip.p2llND

/-!
# The guarded calculus: J-formulas, `JND`, and the definability cells

File 3 of the P2LL definability campaign (`wip/p2ll-STATUS.md`).

The guarded calculus has no `◯` and a primitive relativised quantifier `∀°`:
`∀°I` declares its eigenvariable a J-variable, `∀°E` instantiates only with a
J-formula.  The judgement

    JND J Θ Γ φ        "under J-declarations Θ and hypotheses Γ, φ"

carries the declarations `Θ : List String`; the parameter `J` is the class of
admissible instances, and the calculus proper is `JND IsJ`.  The relativisation
into P2LL (OPEN, `wip/p2llStatements.lean`) sends `Θ` to the guards `◯s → s`.

`IsJ Θ` is the syntactic J-grammar: J-variables, `⊤`, `φ → J`, `J ∧ J`, `∀.J`,
`∀°.J`.  Each clause is a closure property of the fixed-point set of a nucleus
(`wip/f0MacNeille.lean`: closed under arbitrary meets and `x ↠ (−)`); `⊥` and
`∨` are excluded, see C3 and C6.

The defined modality is `◯°φ := ∀°q.((φ → q) → q)` (`Fm.circJ`).  Cells:

* C1 unit:  `Γ ⊢ φ  ⟹  Γ ⊢ ◯°φ`                     (`JND.circJ_intro`)
* C2 bind:  `Γ ⊢ ◯°φ, Γ, φ ⊢ ◯°ψ  ⟹  Γ ⊢ ◯°ψ`       (`JND.circJ_bind`)
  Both use J-VARIABLE instances only, so they hold for every `J` containing the
  declared variables; ◯R, ◯M, ◯S and ◯bind follow (`OI`, `OM`, `OS`, `Obind`).
* C3 guard drop:  `J Θ χ  ⟹  ◯°χ ⊢ χ`               (`JND.circJ_collapse`)
  Admitting `χ` to the instances makes `χ` a fixpoint of `◯°`.  At `χ := ⊥`
  this is `◯°⊥ ⊢ ⊥`, which PLL refutes (`PLLND.not_provable_not_somehow_false`);
  with every formula admitted (`J := fun _ _ => True`, the ◯-free instance) `◯°`
  is the identity, as `rp` is in IPC2 (`wip/p2llND.lean`, F1).
-/

namespace P2LL

open Fm

/-- The J-formulas under the declarations `Θ`: the syntactic grammar of the
fixed points.  `⊤ := ⊥ → ⊥` has its own clause because `⊥` is not a J-formula. -/
inductive IsJ : List String → Fm → Prop
  | var {Θ : List String} {s : String} (h : s ∈ Θ) : IsJ Θ (.fvar s)
  | top {Θ : List String} : IsJ Θ Fm.top
  | imp {Θ : List String} {φ ψ : Fm} (h : IsJ Θ ψ) : IsJ Θ (.imp φ ψ)
  | and {Θ : List String} {φ ψ : Fm} (h₁ : IsJ Θ φ) (h₂ : IsJ Θ ψ) : IsJ Θ (.and φ ψ)
  | all {Θ : List String} {ψ : Fm} (L : List String)
      (h : ∀ s, s ∉ L → IsJ Θ (ψ.opn (.fvar s))) : IsJ Θ (.all ψ)
  | allJ {Θ : List String} {ψ : Fm} (L : List String)
      (h : ∀ s, s ∉ L → IsJ (s :: Θ) (ψ.opn (.fvar s))) : IsJ Θ (.allJ ψ)

/-- J-ness is monotone in the declarations. -/
theorem IsJ.mono {Θ Θ' : List String} {χ : Fm} (h : IsJ Θ χ) (H : ∀ t, t ∈ Θ → t ∈ Θ') :
    IsJ Θ' χ := by
  induction h generalizing Θ' with
  | var hs => exact .var (H _ hs)
  | top => exact .top
  | imp _ ih => exact .imp (ih H)
  | and _ _ ih₁ ih₂ => exact .and (ih₁ H) (ih₂ H)
  | all L _ ih => exact .all L fun s hs => ih s hs H
  | allJ L _ ih => exact .allJ L fun s hs => ih s hs (consMono H)

/-- `⊥` is not a J-formula (it is not a fixpoint: `◯⊥ → ⊥` fails in PLL). -/
theorem IsJ.not_bot (Θ : List String) : ¬ IsJ Θ .bot := fun h => nomatch h

/-- No disjunction is a J-formula (fixpoints are not closed under joins: C6). -/
theorem IsJ.not_or (Θ : List String) (φ ψ : Fm) : ¬ IsJ Θ (.or φ ψ) := fun h => nomatch h

/-- An undeclared variable is not a J-formula. -/
theorem IsJ.not_fvar {Θ : List String} {s : String} (hs : s ∉ Θ) : ¬ IsJ Θ (.fvar s) := by
  intro h
  cases h with
  | var h' => exact hs h'

/-- The class of admissible instances is monotone in the declarations. -/
def JMono (J : List String → Fm → Prop) : Prop :=
  ∀ Θ Θ' χ, J Θ χ → (∀ t, t ∈ Θ → t ∈ Θ') → J Θ' χ

/-- The class of admissible instances contains the declared variables. -/
def JVars (J : List String → Fm → Prop) : Prop := ∀ Θ s, s ∈ Θ → J Θ (.fvar s)

theorem IsJ.jmono : JMono IsJ := fun _ _ _ h H => h.mono H
theorem IsJ.jvars : JVars IsJ := fun _ _ h => .var h

/-- The guarded calculus: IPC2 with a second binder `∀°` whose instances are
restricted to `J Θ`.  `∀°I` declares its eigenvariable (`s :: Θ`); the
elimination rules are in the slime-free equation form with an `LC` side
condition.  No rule mentions `circ`. -/
inductive JND (J : List String → Fm → Prop) : List String → List Fm → Fm → Type
  | iden {Θ : List String} {Γ : List Fm} {φ : Fm} (h : φ ∈ Γ) : JND J Θ Γ φ
  | falsoElim {Θ : List String} {Γ : List Fm} (φ : Fm) (p : JND J Θ Γ .bot) : JND J Θ Γ φ
  | impIntro {Θ : List String} {Γ : List Fm} {φ ψ : Fm} (p : JND J Θ (φ :: Γ) ψ) :
      JND J Θ Γ (.imp φ ψ)
  | impElim {Θ : List String} {Γ : List Fm} {φ ψ : Fm} (p₁ : JND J Θ Γ (.imp φ ψ))
      (p₂ : JND J Θ Γ φ) : JND J Θ Γ ψ
  | andIntro {Θ : List String} {Γ : List Fm} {φ ψ : Fm} (p₁ : JND J Θ Γ φ) (p₂ : JND J Θ Γ ψ) :
      JND J Θ Γ (.and φ ψ)
  | andElim1 {Θ : List String} {Γ : List Fm} {φ ψ : Fm} (p : JND J Θ Γ (.and φ ψ)) : JND J Θ Γ φ
  | andElim2 {Θ : List String} {Γ : List Fm} {φ ψ : Fm} (p : JND J Θ Γ (.and φ ψ)) : JND J Θ Γ ψ
  | orIntro1 {Θ : List String} {Γ : List Fm} {φ ψ : Fm} (p : JND J Θ Γ φ) : JND J Θ Γ (.or φ ψ)
  | orIntro2 {Θ : List String} {Γ : List Fm} {φ ψ : Fm} (p : JND J Θ Γ ψ) : JND J Θ Γ (.or φ ψ)
  | orElim {Θ : List String} {Γ : List Fm} {φ ψ χ : Fm} (p₀ : JND J Θ Γ (.or φ ψ))
      (p₁ : JND J Θ (φ :: Γ) χ) (p₂ : JND J Θ (ψ :: Γ) χ) : JND J Θ Γ χ
  /-- `∀I`, cofinite. -/
  | allIntro {Θ : List String} {Γ : List Fm} {ψ : Fm} (L : List String)
      (p : ∀ s, s ∉ L → JND J Θ Γ (ψ.opn (.fvar s))) : JND J Θ Γ (.all ψ)
  /-- `∀E`, full comprehension. -/
  | allElim {Θ : List String} {Γ : List Fm} {ψ χ θ : Fm} (hχ : LC χ) (p : JND J Θ Γ (.all ψ))
      (e : θ = ψ.opn χ) : JND J Θ Γ θ
  /-- `∀°I`: the eigenvariable is declared a J-variable in the premise. -/
  | allJIntro {Θ : List String} {Γ : List Fm} {ψ : Fm} (L : List String)
      (p : ∀ s, s ∉ L → JND J (s :: Θ) Γ (ψ.opn (.fvar s))) : JND J Θ Γ (.allJ ψ)
  /-- `∀°E`: only a J-formula instantiates. -/
  | allJElim {Θ : List String} {Γ : List Fm} {ψ χ θ : Fm} (hχ : LC χ) (hJ : J Θ χ)
      (p : JND J Θ Γ (.allJ ψ)) (e : θ = ψ.opn χ) : JND J Θ Γ θ

variable {J : List String → Fm → Prop}

/-- A context inclusion transports derivations (weakening, exchange, contraction). -/
def JND.rename {Θ : List String} {Γ Γ' : List Fm} {φ : Fm} (H : ∀ ψ, ψ ∈ Γ → ψ ∈ Γ') :
    JND J Θ Γ φ → JND J Θ Γ' φ
  | .iden h => .iden (H _ h)
  | .falsoElim φ p => .falsoElim φ (p.rename H)
  | .impIntro p => .impIntro (p.rename (consMono H))
  | .impElim p₁ p₂ => .impElim (p₁.rename H) (p₂.rename H)
  | .andIntro p₁ p₂ => .andIntro (p₁.rename H) (p₂.rename H)
  | .andElim1 p => .andElim1 (p.rename H)
  | .andElim2 p => .andElim2 (p.rename H)
  | .orIntro1 p => .orIntro1 (p.rename H)
  | .orIntro2 p => .orIntro2 (p.rename H)
  | .orElim p₀ p₁ p₂ =>
      .orElim (p₀.rename H) (p₁.rename (consMono H)) (p₂.rename (consMono H))
  | .allIntro L p => .allIntro L fun s hs => (p s hs).rename H
  | .allElim hχ p e => .allElim hχ (p.rename H) e
  | .allJIntro L p => .allJIntro L fun s hs => (p s hs).rename H
  | .allJElim hχ hJ p e => .allJElim hχ hJ (p.rename H) e

def JND.weaken {Θ : List String} {Γ : List Fm} {φ : Fm} (ψ : Fm) :
    JND J Θ Γ φ → JND J Θ (ψ :: Γ) φ :=
  .rename fun _ h => List.mem_cons_of_mem _ h

/-- Declarations may be added (for a monotone class of instances). -/
def JND.weakenΘ (hJ : JMono J) {Θ Θ' : List String} {Γ : List Fm} {φ : Fm}
    (H : ∀ t, t ∈ Θ → t ∈ Θ') : JND J Θ Γ φ → JND J Θ' Γ φ
  | .iden h => .iden h
  | .falsoElim φ p => .falsoElim φ (p.weakenΘ hJ H)
  | .impIntro p => .impIntro (p.weakenΘ hJ H)
  | .impElim p₁ p₂ => .impElim (p₁.weakenΘ hJ H) (p₂.weakenΘ hJ H)
  | .andIntro p₁ p₂ => .andIntro (p₁.weakenΘ hJ H) (p₂.weakenΘ hJ H)
  | .andElim1 p => .andElim1 (p.weakenΘ hJ H)
  | .andElim2 p => .andElim2 (p.weakenΘ hJ H)
  | .orIntro1 p => .orIntro1 (p.weakenΘ hJ H)
  | .orIntro2 p => .orIntro2 (p.weakenΘ hJ H)
  | .orElim p₀ p₁ p₂ => .orElim (p₀.weakenΘ hJ H) (p₁.weakenΘ hJ H) (p₂.weakenΘ hJ H)
  | .allIntro L p => .allIntro L fun s hs => (p s hs).weakenΘ hJ H
  | .allElim hχ p e => .allElim hχ (p.weakenΘ hJ H) e
  | .allJIntro L p => .allJIntro L fun s hs => (p s hs).weakenΘ hJ (consMono H)
  | .allJElim hχ hj p e => .allJElim hχ (hJ _ _ _ hj H) (p.weakenΘ hJ H) e

/-! ## C3: the guard cannot be dropped

    J Θ χ  ⟹  ◯°χ ⊢ χ

by instantiating `∀°q.((χ → q) → q)` at `q := χ`. -/

/-- C3: an admitted instance is a fixpoint of the defined modality. -/
def JND.circJ_collapse {Θ : List String} {Γ : List Fm} {χ : Fm} (hJ : J Θ χ) (hχ : LC χ) :
    JND J Θ (circJ χ :: Γ) χ :=
  .impElim
    (.allJElim (χ := χ) (θ := .imp (.imp χ χ) χ) hχ hJ (.iden (List.mem_cons_self ..))
      (rpBody_opn hχ χ).symm)
    (.impIntro (.iden (List.mem_cons_self ..)))

/-- C3 at `⊥`: if `⊥` were a J-formula, `◯°⊥ ⊢ ⊥`. -/
def JND.circJ_bot_collapse {Θ : List String} {Γ : List Fm} (hJ : J Θ .bot) :
    JND J Θ (circJ .bot :: Γ) .bot :=
  JND.circJ_collapse hJ trivial

/-- F2, the ◯-free instance: with every formula admitted, `◯°` is the identity. -/
def JND.circJ_collapse_unguarded {Θ : List String} {Γ : List Fm} {χ : Fm} (hχ : LC χ) :
    JND (fun _ _ => True) Θ (circJ χ :: Γ) χ :=
  JND.circJ_collapse trivial hχ

/-! ## C1 and C2: the defined modality satisfies the PLL rules

    Γ ⊢ φ                     Γ ⊢ ◯°φ     Γ, φ ⊢ ◯°ψ
    ──────── (unit)           ─────────────────────── (bind)
    Γ ⊢ ◯°φ                   Γ ⊢ ◯°ψ

Unit: fix a fresh J-variable `s`, assume `φ → s`, conclude `s`.  Bind: fix a
fresh J-variable `s`, assume `ψ → s`; instantiate `◯°φ` at `s` to `(φ → s) → s`;
under `φ`, instantiate `◯°ψ` at `s` and apply it to `ψ → s`.  The only
instances are J-variables. -/

/-- C1, unit. -/
def JND.circJ_intro (hJ : JMono J) {Θ : List String} {Γ : List Fm} {φ : Fm} (hφ : LC φ)
    (p : JND J Θ Γ φ) : JND J Θ Γ (circJ φ) :=
  .allJIntro [] fun s _ => by
    rw [rpBody_opn hφ]
    exact .impIntro (.impElim (.iden (List.mem_cons_self ..))
      ((p.weakenΘ hJ fun t ht => List.mem_cons_of_mem _ ht).weaken _))

/-- C2, bind. -/
def JND.circJ_bind (hJ : JMono J) (hv : JVars J) {Θ : List String} {Γ : List Fm} {φ ψ : Fm}
    (hφ : LC φ) (hψ : LC ψ) (p₁ : JND J Θ Γ (circJ φ)) (p₂ : JND J Θ (φ :: Γ) (circJ ψ)) :
    JND J Θ Γ (circJ ψ) :=
  .allJIntro [] fun s _ => by
    rw [rpBody_opn hψ]
    refine .impIntro ?_
    refine .impElim
      (.allJElim (χ := .fvar s) (θ := .imp (.imp φ (.fvar s)) (.fvar s)) trivial
        (hv _ _ (List.mem_cons_self ..))
        ((p₁.weakenΘ hJ fun t ht => List.mem_cons_of_mem _ ht).weaken _)
        (rpBody_opn hφ _).symm) ?_
    refine .impIntro ?_
    refine .impElim
      (.allJElim (χ := .fvar s) (θ := .imp (.imp ψ (.fvar s)) (.fvar s)) trivial
        (hv _ _ (List.mem_cons_self ..))
        ((p₂.weakenΘ hJ fun t ht => List.mem_cons_of_mem _ ht).rename ?_)
        (rpBody_opn hψ _).symm)
      (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    intro χ h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-! The four Hilbert laws of PLL for `◯°` (`LaxLogic/PLL/Syntax/Axiom.lean`:
`somehowR`, `somehowM`, `somehowS`, `somehowBind`), from unit and bind exactly
as `PLLND.OI`, `OM`, `OSR` in `LaxLogic/PLL/ND/NDCore.lean`. -/

/-- ◯R: `⊢ φ → ◯°φ`. -/
def JND.OI (hJ : JMono J) {Θ : List String} (Γ : List Fm) {φ : Fm} (hφ : LC φ) :
    JND J Θ Γ (.imp φ (circJ φ)) :=
  .impIntro (JND.circJ_intro hJ hφ (.iden (List.mem_cons_self ..)))

/-- ◯M: `⊢ ◯°◯°φ → ◯°φ`. -/
def JND.OM (hJ : JMono J) (hv : JVars J) {Θ : List String} (Γ : List Fm) {φ : Fm} (hφ : LC φ) :
    JND J Θ Γ (.imp (circJ (circJ φ)) (circJ φ)) :=
  .impIntro (JND.circJ_bind hJ hv (lc_circJ hφ) hφ (.iden (List.mem_cons_self ..))
    (.iden (List.mem_cons_self ..)))

/-- ◯S: `⊢ ◯°φ ∧ ◯°ψ → ◯°(φ ∧ ψ)`. -/
def JND.OS (hJ : JMono J) (hv : JVars J) {Θ : List String} (Γ : List Fm) {φ ψ : Fm}
    (hφ : LC φ) (hψ : LC ψ) :
    JND J Θ Γ (.imp (.and (circJ φ) (circJ ψ)) (circJ (.and φ ψ))) :=
  .impIntro <|
    JND.circJ_bind hJ hv hφ ⟨hφ, hψ⟩ (.andElim1 (.iden (List.mem_cons_self ..))) <|
      JND.circJ_bind hJ hv hψ ⟨hφ, hψ⟩
        (.andElim2 (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) <|
        JND.circJ_intro hJ ⟨hφ, hψ⟩ (.andIntro
          (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          (.iden (List.mem_cons_self ..)))

/-- ◯bind: `⊢ (φ → ◯°ψ) → (◯°φ → ◯°ψ)`. -/
def JND.Obind (hJ : JMono J) (hv : JVars J) {Θ : List String} (Γ : List Fm) {φ ψ : Fm}
    (hφ : LC φ) (hψ : LC ψ) :
    JND J Θ Γ (.imp (.imp φ (circJ ψ)) (.imp (circJ φ) (circJ ψ))) :=
  .impIntro (.impIntro (JND.circJ_bind hJ hv hφ hψ (.iden (List.mem_cons_self ..))
    (.impElim (.iden (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (.iden (List.mem_cons_self ..)))))

end P2LL

/-! ## Pins (upper bounds; first run at `[]`, see `wip/p2ll-STATUS.md`) -/

#axioms_within P2LL.IsJ.mono [propext]
#axioms_within P2LL.IsJ.not_bot []
#axioms_within P2LL.IsJ.not_or []
#axioms_within P2LL.JND.rename [propext]
#axioms_within P2LL.JND.weakenΘ [propext]
#axioms_within P2LL.JND.circJ_collapse [propext]
#axioms_within P2LL.JND.circJ_collapse_unguarded [propext]
#axioms_within P2LL.JND.circJ_intro [propext]
#axioms_within P2LL.JND.circJ_bind [propext]
#axioms_within P2LL.JND.OI [propext]
#axioms_within P2LL.JND.OM [propext]
#axioms_within P2LL.JND.OS [propext]
#axioms_within P2LL.JND.Obind [propext]
