import wip.p2llSyntax

/-!
# P2LL: natural deduction, its ◯-free fragment, and the P2LL-side cells

File 2 of the P2LL definability campaign (`wip/p2ll-STATUS.md`).

* `LaxND2`: natural deduction for P2LL (plan §1.2): `PLLND.LaxND` (membership
  `iden`, no structural rules, `orElim` with its major premise) plus the
  cofinite `∀I` and the `∀E` with an `LC` side condition, in the slime-free
  equation form of `LaxLogic/QLL`'s `Prv.allE`.
* `IPC2ND`: the same without the lax rules (data, as `LaxND2`): the ◯-free fragment,
  IPC2 (CLAUDE.md rule 8: the ◯-free instance first).
* `IPC2NoLC`: the `∀`-fragment WITHOUT the `LC` side condition on `∀E`, a design
  variant: it is inconsistent (cell C5).

**Well-formedness (2026-10-24, second revision of the rules).**  Every rule
whose conclusion is not locally closed by virtue of its premises carries the
missing local closure as a side condition: `iden` (`LC φ`), `falsoElim`
(`LC φ`), `impIntro` (`LC φ`, the discharged hypothesis), `orIntro1`/`orIntro2`
(the other disjunct), `allIntro` (`lcAt 1 ψ`, the body), and `allElim`/`allJElim`
(`LC χ`, the instance, as before).  Hence every derivable formula is locally
closed (`LaxND2.lc`), with no fresh name chosen anywhere (the condition on
`∀I` is redundant given one fresh name, `lcAt_of_openRec`, but a fresh-name
supply over `String` is classical in core).  Without these conditions the
first revision derived ill-formed sequents such as `[bvar 0] ⊢ ◯(bvar 0)`,
whose translation into the guarded calculus, `[bvar 0] ⊢ ∀°q.((bvar 1 → q) → q)`
(the body shifts), is not derivable; so the interpretation theorem I₁ of
`wip/p2llStatements.lean` was FALSE for that revision.

Cells (statements first, `METHOD.md` §1–2; nothing here is a full theorem of
the campaign):

* F1 (fragment first, in IPC2): Aczel's `RP(φ) := ∀q.((φ → q) → q)` is the
  IDENTITY: `φ ⊢ RP(φ)` and `RP(φ) ⊢ φ`.  So the ◯-free instance of the defined
  modality is the identity nucleus, and the plan's Propositions A and B
  (`RP(φ) ⊢ ◯φ`, `◯φ ⊬ RP(φ)`) are the unit law and `◯φ ⊬ φ`.
* C7 (P2LL, Proposition C of plan §1.6, both directions):
  `◯φ ⊢ ∀°p.((φ → p) → p)` and `∀°p.((φ → p) → p) ⊢ ◯φ`.
* C5: `IPC2NoLC [] ⊥`.  Two instantiations at the dangling index `bvar 0`,
  each captured by an inner binder, derive `⊥`, although every hypothesis,
  leaf and quantified body of that derivation is locally closed; the `LC`
  side condition on `∀E` is part of the statement, not a convenience.
-/

namespace P2LL

open Fm

/-- Natural deduction for P2LL: `PLLND.LaxND` with the two quantifier rules and
the well-formedness side conditions.  Contexts are lists extended by `::`;
`iden` is membership-based (weakening, exchange and contraction are admissible,
`LaxND2.rename`). -/
inductive LaxND2 : List Fm → Fm → Type
  | iden {Γ : List Fm} {φ : Fm} (hφ : LC φ) (h : φ ∈ Γ) : LaxND2 Γ φ
  | falsoElim {Γ : List Fm} (φ : Fm) (hφ : LC φ) (p : LaxND2 Γ .bot) : LaxND2 Γ φ
  | impIntro {Γ : List Fm} {φ ψ : Fm} (hφ : LC φ) (p : LaxND2 (φ :: Γ) ψ) : LaxND2 Γ (.imp φ ψ)
  | impElim {Γ : List Fm} {φ ψ : Fm} (p₁ : LaxND2 Γ (.imp φ ψ)) (p₂ : LaxND2 Γ φ) : LaxND2 Γ ψ
  | andIntro {Γ : List Fm} {φ ψ : Fm} (p₁ : LaxND2 Γ φ) (p₂ : LaxND2 Γ ψ) : LaxND2 Γ (.and φ ψ)
  | andElim1 {Γ : List Fm} {φ ψ : Fm} (p : LaxND2 Γ (.and φ ψ)) : LaxND2 Γ φ
  | andElim2 {Γ : List Fm} {φ ψ : Fm} (p : LaxND2 Γ (.and φ ψ)) : LaxND2 Γ ψ
  | orIntro1 {Γ : List Fm} {φ ψ : Fm} (hψ : LC ψ) (p : LaxND2 Γ φ) : LaxND2 Γ (.or φ ψ)
  | orIntro2 {Γ : List Fm} {φ ψ : Fm} (hφ : LC φ) (p : LaxND2 Γ ψ) : LaxND2 Γ (.or φ ψ)
  | orElim {Γ : List Fm} {φ ψ χ : Fm} (p₀ : LaxND2 Γ (.or φ ψ))
      (p₁ : LaxND2 (φ :: Γ) χ) (p₂ : LaxND2 (ψ :: Γ) χ) : LaxND2 Γ χ
  | laxIntro {Γ : List Fm} {φ : Fm} (p : LaxND2 Γ φ) : LaxND2 Γ (.circ φ)
  | laxElim {Γ : List Fm} {φ ψ : Fm} (p₁ : LaxND2 Γ (.circ φ))
      (p₂ : LaxND2 (φ :: Γ) (.circ ψ)) : LaxND2 Γ (.circ ψ)
  /-- `∀I`, cofinite: the (well-formed) body holds at every name outside `L`. -/
  | allIntro {Γ : List Fm} {ψ : Fm} (L : List String) (hψ : lcAt 1 ψ)
      (p : ∀ s, s ∉ L → LaxND2 Γ (ψ.opn (.fvar s))) : LaxND2 Γ (.all ψ)
  /-- `∀E`, full comprehension: any locally closed `χ` instantiates. -/
  | allElim {Γ : List Fm} {ψ χ θ : Fm} (hχ : LC χ) (p : LaxND2 Γ (.all ψ))
      (e : θ = ψ.opn χ) : LaxND2 Γ θ

/-- A context inclusion extends under `::`. -/
def consMono {α : Type} {Γ Γ' : List α} {χ : α} (H : ∀ ψ, ψ ∈ Γ → ψ ∈ Γ') :
    ∀ ψ, ψ ∈ χ :: Γ → ψ ∈ χ :: Γ' := by
  intro ψ h
  rcases List.mem_cons.mp h with rfl | h
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (H _ h)

/-- A context inclusion transports derivations (weakening, exchange, contraction). -/
def LaxND2.rename {Γ Γ' : List Fm} {φ : Fm} (H : ∀ ψ, ψ ∈ Γ → ψ ∈ Γ') :
    LaxND2 Γ φ → LaxND2 Γ' φ
  | .iden hφ h => .iden hφ (H _ h)
  | .falsoElim φ hφ p => .falsoElim φ hφ (p.rename H)
  | .impIntro hφ p => .impIntro hφ (p.rename (consMono H))
  | .impElim p₁ p₂ => .impElim (p₁.rename H) (p₂.rename H)
  | .andIntro p₁ p₂ => .andIntro (p₁.rename H) (p₂.rename H)
  | .andElim1 p => .andElim1 (p.rename H)
  | .andElim2 p => .andElim2 (p.rename H)
  | .orIntro1 hψ p => .orIntro1 hψ (p.rename H)
  | .orIntro2 hφ p => .orIntro2 hφ (p.rename H)
  | .orElim p₀ p₁ p₂ =>
      .orElim (p₀.rename H) (p₁.rename (consMono H)) (p₂.rename (consMono H))
  | .laxIntro p => .laxIntro (p.rename H)
  | .laxElim p₁ p₂ => .laxElim (p₁.rename H) (p₂.rename (consMono H))
  | .allIntro L hψ p => .allIntro L hψ fun s hs => (p s hs).rename H
  | .allElim hχ p e => .allElim hχ (p.rename H) e

def LaxND2.weaken {Γ : List Fm} {φ : Fm} (ψ : Fm) : LaxND2 Γ φ → LaxND2 (ψ :: Γ) φ :=
  .rename fun _ h => List.mem_cons_of_mem _ h

/-- **Every derivable formula is locally closed.** -/
theorem LaxND2.lc {Γ : List Fm} {φ : Fm} : LaxND2 Γ φ → LC φ
  | .iden hφ _ => hφ
  | .falsoElim _ hφ _ => hφ
  | .impIntro hφ p => ⟨hφ, p.lc⟩
  | .impElim p₁ _ => p₁.lc.2
  | .andIntro p₁ p₂ => ⟨p₁.lc, p₂.lc⟩
  | .andElim1 p => p.lc.1
  | .andElim2 p => p.lc.2
  | .orIntro1 hψ p => ⟨p.lc, hψ⟩
  | .orIntro2 hφ p => ⟨hφ, p.lc⟩
  | .orElim _ p₁ _ => p₁.lc
  | .laxIntro p => p.lc
  | .laxElim _ p₂ => p₂.lc
  | .allIntro _ hψ _ => hψ
  | .allElim hχ p e => e ▸ lc_opn _ hχ p.lc

/-! ## The ◯-free fragment: IPC2 -/

/-- Natural deduction for IPC2 (no lax rules), as data like `LaxND2`:
the ◯-free fragment of `LaxND2`, and the target of the plan's erasure (M3). -/
inductive IPC2ND : List Fm → Fm → Type
  | iden {Γ : List Fm} {φ : Fm} (hφ : LC φ) (h : φ ∈ Γ) : IPC2ND Γ φ
  | falsoElim {Γ : List Fm} (φ : Fm) (hφ : LC φ) (p : IPC2ND Γ .bot) : IPC2ND Γ φ
  | impIntro {Γ : List Fm} {φ ψ : Fm} (hφ : LC φ) (p : IPC2ND (φ :: Γ) ψ) : IPC2ND Γ (.imp φ ψ)
  | impElim {Γ : List Fm} {φ ψ : Fm} (p₁ : IPC2ND Γ (.imp φ ψ)) (p₂ : IPC2ND Γ φ) : IPC2ND Γ ψ
  | andIntro {Γ : List Fm} {φ ψ : Fm} (p₁ : IPC2ND Γ φ) (p₂ : IPC2ND Γ ψ) : IPC2ND Γ (.and φ ψ)
  | andElim1 {Γ : List Fm} {φ ψ : Fm} (p : IPC2ND Γ (.and φ ψ)) : IPC2ND Γ φ
  | andElim2 {Γ : List Fm} {φ ψ : Fm} (p : IPC2ND Γ (.and φ ψ)) : IPC2ND Γ ψ
  | orIntro1 {Γ : List Fm} {φ ψ : Fm} (hψ : LC ψ) (p : IPC2ND Γ φ) : IPC2ND Γ (.or φ ψ)
  | orIntro2 {Γ : List Fm} {φ ψ : Fm} (hφ : LC φ) (p : IPC2ND Γ ψ) : IPC2ND Γ (.or φ ψ)
  | orElim {Γ : List Fm} {φ ψ χ : Fm} (p₀ : IPC2ND Γ (.or φ ψ))
      (p₁ : IPC2ND (φ :: Γ) χ) (p₂ : IPC2ND (ψ :: Γ) χ) : IPC2ND Γ χ
  | allIntro {Γ : List Fm} {ψ : Fm} (L : List String) (hψ : lcAt 1 ψ)
      (p : ∀ s, s ∉ L → IPC2ND Γ (ψ.opn (.fvar s))) : IPC2ND Γ (.all ψ)
  | allElim {Γ : List Fm} {ψ χ θ : Fm} (hχ : LC χ) (p : IPC2ND Γ (.all ψ))
      (e : θ = ψ.opn χ) : IPC2ND Γ θ

/-! ## F1: in IPC2, Aczel's `RP` is the identity (the ◯-free instance, rule 8)

    φ ⊢ ∀q.((φ → q) → q)          ∀q.((φ → q) → q) ⊢ φ

The second derivation instantiates `q := φ` (full comprehension), which is what
the restriction to J-formulas forbids in the guarded calculus. -/

/-- F1, `φ ⊢ RP(φ)`. -/
def IPC2ND.rp_intro {Γ : List Fm} {φ : Fm} (hφ : LC φ) : IPC2ND (φ :: Γ) (rp φ) := by
  refine .allIntro [] (lc_rpBody hφ) fun s _ => ?_
  rw [rpBody_opn hφ]
  exact .impIntro ⟨hφ, trivial⟩ (.impElim (.iden ⟨hφ, trivial⟩ (List.mem_cons_self ..))
    (.iden hφ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- F1, `RP(φ) ⊢ φ`, by instantiating at `φ` itself. -/
def IPC2ND.rp_elim {Γ : List Fm} {φ : Fm} (hφ : LC φ) : IPC2ND (rp φ :: Γ) φ :=
  .impElim
    (.allElim (χ := φ) (θ := .imp (.imp φ φ) φ) hφ (.iden (lc_rp hφ) (List.mem_cons_self ..))
      (rpBody_opn hφ φ).symm)
    (.impIntro hφ (.iden hφ (List.mem_cons_self ..)))

/-! ## C7: Proposition C in P2LL

    ◯φ ⊢ ∀p.((◯p → p) → ((φ → p) → p))        ∀p.((◯p → p) → ((φ → p) → p)) ⊢ ◯φ

The first uses `laxElim` (bind) at a declared fixpoint `p`; the second
instantiates `p := ◯φ`, whose guard `◯◯φ → ◯φ` is ◯M and whose premise
`φ → ◯φ` is ◯R (plan §1.6). -/

/-- ◯R in P2LL: `⊢ φ → ◯φ`. -/
def LaxND2.OI (Γ : List Fm) {φ : Fm} (hφ : LC φ) : LaxND2 Γ (.imp φ (.circ φ)) :=
  .impIntro hφ (.laxIntro (.iden hφ (List.mem_cons_self ..)))

/-- ◯M in P2LL: `⊢ ◯◯φ → ◯φ`. -/
def LaxND2.OM (Γ : List Fm) {φ : Fm} (hφ : LC φ) : LaxND2 Γ (.imp (.circ (.circ φ)) (.circ φ)) :=
  .impIntro hφ (.laxElim (φ := .circ φ) (.iden hφ (List.mem_cons_self ..)) (.iden hφ (List.mem_cons_self ..)))

/-- C7 (⊢): `◯φ ⊢ ∀°p.((φ → p) → p)`. -/
def LaxND2.circ_to_circNuc {Γ : List Fm} {φ : Fm} (hφ : LC φ) :
    LaxND2 (.circ φ :: Γ) (circNuc φ) :=
  .allIntro [] (lc_circNuc hφ) fun s _ => by
    have e : (Fm.imp (.imp (.circ (.bvar 0)) (.bvar 0)) (rpBody φ)).opn (.fvar s) =
        .imp (.imp (.circ (.fvar s)) (.fvar s)) (.imp (.imp φ (.fvar s)) (.fvar s)) := by
      simp [opn, openRec, rpBody, shiftAt_lcAt 0 φ hφ, openRec_lcAt _ 0 φ hφ]
    rw [e]
    refine .impIntro ⟨trivial, trivial⟩ (.impIntro ⟨hφ, trivial⟩ ?_)
    -- φ → s, ◯s → s, ◯φ, Γ ⊢ s
    refine .impElim (φ := .circ (.fvar s)) (.iden ⟨trivial, trivial⟩ (by simp)) ?_
    -- φ → s, ◯s → s, ◯φ, Γ ⊢ ◯s, by bind on ◯φ
    exact .laxElim (φ := φ) (.iden hφ (by simp))
      (.laxIntro (.impElim (φ := φ) (.iden ⟨hφ, trivial⟩ (by simp)) (.iden hφ (by simp))))

/-- C7 (⊣): `∀°p.((φ → p) → p) ⊢ ◯φ`, instantiating `p := ◯φ`. -/
def LaxND2.circNuc_to_circ {Γ : List Fm} {φ : Fm} (hφ : LC φ) :
    LaxND2 (circNuc φ :: Γ) (.circ φ) :=
  .impElim
    (.impElim
      (.allElim (χ := .circ φ)
        (θ := .imp (.imp (.circ (.circ φ)) (.circ φ)) (.imp (.imp φ (.circ φ)) (.circ φ)))
        hφ (.iden (lc_circNuc hφ) (List.mem_cons_self ..))
        (by simp [opn, openRec, rpBody, shiftAt_lcAt 0 φ hφ, openRec_lcAt _ 0 φ hφ]))
      (LaxND2.OM _ hφ))
    (LaxND2.OI _ hφ)

/-! ## C5: the `LC` side condition on `∀E` cannot be dropped

Without `LC χ` on `∀E`, an instance at the dangling index `bvar 0` is captured
by the binders it lands under, even though every hypothesis, leaf and quantified
body is locally closed:

    A := ∀p.((∀q.(q → p)) → p)   provable;  A at bvar 0:  (∀q.(q → q)) → bvar 0,  so  ⊢ bvar 0
    B := ∀p.(p → ∀q.p)           provable;  B at bvar 0:  bvar 0 → ∀q.q,          so  ⊢ ∀q.q
    ∀q.q at ⊥:  ⊢ ⊥ -/

/-- The `∀`-fragment of IPC2 with the `LC` side condition on `∀E` removed (the
conditions on `iden`, `impIntro` and `allIntro` kept). -/
inductive IPC2NoLC : List Fm → Fm → Prop
  | iden {Γ : List Fm} {φ : Fm} (hφ : LC φ) (h : φ ∈ Γ) : IPC2NoLC Γ φ
  | impIntro {Γ : List Fm} {φ ψ : Fm} (hφ : LC φ) (p : IPC2NoLC (φ :: Γ) ψ) : IPC2NoLC Γ (.imp φ ψ)
  | impElim {Γ : List Fm} {φ ψ : Fm} (p₁ : IPC2NoLC Γ (.imp φ ψ)) (p₂ : IPC2NoLC Γ φ) :
      IPC2NoLC Γ ψ
  | allIntro {Γ : List Fm} {ψ : Fm} (L : List String) (hψ : lcAt 1 ψ)
      (p : ∀ s, s ∉ L → IPC2NoLC Γ (ψ.opn (.fvar s))) : IPC2NoLC Γ (.all ψ)
  | allElim {Γ : List Fm} {ψ θ : Fm} (χ : Fm) (p : IPC2NoLC Γ (.all ψ))
      (e : θ = ψ.opn χ) : IPC2NoLC Γ θ

/-- C5: the variant without `LC` on `∀E` derives `⊥`. -/
theorem IPC2NoLC.inconsistent : IPC2NoLC [] .bot := by
  -- A := ∀p.((∀q.(q → p)) → p), provable: instantiate q := ⊤
  have hA : IPC2NoLC [] (.all (.imp (.all (.imp (.bvar 0) (.bvar 1))) (.bvar 0))) := by
    refine .allIntro [] (by decide) fun s _ => ?_
    have e : (Fm.imp (.all (.imp (.bvar 0) (.bvar 1))) (.bvar 0)).opn (.fvar s) =
        .imp (.all (.imp (.bvar 0) (.fvar s))) (.fvar s) := by simp [opn, openRec]
    rw [e]
    refine .impIntro (by exact ⟨Nat.zero_lt_one, trivial⟩) ?_
    refine .impElim (.allElim (θ := .imp Fm.top (.fvar s)) Fm.top
      (.iden (by exact ⟨Nat.zero_lt_one, trivial⟩) (List.mem_cons_self ..)) (by simp [opn, openRec])) ?_
    exact .impIntro trivial (.iden trivial (List.mem_cons_self ..))
  -- A at the dangling bvar 0: (∀q.(q → q)) → bvar 0
  have h1 : IPC2NoLC [] (.imp (.all (.imp (.bvar 0) (.bvar 0))) (.bvar 0)) :=
    .allElim (.bvar 0) hA (by simp [opn, openRec])
  have h2 : IPC2NoLC [] (.all (.imp (.bvar 0) (.bvar 0))) := by
    refine .allIntro [] (by decide) fun s _ => ?_
    have e : (Fm.imp (.bvar 0) (.bvar 0)).opn (.fvar s) = .imp (.fvar s) (.fvar s) := by
      simp [opn, openRec]
    rw [e]
    exact .impIntro trivial (.iden trivial (List.mem_cons_self ..))
  have h3 : IPC2NoLC [] (.bvar 0) := .impElim h1 h2
  -- B := ∀p.(p → ∀q.p)
  have hB : IPC2NoLC [] (.all (.imp (.bvar 0) (.all (.bvar 1)))) := by
    refine .allIntro [] (by decide) fun s _ => ?_
    have e : (Fm.imp (.bvar 0) (.all (.bvar 1))).opn (.fvar s) =
        .imp (.fvar s) (.all (.fvar s)) := by simp [opn, openRec]
    rw [e]
    refine .impIntro trivial (.allIntro [] trivial fun t _ => ?_)
    have e' : (Fm.fvar s).opn (.fvar t) = .fvar s := rfl
    rw [e']
    exact .iden trivial (List.mem_cons_self ..)
  -- B at the dangling bvar 0: bvar 0 → ∀q.q
  have h4 : IPC2NoLC [] (.imp (.bvar 0) (.all (.bvar 0))) :=
    .allElim (.bvar 0) hB (by simp [opn, openRec])
  have h5 : IPC2NoLC [] (.all (.bvar 0)) := .impElim h4 h3
  exact .allElim .bot h5 (by simp [opn, openRec])

end P2LL

/-! ## Pins (upper bounds).  Each was first run at `[]` and failed with
`propext` (2026-10-24; with `Finset String` for the excluded names the profile
was `propext, Quot.sound`, from `Finset` membership), see `wip/p2ll-STATUS.md`. -/

#axioms_within P2LL.LaxND2.rename [propext]
#axioms_within P2LL.LaxND2.lc [propext]
#axioms_within P2LL.IPC2ND.rp_intro [propext]
#axioms_within P2LL.IPC2ND.rp_elim [propext]
#axioms_within P2LL.LaxND2.circ_to_circNuc [propext]
#axioms_within P2LL.LaxND2.circNuc_to_circ [propext]
#axioms_within P2LL.IPC2NoLC.inconsistent [propext]
