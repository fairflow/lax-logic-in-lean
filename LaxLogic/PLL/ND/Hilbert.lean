import LaxLogic.PLL.ND.NDCore
import LaxLogic.PLL.Syntax.Proof

/-!
# The Hilbert system embeds in natural deduction (half of F&M Theorem 2.3)

This connects the two halves of the repository: the Hilbert-style proof
checker of `PLLProof.lean`/`PLLAxiom.lean` and the natural deduction system
`PLLND.LaxND` of `PLLNDCore.lean`.

* every Hilbert axiom is a theorem of `LaxND` (`axiomDeriv`);
* every formula appearing in a *valid* Hilbert proof is a theorem
  (`formulas_derivable`);
* hence any checked Hilbert proof of `φ` yields `Nonempty (LaxND [] φ)`
  (`hilbert_to_ND`).

The converse direction (ND → Hilbert, completing F&M Theorem 2.3) needs the
internal deduction theorem for the Hilbert system and is left as future work.

Note this required two fixes to the checker, both matching their own
documentation: the `orElim` axiom read `(A ∧ B) ⊃ C` where IPC requires
`(A ∨ B) ⊃ C`, and `isValid` did not check validity recursively under a
`modusPonens` step (so stacked MP steps could launder arbitrary formulas —
including a "valid" proof of `⊥`).
-/

open PLLFormula PLLProof

namespace PLLND

/-- Every axiom of the Hilbert system is derivable in `LaxND`, in any
context. -/
def axiomDeriv (Γ : List PLLFormula) : (ax : PLLAxiom) → LaxND Γ ax.get
  | .somehowR M => OI Γ M
  | .somehowM M => OM Γ M
  | .somehowS M N => OSR Γ M N
  | .somehowBind M N =>
      .impIntro <| .impIntro <|
        .laxElim (.iden (.head _))
          (.impElim (.iden (.tail _ (.tail _ (.head _)))) (.iden (.head _)))
  | .impK _ _ =>
      .impIntro (.impIntro (.iden (.tail _ (.head _))))
  | .impS _ _ _ =>
      .impIntro <| .impIntro <| .impIntro <|
        .impElim
          (.impElim (.iden (.tail _ (.tail _ (.head _)))) (.iden (.head _)))
          (.impElim (.iden (.tail _ (.head _))) (.iden (.head _)))
  | .andElim1 _ _ => .impIntro (.andElim1 (.iden (.head _)))
  | .andElim2 _ _ => .impIntro (.andElim2 (.iden (.head _)))
  | .andIntro _ _ =>
      .impIntro (.impIntro
        (.andIntro (.iden (.tail _ (.head _))) (.iden (.head _))))
  | .orIntro1 _ _ => .impIntro (.orIntro1 (.iden (.head _)))
  | .orIntro2 _ _ => .impIntro (.orIntro2 (.iden (.head _)))
  | .orElim _ _ _ =>
      .impIntro <| .impIntro <| .impIntro <|
        .orElim (.iden (.head _))
          (.impElim (.iden (.tail _ (.tail _ (.tail _ (.head _)))))
            (.iden (.head _)))
          (.impElim (.iden (.tail _ (.tail _ (.head _))))
            (.iden (.head _)))
  | .explosion _ => .impIntro (.falsoElim _ (.iden (.head _)))

/-- Every formula recorded in a valid Hilbert proof is an `LaxND` theorem. -/
theorem formulas_derivable : ∀ {p : PLLProof}, p.isValid →
    ∀ φ ∈ p.formulas, Nonempty (LaxND [] φ)
  | .emptyProof, _, φ, hφ => by simp at hφ
  | .axiomStep prev ax, hv, φ, hφ => by
      simp only [PLLProof.formulas, List.mem_append, List.mem_singleton] at hφ
      rcases hφ with h | rfl
      · exact formulas_derivable (p := prev) hv φ h
      · exact ⟨axiomDeriv [] ax⟩
  | .modusPonens prev c, hv, φ, hφ => by
      obtain ⟨hvprev, hant, hval⟩ := hv
      simp only [PLLProof.formulas, List.mem_append, List.mem_singleton] at hφ
      rcases hφ with h | rfl
      · exact formulas_derivable (p := prev) hvprev φ h
      · obtain ⟨F, hF⟩ := c
        obtain ⟨P, Q, rfl⟩ := hF
        obtain ⟨pv⟩ := formulas_derivable (p := prev) hvprev _ hval
        obtain ⟨pa⟩ := formulas_derivable (p := prev) hvprev _ hant
        exact ⟨.impElim pv pa⟩

/-- **Half of F&M Theorem 2.3**: a checked Hilbert proof of `φ` yields a
natural deduction proof of `φ`. -/
theorem hilbert_to_ND {p : PLLProof} {φ : PLLFormula}
    (h : p.isProofOf φ) : Nonempty (LaxND [] φ) := by
  cases p with
  | emptyProof => exact absurd h (by simp)
  | axiomStep prev ax =>
      obtain ⟨hconc, hv⟩ := h
      have hmem : φ ∈ (PLLProof.axiomStep prev ax).formulas := by
        rw [← hconc]
        exact List.getLast_mem _
      exact formulas_derivable hv φ hmem
  | modusPonens prev c =>
      obtain ⟨hconc, hv⟩ := h
      have hmem : φ ∈ (PLLProof.modusPonens prev c).formulas := by
        rw [← hconc]
        exact List.getLast_mem _
      exact formulas_derivable hv φ hmem

/-! ### Hilbert consequence, the deduction theorem, and F&M Theorem 2.3 -/

/-- Hilbert-style consequence over an axiom set `Ax`: derivable from the
hypotheses and `Ax`-instances by modus ponens alone. -/
inductive HdOn (Ax : PLLFormula → Prop) (Γ : List PLLFormula) : PLLFormula → Prop
  | ax {φ : PLLFormula} (h : Ax φ) : HdOn Ax Γ φ
  | hyp {φ : PLLFormula} (h : φ ∈ Γ) : HdOn Ax Γ φ
  | mp {φ ψ : PLLFormula} :
      HdOn Ax Γ (φ.ifThen ψ) → HdOn Ax Γ φ → HdOn Ax Γ ψ

/-- The full PLL axiom set (including the repaired `orElim` and the added
`somehowBind`). -/
def PLLAx (φ : PLLFormula) : Prop := ∃ a : PLLAxiom, φ = a.get

/-- Hilbert-style PLL consequence. -/
abbrev Hd (Γ : List PLLFormula) (φ : PLLFormula) : Prop := HdOn PLLAx Γ φ

namespace HdOn

/-- `⊢ φ ⊃ φ` from `K` and `S`. -/
theorem impSelf {Ax : PLLFormula → Prop}
    (hK : ∀ A B : PLLFormula, Ax (ifThen A (ifThen B A)))
    (hS : ∀ A B C : PLLFormula, Ax (ifThen (ifThen A (ifThen B C))
      (ifThen (ifThen A B) (ifThen A C))))
    {Γ : List PLLFormula} (φ : PLLFormula) :
    HdOn Ax Γ (φ.ifThen φ) :=
  .mp (.mp (.ax (hS φ (φ.ifThen φ) φ)) (.ax (hK φ (φ.ifThen φ))))
    (.ax (hK φ φ))

/-- **Deduction theorem** (F&M Proposition 2.2, Hilbert form): available
for any axiom set containing `K` and `S`, because PLL's rules are modus
ponens only.  F&M note this fails for K, T, S4. -/
theorem deduction {Ax : PLLFormula → Prop}
    (hK : ∀ A B : PLLFormula, Ax (ifThen A (ifThen B A)))
    (hS : ∀ A B C : PLLFormula, Ax (ifThen (ifThen A (ifThen B C))
      (ifThen (ifThen A B) (ifThen A C))))
    {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (h : HdOn Ax (φ :: Γ) ψ) : HdOn Ax Γ (φ.ifThen ψ) := by
  induction h with
  | ax h' => exact .mp (.ax (hK _ φ)) (.ax h')
  | hyp h' =>
      rcases List.mem_cons.mp h' with rfl | h'
      · exact impSelf hK hS _
      · exact .mp (.ax (hK _ φ)) (.hyp h')
  | mp _ _ ih₁ ih₂ => exact .mp (.mp (.ax (hS φ _ _)) ih₁) ih₂

end HdOn

/-- Natural deduction embeds in the Hilbert system (with the full axiom
set): one half of F&M Theorem 2.3. -/
theorem ND_to_Hd : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    LaxND Γ φ → Hd Γ φ := by
  have hK : ∀ A B : PLLFormula, PLLAx (ifThen A (ifThen B A)) :=
    fun A B => ⟨.impK A B, rfl⟩
  have hS : ∀ A B C : PLLFormula, PLLAx (ifThen (ifThen A (ifThen B C))
      (ifThen (ifThen A B) (ifThen A C))) :=
    fun A B C => ⟨.impS A B C, rfl⟩
  intro Γ φ p
  induction p with
  | iden h => exact .hyp h
  | falsoElim φ _ ih => exact .mp (.ax ⟨.explosion φ, rfl⟩) ih
  | impIntro _ ih => exact HdOn.deduction hK hS ih
  | impElim _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | andIntro _ _ ih₁ ih₂ =>
      exact .mp (.mp (.ax ⟨.andIntro _ _, rfl⟩) ih₁) ih₂
  | andElim1 _ ih => exact .mp (.ax ⟨.andElim1 _ _, rfl⟩) ih
  | andElim2 _ ih => exact .mp (.ax ⟨.andElim2 _ _, rfl⟩) ih
  | orIntro1 _ ih => exact .mp (.ax ⟨.orIntro1 _ _, rfl⟩) ih
  | orIntro2 _ ih => exact .mp (.ax ⟨.orIntro2 _ _, rfl⟩) ih
  | orElim _ _ _ ih₀ ih₁ ih₂ =>
      exact .mp (.mp (.mp (.ax ⟨.orElim _ _ _, rfl⟩)
        (HdOn.deduction hK hS ih₁)) (HdOn.deduction hK hS ih₂)) ih₀
  | laxIntro _ ih => exact .mp (.ax ⟨.somehowR _, rfl⟩) ih
  | laxElim _ _ ih₁ ih₂ =>
      exact .mp (.mp (.ax ⟨.somehowBind _ _, rfl⟩)
        (HdOn.deduction hK hS ih₂)) ih₁

/-- The Hilbert system embeds in natural deduction. -/
theorem Hd_to_ND : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    Hd Γ φ → Nonempty (LaxND Γ φ) := by
  intro Γ φ h
  induction h with
  | ax h' => obtain ⟨a, rfl⟩ := h'; exact ⟨axiomDeriv Γ a⟩
  | hyp h' => exact ⟨.iden h'⟩
  | mp _ _ ih₁ ih₂ =>
      obtain ⟨p₁⟩ := ih₁
      obtain ⟨p₂⟩ := ih₂
      exact ⟨.impElim p₁ p₂⟩

/-- **F&M Theorem 2.3** (Hilbert side): Hilbert-style and natural deduction
consequence coincide. -/
theorem hd_iff_ND {Γ : List PLLFormula} {φ : PLLFormula} :
    Hd Γ φ ↔ Nonempty (LaxND Γ φ) :=
  ⟨Hd_to_ND, fun ⟨p⟩ => ND_to_Hd p⟩

/-! ### F&M Lemma 2.1: PLL is a purely axiomatic extension of IPC

The single additional scheme is the *Kleisli adjunction*
`(N ⊃ ◯K) ≡ (◯N ⊃ ◯K)`.  (The forward implication alone — bind — does not
suffice: interpreting `◯` as the constant-`⊥` operator validates every bind
instance but refutes `◯R`.) -/

/-- The IPC axioms. -/
def IPCAx (φ : PLLFormula) : Prop :=
  ∃ a : PLLAxiom, φ = a.get ∧ match a with
    | .somehowR _ | .somehowM _ | .somehowS _ _ | .somehowBind _ _ => False
    | _ => True

/-- IPC plus the Kleisli adjunction scheme. -/
def IPCBindAx (φ : PLLFormula) : Prop :=
  IPCAx φ ∨ ∃ M N : PLLFormula,
    φ = ((M.ifThen (somehow N)).ifThen ((somehow M).ifThen (somehow N))) ∨
    φ = (((somehow M).ifThen (somehow N)).ifThen (M.ifThen (somehow N)))

/-- Every `IPCBindAx` axiom is a theorem of natural deduction. -/
theorem IPCBindAx_deriv {Γ : List PLLFormula} {φ : PLLFormula}
    (h : IPCBindAx φ) : Nonempty (LaxND Γ φ) := by
  rcases h with ⟨a, rfl, _⟩ | ⟨M, N, rfl | rfl⟩
  · exact ⟨axiomDeriv Γ a⟩
  · exact ⟨axiomDeriv Γ (.somehowBind M N)⟩
  · exact ⟨.impIntro (.impIntro (.impElim
      (.iden (.tail _ (.head _)))
      (.laxIntro (.iden (.head _)))))⟩

/-- **F&M Lemma 2.1**: PLL consequence coincides with derivability in IPC
extended by the single scheme `(N ⊃ ◯K) ≡ (◯N ⊃ ◯K)`. -/
theorem lemma21 {Γ : List PLLFormula} {φ : PLLFormula} :
    HdOn IPCBindAx Γ φ ↔ Hd Γ φ := by
  constructor
  · -- IPC + adjunction ⟶ ND ⟶ full Hilbert
    intro h
    refine (hd_iff_ND).mpr ?_
    induction h with
    | ax h' => exact IPCBindAx_deriv h'
    | hyp h' => exact ⟨.iden h'⟩
    | mp _ _ ih₁ ih₂ =>
        obtain ⟨p₁⟩ := ih₁
        obtain ⟨p₂⟩ := ih₂
        exact ⟨.impElim p₁ p₂⟩
  · -- full Hilbert ⟶ ND ⟶ IPC + adjunction
    intro h
    obtain ⟨p⟩ := hd_iff_ND.mp h
    have hK : ∀ A B : PLLFormula, IPCBindAx (ifThen A (ifThen B A)) :=
      fun A B => .inl ⟨.impK A B, rfl, trivial⟩
    have hS : ∀ A B C : PLLFormula, IPCBindAx (ifThen (ifThen A (ifThen B C))
        (ifThen (ifThen A B) (ifThen A C))) :=
      fun A B C => .inl ⟨.impS A B C, rfl, trivial⟩
    clear h
    induction p with
    | iden h => exact .hyp h
    | falsoElim φ _ ih => exact .mp (.ax (.inl ⟨.explosion φ, rfl, trivial⟩)) ih
    | impIntro _ ih => exact HdOn.deduction hK hS ih
    | impElim _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
    | andIntro _ _ ih₁ ih₂ =>
        exact .mp (.mp (.ax (.inl ⟨.andIntro _ _, rfl, trivial⟩)) ih₁) ih₂
    | andElim1 _ ih => exact .mp (.ax (.inl ⟨.andElim1 _ _, rfl, trivial⟩)) ih
    | andElim2 _ ih => exact .mp (.ax (.inl ⟨.andElim2 _ _, rfl, trivial⟩)) ih
    | orIntro1 _ ih => exact .mp (.ax (.inl ⟨.orIntro1 _ _, rfl, trivial⟩)) ih
    | orIntro2 _ ih => exact .mp (.ax (.inl ⟨.orIntro2 _ _, rfl, trivial⟩)) ih
    | orElim _ _ _ ih₀ ih₁ ih₂ =>
        exact .mp (.mp (.mp (.ax (.inl ⟨.orElim _ _ _, rfl, trivial⟩))
          (HdOn.deduction hK hS ih₁)) (HdOn.deduction hK hS ih₂)) ih₀
    | @laxIntro Γ' φ' _ ih =>
        -- ◯R from the ← direction of the adjunction, at K := N := φ'
        have hadj : HdOn IPCBindAx Γ'
            (((somehow φ').ifThen (somehow φ')).ifThen
              (φ'.ifThen (somehow φ'))) :=
          .ax (.inr ⟨φ', φ', .inr rfl⟩)
        exact .mp (.mp hadj (HdOn.impSelf hK hS _)) ih
    | @laxElim Γ' φ' ψ' _ _ ih₁ ih₂ =>
        have hbind : HdOn IPCBindAx Γ'
            ((φ'.ifThen (somehow ψ')).ifThen
              ((somehow φ').ifThen (somehow ψ'))) :=
          .ax (.inr ⟨φ', ψ', .inl rfl⟩)
        exact .mp (.mp hbind (HdOn.deduction hK hS ih₂)) ih₁

end PLLND
