import LaxLogic.PLLNDCore
import LaxLogic.PLLProof

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

end PLLND
