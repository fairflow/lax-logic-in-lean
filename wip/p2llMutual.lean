import wip.p2llRoundTrip

/-!
# Mutual interpretability: MP and MJ

File 9 of the P2LL definability campaign (`wip/p2ll-STATUS.md` §12): the
proofs of `MutualP2LL` and `MutualJ` of `wip/p2llStatements.lean`, in their
fragment-restricted wording of 2026-10-25.

    MP   Γ ⊢_P2LL φ  ⟺  [] ; Γ° ⊢_J φ°          (Γ, φ locally closed P2LL formulas)
    MJ   Θ ; Γ ⊢_J φ  ⟺  G(Θ), Γ* ⊢_P2LL φ*     (Γ, φ locally closed guarded formulas)

Left to right is I₁ (`toJD`), respectively I₂ (`relD`).  Right to left: I₂
(resp. I₁) brings the derivation back to the original calculus, with the
hypotheses doubly translated; the context is then translated back one
hypothesis at a time by `→I`, the round trip on that hypothesis and `→E`
(`ctxBackP`, `ctxBackJ`), and the conclusion by the other half of the round
trip.  For MJ the translated guards `(◯s → s)° = ◯°s → s`, `s ∈ Θ`, are
discharged first by C3 at the declared `s` (`peelGuards`).  Membership in a
context is never decoded into data: the context translations recurse on the
list itself.
-/

namespace P2LL

open Fm

/-! ## MP -/

/-- From hypotheses `(ψ°)*`, `ψ ∈ Γ`, to hypotheses `Γ`, by RTP on each `ψ`. -/
def ctxBackP : ∀ (Γ : List Fm), (∀ ψ ∈ Γ, LC ψ ∧ allJFree ψ) → ∀ (χ : Fm),
    LaxND2 ((Γ.map toJ).map rel) χ → LaxND2 Γ χ
  | [], _, _, d => d
  | ψ :: Γ, H, χ, d =>
    let hψ := H ψ (List.mem_cons_self ..)
    let d' : LaxND2 ((Γ.map toJ).map rel) (.imp (rel (toJ ψ)) χ) := .impIntro (lc_rt hψ.1) d
    let d'' := ctxBackP Γ (fun ψ' h => H ψ' (List.mem_cons_of_mem _ h)) _ d'
    .impElim (d''.weaken ψ)
      (.cut1 (rtpD (size ψ + 1) ψ (Nat.lt_succ_self _) hψ.1 hψ.2).1 hψ.1
        (.iden hψ.1 (List.mem_cons_self ..)))

/-- **MP.** -/
theorem mutualP2LL : MutualP2LL := fun Γ φ hΓ hφ hf =>
  ⟨fun ⟨d⟩ => ⟨toJD d []⟩,
   fun ⟨e⟩ => ⟨.cut1 (rtpD (size φ + 1) φ (Nat.lt_succ_self _) hφ hf).2 (lc_rt hφ)
      (ctxBackP Γ hΓ _ (relD e))⟩⟩

end P2LL

/-! ## Pins (upper bounds; first run at `[]`, see `wip/p2ll-STATUS.md` §12) -/

#axioms_within P2LL.ctxBackP [propext]
#axioms_within P2LL.mutualP2LL [propext]
