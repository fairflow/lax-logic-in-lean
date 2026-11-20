/-
# Uniform interpolation for CK

Source: I. van der Giessen and I. Shillito, "Uniform interpolation with
constructive diamond", arXiv:2602.16880, §4: Theorem 4 (`thm:UIP_CK`) and its
corollary, "CK has the uniform interpolation property".  Rocq:
`theories/Sequent/G4CK/CKPropQuantifiers.v` of github.com/ianshil/CK,
`CK_uniform_interpolation`.

The theorem is the authors'; this file is a re-proof in Lean, in the form of
the Rocq statement.  The three parts are `Ep_vars`, `Ap_vars`
(`CK/InterpVars.lean`), `Ep_entail`, `Ap_entail` (`CK/InterpEntail.lean`) and
`pq_correct` (`CK/InterpUniform.lean`).
-/
import CK.InterpUniform

namespace CK

open Form

/-- Every variable of `φ` is in the list `V`.  Rocq `vars_incl`. -/
def VarsIncl (φ : Form) (V : List Nat) : Prop := ∀ x, Occurs x φ → x ∈ V

/-- **Uniform interpolation for G4CK.**  Rocq `CK_uniform_interpolation`.

For `p ∉ V` and `φ` over `p, V`:

    Vars(∃p φ) ⊆ V     φ ⇒ ∃p φ     φ ⇒ ψ gives ∃p φ ⇒ ψ   for ψ over V
    Vars(∀p φ) ⊆ V     ∀p φ ⇒ φ     θ ⇒ φ gives θ ⇒ ∀p φ   for θ over V

where `∃p φ = Ef p φ` and `∀p φ = Af p φ`. -/
theorem G4CK_uniform_interpolation (p : Nat) (V : List Nat) (hp : p ∉ V) (φ : Form)
    (hφ : VarsIncl φ (p :: V)) :
    VarsIncl (Ef p φ) V
    ∧ G4CK [φ] (Ef p φ)
    ∧ (∀ ψ, VarsIncl ψ V → G4CK [φ] ψ → G4CK [Ef p φ] ψ)
    ∧ VarsIncl (Af p φ) V
    ∧ G4CK [Af p φ] φ
    ∧ (∀ θ, VarsIncl θ V → G4CK [θ] φ → G4CK [θ] (Af p φ)) := by
  have inV : ∀ x, x ≠ p → Occurs x φ → x ∈ V := fun x hx ho => by
    rcases List.mem_cons.1 (hφ x ho) with e | h
    · exact absurd e hx
    · exact h
  refine ⟨?_, Ep_entail p [φ], ?_, ?_, Ap_entail p [] φ, ?_⟩
  · intro x hx
    obtain ⟨hne, θ, hθ, ho⟩ := Ep_vars hx
    rcases List.mem_cons.1 hθ with rfl | h
    · exact inV x hne ho
    · exact nomatch h
  · intro ψ hψ d
    exact (pq_correct (Γ := []) (Δ := [φ]) (fun _ h => nomatch h) d).1 fun h => hp (hψ p h)
  · intro x hx
    obtain ⟨hne, ho | ⟨θ, hθ, _⟩⟩ := Ap_vars hx
    · exact inV x hne ho
    · exact nomatch hθ
  · intro θ hθ d
    have h₁ : G4CK (Ep p [] :: [θ]) (Af p φ) :=
      (pq_correct (Γ := [θ]) (Δ := []) (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | h
        · exact fun h => hp (hθ p h)
        · exact nomatch h) d).2
    exact ((Ep_entail p []).weaken θ).cut h₁

/-- **Corollary: CK has the uniform interpolation property**, for the
Hilbert calculus `CKH` of §2, by Theorem 2 (`G4CK_iff_CKH`). -/
theorem CK_uniform_interpolation (p : Nat) (V : List Nat) (hp : p ∉ V) (φ : Form)
    (hφ : VarsIncl φ (p :: V)) :
    VarsIncl (Ef p φ) V
    ∧ CKH (ctx [φ]) (Ef p φ)
    ∧ (∀ ψ, VarsIncl ψ V → CKH (ctx [φ]) ψ → CKH (ctx [Ef p φ]) ψ)
    ∧ VarsIncl (Af p φ) V
    ∧ CKH (ctx [Af p φ]) φ
    ∧ (∀ θ, VarsIncl θ V → CKH (ctx [θ]) φ → CKH (ctx [θ]) (Af p φ)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := G4CK_uniform_interpolation p V hp φ hφ
  exact ⟨h₁, G4CK_iff_CKH.1 h₂, fun ψ hψ d => G4CK_iff_CKH.1 (h₃ ψ hψ (G4CK_iff_CKH.2 d)),
    h₄, G4CK_iff_CKH.1 h₅, fun θ hθ d => G4CK_iff_CKH.1 (h₆ θ hθ (G4CK_iff_CKH.2 d))⟩

/-- **CK has the uniform interpolation property**, in the usual form for a
logic (the paper's Definition 3, `def:UIP`): for every formula `φ` and
variable `p` the formulas `∃p φ := Ef p φ` and `∀p φ := Af p φ` contain only
variables of `φ` other than `p`, and for every `ψ` without `p`

    ⊢ φ → ∃p φ          ⊢ φ → ψ  gives  ⊢ ∃p φ → ψ
    ⊢ ∀p φ → φ          ⊢ ψ → φ  gives  ⊢ ψ → ∀p φ

where `⊢` is derivability in `CKH` from no assumptions. -/
theorem CK_UIP (p : Nat) (φ : Form) :
    (∀ x, Occurs x (Ef p φ) → x ≠ p ∧ Occurs x φ)
    ∧ CKH (ctx []) (φ ⟶ Ef p φ)
    ∧ (∀ ψ, ¬Occurs p ψ → CKH (ctx []) (φ ⟶ ψ) → CKH (ctx []) (Ef p φ ⟶ ψ))
    ∧ (∀ x, Occurs x (Af p φ) → x ≠ p ∧ Occurs x φ)
    ∧ CKH (ctx []) (Af p φ ⟶ φ)
    ∧ (∀ ψ, ¬Occurs p ψ → CKH (ctx []) (ψ ⟶ φ) → CKH (ctx []) (ψ ⟶ Af p φ)) := by
  refine ⟨?_, G4CK_iff_CKH.1 (.impR (Ep_entail p [φ])), ?_, ?_,
    G4CK_iff_CKH.1 (.impR (Ap_entail p [] φ)), ?_⟩
  · intro x hx
    obtain ⟨hne, θ, hθ, ho⟩ := Ep_vars hx
    rcases List.mem_cons.1 hθ with rfl | h
    · exact ⟨hne, ho⟩
    · exact nomatch h
  · intro ψ hψ d
    have d' : G4CK [φ] ψ := (G4CK_iff_CKH.2 d).impR_inv
    exact G4CK_iff_CKH.1 (.impR
      ((pq_correct (Γ := []) (Δ := [φ]) (fun _ h => nomatch h) d').1 hψ))
  · intro x hx
    obtain ⟨hne, ho | ⟨θ, hθ, _⟩⟩ := Ap_vars hx
    · exact ⟨hne, ho⟩
    · exact nomatch hθ
  · intro ψ hψ d
    have d' : G4CK [ψ] φ := (G4CK_iff_CKH.2 d).impR_inv
    have h₁ : G4CK (Ep p [] :: [ψ]) (Af p φ) :=
      (pq_correct (Γ := [ψ]) (Δ := []) (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | h
        · exact hψ
        · exact nomatch h) d').2
    exact G4CK_iff_CKH.1 (.impR (((Ep_entail p []).weaken ψ).cut h₁))

#print axioms G4CK_uniform_interpolation
#print axioms CK_uniform_interpolation
#print axioms CK_UIP

end CK
