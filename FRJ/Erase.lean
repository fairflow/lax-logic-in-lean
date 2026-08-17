/-
# ◯-erasure and the transfer route to transparent-model completeness

2026-08-17.  Matthew's observation: when a countermodel does not depend
on `Rm` — the model is ◯-TRANSPARENT, `Rm = id`, so `force a (◯A) ↔
force a A` — the ◯-machinery of the calculus "should be redundant".
Semantically it is: such a model refutes `G` exactly when the underlying
ordinary Kripke model refutes the ◯-erasure of `G`, and the erasure is
circ-free, so the PROVED ◯-free completeness (`FRJ/Minimal.lean`)
already refutes it in the calculus.  What is missing is purely
syntactic, the ERASURE TRANSFER

    (E)    Provable (erase G) → Provable G

— a derivation translation reinserting the ◯s.  This file holds the
semantic half and the wiring:

* `erase`, `noCirc`, `erase_hcf` — the erasure and its circ-freeness;
* `force_erase` — over a transparent model, `force a (erase A) ↔
  force a A` (the semantic half; PROVED);
* `completeness_of_transparent_of_lift` — completeness over transparent
  infallible models, conditional on (E) for the given goal (PROVED
  relative to its `hlift` hypothesis).

(E) itself is OPEN; per the testing mandate it gets the extensional
attack (`wip/frj_sat.lean`, erasure-transfer block) before any proof
build is scoped.
-/
import FRJ.Minimal

namespace FRJ

open Form

/-- ◯-erasure: the collapse translation `◯ := id`, homomorphic on the
rest of the syntax. -/
def erase : Form → Form
  | .atom p => .atom p
  | .bot => .bot
  | .and A B => .and (erase A) (erase B)
  | .or A B => .or (erase A) (erase B)
  | .imp A B => .imp (erase A) (erase B)
  | .circ A => erase A

/-- No occurrence of `◯` anywhere in the formula. -/
def noCirc : Form → Bool
  | .atom _ => true
  | .bot => true
  | .and A B => noCirc A && noCirc B
  | .or A B => noCirc A && noCirc B
  | .imp A B => noCirc A && noCirc B
  | .circ _ => false

theorem noCirc_erase : ∀ A : Form, noCirc (erase A) = true
  | .atom _ => rfl
  | .bot => rfl
  | .and A B => by simp [erase, noCirc, noCirc_erase A, noCirc_erase B]
  | .or A B => by simp [erase, noCirc, noCirc_erase A, noCirc_erase B]
  | .imp A B => by simp [erase, noCirc, noCirc_erase A, noCirc_erase B]
  | .circ A => noCirc_erase A

/-- Every signed subformula of a `◯`-free formula is non-`◯`. -/
theorem mem_sf_noCirc : ∀ A : Form, noCirc A = true → ∀ X : Form,
    (X ∈ (sfPos A).1 ∨ X ∈ (sfPos A).2 ∨ X ∈ (sfNeg A).1 ∨ X ∈ (sfNeg A).2) →
    X.isCirc = false := by
  intro A
  induction A with
  | atom p =>
      intro _ X hX
      rcases hX with h | h | h | h <;> simp only [sfPos, sfNeg] at h <;>
        first
          | (simp only [List.mem_singleton] at h; simp [h, isCirc])
          | exact absurd h (List.not_mem_nil)
  | bot =>
      intro _ X hX
      rcases hX with h | h | h | h <;> simp only [sfPos, sfNeg] at h <;>
        first
          | (simp only [List.mem_singleton] at h; simp [h, isCirc])
          | exact absurd h (List.not_mem_nil)
  | and A B ihA ihB =>
      intro hnc X hX
      simp only [noCirc, Bool.and_eq_true] at hnc
      rcases hX with h | h | h | h <;>
        simp only [sfPos, sfNeg, List.mem_cons, List.mem_append] at h
      · rcases h with h | h | h
        · subst h; rfl
        · exact ihA hnc.1 X (Or.inl h)
        · exact ihB hnc.2 X (Or.inl h)
      · rcases h with h | h
        · exact ihA hnc.1 X (Or.inr (Or.inl h))
        · exact ihB hnc.2 X (Or.inr (Or.inl h))
      · rcases h with h | h
        · exact ihA hnc.1 X (Or.inr (Or.inr (Or.inl h)))
        · exact ihB hnc.2 X (Or.inr (Or.inr (Or.inl h)))
      · rcases h with h | h | h
        · subst h; rfl
        · exact ihA hnc.1 X (Or.inr (Or.inr (Or.inr h)))
        · exact ihB hnc.2 X (Or.inr (Or.inr (Or.inr h)))
  | or A B ihA ihB =>
      intro hnc X hX
      simp only [noCirc, Bool.and_eq_true] at hnc
      rcases hX with h | h | h | h <;>
        simp only [sfPos, sfNeg, List.mem_cons, List.mem_append] at h
      · rcases h with h | h | h
        · subst h; rfl
        · exact ihA hnc.1 X (Or.inl h)
        · exact ihB hnc.2 X (Or.inl h)
      · rcases h with h | h
        · exact ihA hnc.1 X (Or.inr (Or.inl h))
        · exact ihB hnc.2 X (Or.inr (Or.inl h))
      · rcases h with h | h
        · exact ihA hnc.1 X (Or.inr (Or.inr (Or.inl h)))
        · exact ihB hnc.2 X (Or.inr (Or.inr (Or.inl h)))
      · rcases h with h | h | h
        · subst h; rfl
        · exact ihA hnc.1 X (Or.inr (Or.inr (Or.inr h)))
        · exact ihB hnc.2 X (Or.inr (Or.inr (Or.inr h)))
  | imp A B ihA ihB =>
      intro hnc X hX
      simp only [noCirc, Bool.and_eq_true] at hnc
      rcases hX with h | h | h | h <;>
        simp only [sfPos, sfNeg, List.mem_cons, List.mem_append] at h
      · rcases h with h | h | h
        · subst h; rfl
        · exact ihA hnc.1 X (Or.inr (Or.inr (Or.inl h)))
        · exact ihB hnc.2 X (Or.inl h)
      · rcases h with h | h
        · exact ihA hnc.1 X (Or.inr (Or.inr (Or.inr h)))
        · exact ihB hnc.2 X (Or.inr (Or.inl h))
      · rcases h with h | h
        · exact ihA hnc.1 X (Or.inl h)
        · exact ihB hnc.2 X (Or.inr (Or.inr (Or.inl h)))
      · rcases h with h | h | h
        · subst h; rfl
        · exact ihA hnc.1 X (Or.inr (Or.inl h))
        · exact ihB hnc.2 X (Or.inr (Or.inr (Or.inr h)))
  | circ A ih =>
      intro hnc
      exact absurd hnc (by simp [noCirc])

/-- The erasure satisfies the circ-freeness hypothesis of the ◯-free
completeness (`FRJ/Minimal.lean`). -/
theorem erase_hcf (G : Form) :
    ∀ X ∈ sfR (erase G) ++ sfL (erase G), X.isCirc = false := by
  intro X hX
  rcases List.mem_append.mp hX with h | h
  · exact mem_sf_noCirc (erase G) (noCirc_erase G) X (Or.inl h)
  · exact mem_sf_noCirc (erase G) (noCirc_erase G) X (Or.inr (Or.inl h))

/-! ## The semantic half: transparency

A model is ◯-TRANSPARENT when `Rm` is the identity — with `rm_refl` the
hypothesis `Rm a u → u = a` makes them equal.  This is a legal frame
(`id` is a preorder inside `≤`), and on it the `◯`-clause of forcing
collapses. -/

/-- Over a transparent model the erasure forces exactly as the original:

    `force a (erase A) ↔ force a A`. -/
theorem force_erase {K : Kripke} (hRm : ∀ {a u : K.W}, K.Rm a u → u = a) :
    ∀ (A : Form) (a : K.W), K.force a (erase A) ↔ K.force a A := by
  intro A
  induction A with
  | atom p => intro a; exact Iff.rfl
  | bot => intro a; exact Iff.rfl
  | and A B ihA ihB => intro a; exact and_congr (ihA a) (ihB a)
  | or A B ihA ihB => intro a; exact or_congr (ihA a) (ihB a)
  | imp A B ihA ihB =>
      intro a
      constructor
      · intro h b hab hA
        exact (ihB b).mp (h b hab ((ihA b).mpr hA))
      · intro h b hab hA
        exact (ihB b).mpr (h b hab ((ihA b).mp hA))
  | circ A ih =>
      intro a
      constructor
      · intro h b hab
        exact ⟨b, K.rm_refl b, K.force_mono hab ((ih a).mp h)⟩
      · intro h
        obtain ⟨c, hrm, hc⟩ := h a (K.le_refl a)
        exact (ih a).mpr (hRm hrm ▸ hc)

theorem valid_erase {K : Kripke} {G : Form}
    (hRm : ∀ {a u : K.W}, K.Rm a u → u = a) :
    K.valid (erase G) ↔ K.valid G :=
  force_erase hRm G K.root

/-! ## The wiring: completeness over transparent models, modulo (E) -/

/-- **Completeness over ◯-transparent infallible models, conditional on
the erasure transfer** `hlift : Provable (erase G) → Provable G`.  The
chain: the transparent countermodel refutes the (circ-free) erasure,
the PROVED ◯-free completeness derives the erasure's refutation, and
`hlift` reinstates the ◯s.  Discharging `hlift` — statement (E) — is
the open syntactic content; nothing semantic remains. -/
theorem completeness_of_transparent_of_lift {G : Form} {K : Kripke}
    (hlift : Provable (erase G) → Provable G)
    (hRm : ∀ {a u : K.W}, K.Rm a u → u = a)
    (hinf : K.Infallible) (hK : ¬ K.valid G) : Provable G :=
  hlift (completeness (erase_hcf G) K hinf
    (fun h => hK ((valid_erase hRm).mp h)))

end FRJ
