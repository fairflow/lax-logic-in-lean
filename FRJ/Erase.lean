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
import FRJ.Saturate

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

/-! ## Transparent models and the supply route

Independently of the transfer: on a transparent model NO `◯`-formula
ever enters `Λ*` — membership demands `force a (◯Y) ∧ ¬ force a Y` and
transparency collapses the conjuncts — so the pledge supply of
`FRJ/Saturate.lean` is discharged VACUOUSLY, and the supply-conditional
completeness needs only the `◯`-corner kernel there. -/

theorem force_circ_transparent {K : Kripke}
    (hRm : ∀ {a u : K.W}, K.Rm a u → u = a) {a : K.W} {A : Form} :
    K.force a (.circ A) ↔ K.force a A := by
  constructor
  · intro h
    obtain ⟨c, hrm, hc⟩ := h a (K.le_refl a)
    exact hRm hrm ▸ hc
  · intro h b hab
    exact ⟨b, K.rm_refl b, K.force_mono hab h⟩

/-- Choice-free replacement for `List.filter_eq_nil_iff.mpr` (the
Mathlib lemma pins `Classical.choice`). -/
theorem filter_eq_nil_of {α : Type _} {p : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
      have ha := h a List.mem_cons_self
      simp [ha,
        filter_eq_nil_of (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem circPart_lamStar_nil_of_transparent {K : Kripke}
    (hRm : ∀ {a u : K.W}, K.Rm a u → u = a) (b : K.W) (G : Form) :
    circPart (lamStar K b G) = [] := by
  refine filter_eq_nil_of ?_
  intro H hH
  cases H with
  | atom p => rfl
  | bot => rfl
  | and A B => rfl
  | or A B => rfl
  | imp A B => rfl
  | circ A =>
      have h := (mem_lamStar.mp hH).2
      exact absurd ((force_circ_transparent hRm).mp h.1) h.2

/-- Completeness over transparent models, through the SUPPLY route: the
pledge side is vacuous there, so only `CircSupply` remains.  (The
transfer route below is the one that also eliminates `CircSupply`.) -/
theorem completeness_of_transparent_of_circSupply {G : Form} {K : Kripke}
    (hRm : ∀ {a u : K.W}, K.Rm a u → u = a)
    (hsup : CircSupply K G) (hK : ¬ K.valid G) : Provable G :=
  completeness_of_supply
    (pledgeSupply_of_locFree fun b => circPart_lamStar_nil_of_transparent hRm b G)
    hsup hK

/-! ## Zone shape helpers -/

theorem mem_gHat_shape {G X : Form} (h : X ∈ gHat G) :
    X.isPV = true ∨ X.isImp = true ∨ X.isCirc = true := by
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl (List.mem_filter.mp h).2
    · exact Or.inr (Or.inl (List.mem_filter.mp h).2)
  · exact Or.inr (Or.inr (List.mem_filter.mp h).2)

theorem mem_gAt_of {G X : Form} (hX : X ∈ sfL G) (hPV : X.isPV = true) :
    X ∈ gAt G := List.mem_filter.mpr ⟨hX, hPV⟩

theorem mem_gImp_of {G X : Form} (hX : X ∈ sfL G) (hI : X.isImp = true) :
    X ∈ gImp G := List.mem_filter.mpr ⟨hX, hI⟩

theorem gAt_sub_gHat {G : Form} : gAt G ⊆ gHat G := fun _ h =>
  List.mem_append_left _ (List.mem_append_left _ h)

theorem gImp_sub_gHat {G : Form} : gImp G ⊆ gHat G := fun _ h =>
  List.mem_append_left _ (List.mem_append_right _ h)

/-! ## The closure lift

The first load-bearing piece of the derivation translation. -/

/-- **Closure lift.**  For a LEFT-position formula `X'` of `G`: if its
erasure lies in `Cl(Δ)` for an `Ĝ(erase G)`-zone `Δ`, then `X'` lies in
`Cl(Γ)` for any `Γ` containing the `Ĝ(G)`-preimages of `Δ`.  The
`◯`-layers of `X'` are reinstated by `Clo.circ`; base cases land by the
preimage property; compound shapes invert the closure derivation. -/
theorem clo_lift {G : Form} {Δ Γ : List Form}
    (hΔ : ∀ V ∈ Δ, V ∈ gHat (erase G))
    (hpre : ∀ V' ∈ gHat G, erase V' ∈ Δ → V' ∈ Γ) :
    ∀ X' : Form, X' ∈ sfL G → Clo Δ (erase X') → Clo Γ X' := by
  intro X'
  induction X' with
  | atom p =>
      intro hpos hE
      simp only [erase] at hE
      cases hE with
      | base hmem => exact .base (hpre _ (gAt_sub_gHat (mem_gAt_of hpos rfl)) hmem)
  | bot =>
      intro hpos hE
      simp only [erase] at hE
      cases hE with
      | base hmem =>
          rcases mem_gHat_shape (hΔ _ hmem) with h | h | h <;>
            simp [Form.isPV, Form.isImp, Form.isCirc] at h
  | and A B ihA ihB =>
      intro hpos hE
      simp only [erase] at hE
      cases hE with
      | base hmem =>
          rcases mem_gHat_shape (hΔ _ hmem) with h | h | h <;>
            simp [Form.isPV, Form.isImp, Form.isCirc] at h
      | and h1 h2 =>
          exact .and (ihA (sfL_and hpos).1 h1) (ihB (sfL_and hpos).2 h2)
  | or A B ihA ihB =>
      intro hpos hE
      simp only [erase] at hE
      cases hE with
      | base hmem =>
          rcases mem_gHat_shape (hΔ _ hmem) with h | h | h <;>
            simp [Form.isPV, Form.isImp, Form.isCirc] at h
      | orR h => exact .orR (ihB (sfL_or hpos).2 h)
      | orL h => exact .orL (ihA (sfL_or hpos).1 h)
  | imp A B _ihA ihB =>
      intro hpos hE
      simp only [erase] at hE
      cases hE with
      | base hmem => exact .base (hpre _ (gImp_sub_gHat (mem_gImp_of hpos rfl)) hmem)
      | imp h => exact .imp (ihB (sfL_imp hpos).2 h)
  | circ A ih =>
      intro hpos hE
      simp only [erase] at hE
      exact .circ (ih (sfL_circ hpos) hE)

end FRJ
