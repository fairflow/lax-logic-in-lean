/-
BiLax round 2 — THE DISPROOF BRIDGE, and a calibration refutation.

`Hintikka.not_laxND` is the whole point of the build: a saturated open
branch carrying the embedded sequent certifies that the PLL sequent is
NOT DERIVABLE — kernel-checked, no battery enumeration, no cut
admissibility, no ND↔labelled equivalence.  The chain is

  Hintikka  --truth-->  a BiModel refuting emb φ from emb Γ
            --bforce_emb-->  the SAME model (its ConstraintModel part)
                             refutes φ from Γ
            --PLLND.soundness-->  ¬ Nonempty (LaxND Γ φ).

The calibration below re-derives, as a Hintikka structure, the
separation `⊬ ¬◯⊥` (equivalently: `◯⊥` and `⊥` are not interderivable
— the first rung of RN(◯,{})), and the standing repo landmark
`◯p ⊬ p`.  These are the smallest members of the acceptance corpus
(docs/pcll-closed-fragment-catalogue.md).
-/
import BiLax.Hintikka

namespace BiLax

namespace Hintikka

variable (H : Hintikka)

/-- **The bridge to PLL**: a Hintikka structure carrying the EMBEDDED
sequent certifies PLL-underivability. -/
theorem not_laxND {Γ : List PLLFormula} {φ : PLLFormula} (x : Fin H.n)
    (hΓ : ∀ ψ ∈ Γ, H.L x (emb ψ)) (hφ : H.R x (emb φ)) :
    ¬ Nonempty (PLLND.LaxND Γ φ) := by
  rintro ⟨p⟩
  refine (H.truth (emb φ) x).2 hφ ?_
  refine (bforce_emb H.toModel φ x).mpr
    (PLLND.soundness p H.toModel.toConstraintModel x ?_)
  intro ψ hψ
  exact (bforce_emb H.toModel ψ x).mp ((H.truth (emb ψ) x).1 (hΓ ψ hψ))

end Hintikka

/-! ## Calibration 1: `⊬ ¬◯⊥`

The actual saturated branch for the goal `¬◯⊥ = ◯⊥ ⇾ ⊥` at world 0:

    R 0 (◯⊥ ⇾ ⊥)  --impR-->  L 0 ◯⊥,  R 0 ⊥
    L 0 ◯⊥        --laxL-->  L 1 ⊥ (with rm 0 1, rm 1 1)
    L 1 ⊥         --botL-->  fal 1

Two worlds `0 ≤ 1`, `1` fallible, all three relations the order.  The
branch is open (`R 0 = {◯⊥⇾⊥, ⊥}`, `L 0 = {◯⊥}`), so it is a
countermodel — and `⊥ ∈ R 0` records exactly the fact that world 0 is
NOT fallible. -/

private abbrev oBot : BiForm := emb (.somehow .falsePLL)
private abbrev negOBot : BiForm := emb (.ifThen (.somehow .falsePLL) .falsePLL)

def chainH : Hintikka where
  n := 2
  ri x y := x.val ≤ y.val
  rm x y := x.val ≤ y.val
  rc x y := y.val = 1
  fal x := x.val = 1
  L x A := (x.val = 0 ∧ A = oBot) ∨ (x.val = 1 ∧ IsForward A)
  R x A := x.val = 0 ∧ (A = negOBot ∨ A = .bot)
  ri_refl := fun _ => le_refl _
  ri_trans := fun h1 h2 => le_trans h1 h2
  rm_refl := fun _ => le_refl _
  rm_trans := fun h1 h2 => le_trans h1 h2
  sub_mi := fun h => h
  fal_hered := by intro x y h hx; omega
  square_c := by
    intro w u v h1 h2
    refine ⟨w, le_refl _, ?_⟩
    have := v.isLt
    have := u.isLt
    show v.val = 1
    omega
  counit_c := by
    intro w u h
    refine ⟨w, le_refl _, fun y hy => ?_⟩
    have := y.isLt
    show y.val ≤ u.val
    omega
  serial_c := by
    intro v
    refine ⟨⟨1, by omega⟩, ?_, rfl⟩
    have := v.isLt
    show v.val ≤ 1
    omega
  open_lr := by
    rintro x A (⟨hx0, rfl⟩ | ⟨hx1, hfw⟩) ⟨hr0, (heq | heq)⟩
    · exact absurd heq (by simp [negOBot, oBot, emb])
    · exact absurd heq (by simp [negOBot, oBot, emb])
    · omega
    · omega
  prop_hered := by
    rintro x y a h (⟨hx0, heq⟩ | ⟨hx1, hfw⟩)
    · exact absurd heq (by simp [negOBot, oBot, emb])
    · exact .inr ⟨by omega, hfw⟩
  fal_no_prop := by rintro x a hx ⟨hr0, -⟩; omega
  fal_no_bot := by rintro x hx ⟨hr0, -⟩; omega
  bot_left := by
    rintro x (⟨hx0, heq⟩ | ⟨hx1, -⟩)
    · exact absurd heq (by simp [negOBot, oBot, emb])
    · exact hx1
  sat_andL := by
    rintro x A B (⟨hx0, heq⟩ | ⟨hx1, hfw⟩)
    · exact absurd heq (by simp [negOBot, oBot, emb])
    · exact ⟨.inr ⟨hx1, hfw.1⟩, .inr ⟨hx1, hfw.2⟩⟩
  sat_andR := by
    rintro x A B ⟨hr0, (heq | heq)⟩ <;> exact absurd heq (by simp [negOBot, oBot, emb])
  sat_orL := by
    rintro x A B (⟨hx0, heq⟩ | ⟨hx1, hfw⟩)
    · exact absurd heq (by simp [negOBot, oBot, emb])
    · exact .inl (.inr ⟨hx1, hfw.1⟩)
  sat_orR := by
    rintro x A B ⟨hr0, (heq | heq)⟩ <;> exact absurd heq (by simp [negOBot, oBot, emb])
  sat_impL := by
    rintro x y A B (⟨hx0, heq⟩ | ⟨hx1, hfw⟩) hxy
    · exact absurd heq (by simp [negOBot, oBot, emb])
    · exact .inr (.inr ⟨by omega, hfw.2⟩)
  sat_impR := by
    rintro x A B ⟨hr0, (heq | heq)⟩
    · simp only [negOBot, emb] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨x, le_refl _, .inl ⟨hr0, rfl⟩, ⟨hr0, .inr rfl⟩⟩
    · exact absurd heq (by simp [negOBot, oBot, emb])
  sat_coimpL := by
    rintro x A B (⟨hx0, heq⟩ | ⟨hx1, hfw⟩)
    · exact absurd heq (by simp [negOBot, oBot, emb])
    · exact absurd hfw not_false
  sat_coimpR := by
    rintro x y A B ⟨hr0, (heq | heq)⟩ <;> exact absurd heq (by simp [negOBot, oBot, emb])
  sat_laxL := by
    rintro x y A (⟨hx0, heq⟩ | ⟨hx1, hfw⟩) hxy
    · have hA : A = BiForm.bot := by
        simpa [oBot, emb] using heq
      subst hA
      refine ⟨⟨1, by omega⟩, ?_, .inr ⟨rfl, trivial⟩⟩
      have := y.isLt
      show y.val ≤ 1
      omega
    · exact ⟨y, le_refl _, .inr ⟨by omega, hfw⟩⟩
  sat_laxR := by
    rintro x A ⟨hr0, (heq | heq)⟩ <;> exact absurd heq (by simp [negOBot, oBot, emb])
  sat_colaxL := by
    rintro x A (⟨hx0, heq⟩ | ⟨hx1, hfw⟩)
    · exact absurd heq (by simp [negOBot, oBot, emb])
    · exact absurd hfw not_false
  sat_colaxR := by
    rintro x u A ⟨hr0, (heq | heq)⟩ <;> exact absurd heq (by simp [negOBot, oBot, emb])

/-- **`¬◯⊥` is not a theorem of PLL** — certified by the branch, not
by a battery search. -/
theorem not_derivable_negOBot :
    ¬ Nonempty (PLLND.LaxND [] (.ifThen (.somehow .falsePLL) .falsePLL)) :=
  chainH.not_laxND (0 : Fin 2) (by simp) ⟨rfl, .inl rfl⟩

/-! ## Calibration 2: `◯p ⊬ p` (the repo landmark, atoms exercised)

Branch: `R 0 p`, `L 0 ◯p`, and `laxL` supplies an `Rm`-successor `1`
with `L 1 p`.  `Rc` again points at the top world.  No fallible world:
this refutation needs none. -/

private abbrev pAtom : BiForm := emb (.prop "p")
private abbrev boxP : BiForm := emb (.somehow (.prop "p"))

def boxpH : Hintikka where
  n := 2
  ri x y := x.val ≤ y.val
  rm x y := x.val ≤ y.val
  rc _ y := y.val = 1
  fal _ := False
  L x A := (x.val = 0 ∧ A = boxP) ∨ (x.val = 1 ∧ A = pAtom)
  R x A := x.val = 0 ∧ A = pAtom
  ri_refl := fun _ => le_refl _
  ri_trans := fun h1 h2 => le_trans h1 h2
  rm_refl := fun _ => le_refl _
  rm_trans := fun h1 h2 => le_trans h1 h2
  sub_mi := fun h => h
  fal_hered := fun _ h => h
  square_c := by
    intro w u v h1 h2
    refine ⟨w, le_refl _, ?_⟩
    have := v.isLt; have := u.isLt
    show v.val = 1
    omega
  counit_c := by
    intro w u h
    refine ⟨w, le_refl _, fun y hy => ?_⟩
    have := y.isLt
    show y.val ≤ u.val
    omega
  serial_c := by
    intro v
    refine ⟨⟨1, by omega⟩, ?_, rfl⟩
    have := v.isLt
    show v.val ≤ 1
    omega
  open_lr := by
    rintro x A (⟨hx0, rfl⟩ | ⟨hx1, rfl⟩) ⟨hr0, heq⟩
    · exact absurd heq (by simp [boxP, pAtom, emb])
    · omega
  prop_hered := by
    rintro x y a h (⟨hx0, heq⟩ | ⟨hx1, heq⟩)
    · exact absurd heq (by simp [boxP, emb])
    · exact .inr ⟨by omega, heq⟩
  fal_no_prop := by rintro x a hx -; exact hx
  fal_no_bot := by rintro x hx -; exact hx
  bot_left := by
    rintro x (⟨hx0, heq⟩ | ⟨hx1, heq⟩)
    · exact absurd heq (by simp [boxP, emb])
    · exact absurd heq (by simp [pAtom, emb])
  sat_andL := by
    rintro x A B (⟨hx0, heq⟩ | ⟨hx1, heq⟩) <;>
      exact absurd heq (by simp [boxP, pAtom, emb])
  sat_andR := by rintro x A B ⟨hr0, heq⟩; exact absurd heq (by simp [pAtom, emb])
  sat_orL := by
    rintro x A B (⟨hx0, heq⟩ | ⟨hx1, heq⟩) <;>
      exact absurd heq (by simp [boxP, pAtom, emb])
  sat_orR := by rintro x A B ⟨hr0, heq⟩; exact absurd heq (by simp [pAtom, emb])
  sat_impL := by
    rintro x y A B (⟨hx0, heq⟩ | ⟨hx1, heq⟩) hxy <;>
      exact absurd heq (by simp [boxP, pAtom, emb])
  sat_impR := by rintro x A B ⟨hr0, heq⟩; exact absurd heq (by simp [pAtom, emb])
  sat_coimpL := by
    rintro x A B (⟨hx0, heq⟩ | ⟨hx1, heq⟩) <;>
      exact absurd heq (by simp [boxP, pAtom, emb])
  sat_coimpR := by
    rintro x y A B ⟨hr0, heq⟩; exact absurd heq (by simp [pAtom, emb])
  sat_laxL := by
    rintro x y A (⟨hx0, heq⟩ | ⟨hx1, heq⟩) hxy
    · have hA : A = pAtom := by simpa [boxP, pAtom, emb] using heq
      subst hA
      refine ⟨⟨1, by omega⟩, ?_, .inr ⟨rfl, rfl⟩⟩
      have := y.isLt
      show y.val ≤ 1
      omega
    · exact absurd heq (by simp [pAtom, emb])
  sat_laxR := by rintro x A ⟨hr0, heq⟩; exact absurd heq (by simp [pAtom, emb])
  sat_colaxL := by
    rintro x A (⟨hx0, heq⟩ | ⟨hx1, heq⟩) <;>
      exact absurd heq (by simp [boxP, pAtom, emb])
  sat_colaxR := by
    rintro x u A ⟨hr0, heq⟩; exact absurd heq (by simp [pAtom, emb])

/-- **`◯p ⊬ p`** — the repo landmark, certified by a branch. -/
theorem not_derivable_boxp_p :
    ¬ Nonempty (PLLND.LaxND [.somehow (.prop "p")] (.prop "p")) :=
  boxpH.not_laxND (0 : Fin 2)
    (by
      intro ψ hψ
      simp only [List.mem_singleton] at hψ
      subst hψ
      exact .inl ⟨rfl, rfl⟩)
    ⟨rfl, rfl⟩

/-! ## Pins -/

/--
info: 'BiLax.Hintikka.not_laxND' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Hintikka.not_laxND

/--
info: 'BiLax.not_derivable_negOBot' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_derivable_negOBot

/--
info: 'BiLax.not_derivable_boxp_p' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_derivable_boxp_p

end BiLax
