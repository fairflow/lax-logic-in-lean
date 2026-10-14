# Uniform interpolation for PLL

The ∀-side is proved, so uniform interpolation for PLL now holds in both directions, checked by the kernel.

`LaxLogic/PLL/SemUI/SubframeUI.lean` has no sorry. Each theorem depends only on `[propext, Classical.choice, Quot.sound]`. For every φ and p, and every p-free χ:

```
⊢ φ ↠ ∃p φ,       ⊢ φ ↠ χ  ⟹  ⊢ ∃p φ ↠ χ          (uniform_ex)
⊢ ∀p φ ↠ φ,       ⊢ χ ↠ φ  ⟹  ⊢ χ ↠ ∀p φ          (uniform_all)
```

* Both interpolants use only the atoms of φ other than p, and ⊢ is derivability in `LaxND`.
* The ◯-free instances (`uniform_exI`, `uniform_allI`), which are Pitts's theorem for IPC, came first.
* ∀-side construction: ∀p φ is the conjunction of `⋀T ↠ ⋁(R∖T)` over the types T that some refutation of φ realises. It needed no gluing lemma.
* ∃ and ∀ are independent here: neither proof uses the other, unlike Pitts's syntactic proof, where they are defined together.

## The Lean

Reading key: inside the namespace `PLLND`, `Γ ⊢ A` is the type of `LaxND`
derivations of `A` from the list `Γ`, so `Nonempty ([] ⊢ A)` says that `A` is
derivable, written `⊢ A` above; `ψ.atoms` is the set of atoms of `ψ`.

The two theorems, exactly as stated in the file:

```lean
theorem uniform_ex (p : String) (φ : PLLFormula) :
    ∃ ψ : PLLFormula, (∀ a ∈ ψ.atoms, a ∈ φ.atoms ∧ a ≠ p) ∧
      Nonempty ([] ⊢ φ ↠ ψ) ∧
      ∀ χ : PLLFormula, p ∉ χ.atoms →
        Nonempty ([] ⊢ φ ↠ χ) → Nonempty ([] ⊢ ψ ↠ χ)

theorem uniform_all (p : String) (φ : PLLFormula) :
    ∃ ψ : PLLFormula, (∀ a ∈ ψ.atoms, a ∈ φ.atoms ∧ a ≠ p) ∧
      Nonempty ([] ⊢ ψ ↠ φ) ∧
      ∀ χ : PLLFormula, p ∉ χ.atoms →
        Nonempty ([] ⊢ χ ↠ φ) → Nonempty ([] ⊢ χ ↠ ψ)
```

The interpolants, as the proofs supply them.  `R` is a finite list of
representatives, up to interderivability, of all formulas of the stated crank
over the atoms of φ other than p (`frag_reps_exist'`); `ν` counts the atoms,
implications and ◯-formulas among the subformulas of φ.

```lean
-- ∃p φ : the representatives (crank ≤ 3(3ν+2)+2) that φ implies, conjoined
obtain ⟨R, hRb, hR⟩ := frag_reps_exist' (φ.atoms.erase p)
  (3 * (3 * nu (insert PLLFormula.falsePLL (subF φ)) + 2) + 1 + 1)
bigAnd (R.filter fun D => decide (Nonempty (LaxND [] (φ.ifThen D))))

-- ∀p φ : over the representatives (crank ≤ 3(3ν+2)+1), the characters
--        ⋀T ↠ ⋁(R∖T) of the types T that some refutation of φ realises
obtain ⟨R, hRb, hR⟩ := frag_reps_exist' (φ.atoms.erase p)
  (3 * (3 * nu (insert PLLFormula.falsePLL (subF φ)) + 2) + 1)
bigAnd (((R.sublists).filter fun T => decide
    (¬ Nonempty (LaxND [] ((bigAnd T).ifThen ((bigOr (compl R T)).or φ))))).map
  (charT R))

noncomputable def compl (R T : List PLLFormula) : List PLLFormula :=
  R.filter fun D => decide (D ∉ T)

noncomputable def charT (R T : List PLLFormula) : PLLFormula :=
  (bigAnd T).ifThen (bigOr (compl R T))
```

The axioms, as the kernel reports them (pinned in the file with `#guard_msgs`):

```
'PLLND.SubframeModel.uniform_ex' depends on axioms: [propext, Classical.choice, Quot.sound]
'PLLND.SubframeModel.uniform_all' depends on axioms: [propext, Classical.choice, Quot.sound]
```
