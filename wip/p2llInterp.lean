import wip.p2llStatements

/-!
# The two interpretations: I₁, Fix, I₂

File 6 of the P2LL definability campaign (`wip/p2ll-STATUS.md`): the proofs
of the first three statements of `wip/p2llStatements.lean`, each as a function
on derivations (the calculi are `Type`-valued with cofinite premises, so a
derivation is built from derivations, never from `Nonempty`), then packaged as
the stated proposition.

    I₁   Γ ⊢_P2LL φ  ⟹  ∀ Θ,  Θ ; Γ° ⊢_J φ°                    (`toJD`, `interpToJ`)
    Fix  IsJ Θ χ,  LC χ  ⟹  G(Θ) ⊢_P2LL ◯χ* → χ*               (`fixD`, `fixOfIsJ`)
    I₂   Θ ; Γ ⊢_J φ  ⟹  G(Θ), Γ* ⊢_P2LL φ*                    (`relD`, `interpToP2LL`)

The `◯` cases of I₁ are the cells C1 and C2, with the local closure of the
formulas from `LaxND2.lc`; the quantifier cases are `(ψ^χ)° = ψ°^χ°`
(`Fm.toJ_opn`).  Fix is the proof-theoretic form of "J-formulas denote fixed
points": a J-variable's law is its guard, `⊤`, `→` and `∧` are PLL
derivations, the binders use monotonicity of `◯` under `∀E` and the cofinite
`∀I`.  In I₂, `∀°I` is `∀I` plus `→I` on the new guard (`G(s :: Θ)` is
`(◯s → s) :: G(Θ)` definitionally), and `∀°E` is `∀E` at `χ*` discharged by
Fix; the quantifier cases are `(ψ^χ)* = ψ*^χ*` (`Fm.rel_opn`).

All three hold on the whole formula type: the inert constructors translate
homomorphically.  By `LaxND2.lc` and `JND.lc` every formula in a derivation is
locally closed.
-/

namespace P2LL

open Fm

/-! Two membership facts, by recursion on `List.Mem` (core's `List.mem_map`
goes through `simp` and carries `propext`, `Quot.sound`; `List.mem_append_left`
and `List.mem_append_right` are axiom-free and used as they are). -/

theorem mem_map_of_mem {α β : Type} (f : α → β) {a : α} {l : List α} (h : a ∈ l) :
    f a ∈ l.map f := by
  induction h
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (by assumption)

/-- `G ++ a :: l ⊆ a :: (G ++ l)`. -/
theorem mem_append_cons {α : Type} {G l : List α} {a x : α} :
    x ∈ G ++ a :: l → x ∈ a :: (G ++ l) := by
  induction G with
  | nil => exact fun h => h
  | cons g G ih =>
    intro h
    have h : x ∈ g :: (G ++ a :: l) := h
    cases h
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · rename_i h'
      have h'' : x ∈ a :: (G ++ l) := ih h'
      cases h''
      · exact List.mem_cons_self ..
      · rename_i h₃
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h₃)

/-! ## I₁: P2LL into the guarded calculus -/

/-- The translation of derivations under `(−)°`. -/
def toJD : ∀ {Γ : List Fm} {φ : Fm}, LaxND2 Γ φ → ∀ Θ : List String,
    JND IsJ Θ (Γ.map toJ) (toJ φ)
  | _, _, .iden hφ h, _ => .iden (lc_toJ hφ) (mem_map_of_mem toJ h)
  | _, _, .falsoElim φ hφ p, Θ => .falsoElim (toJ φ) (lc_toJ hφ) (toJD p Θ)
  | _, _, .impIntro hφ p, Θ => .impIntro (lc_toJ hφ) (toJD p Θ)
  | _, _, .impElim p₁ p₂, Θ => .impElim (toJD p₁ Θ) (toJD p₂ Θ)
  | _, _, .andIntro p₁ p₂, Θ => .andIntro (toJD p₁ Θ) (toJD p₂ Θ)
  | _, _, .andElim1 p, Θ => .andElim1 (toJD p Θ)
  | _, _, .andElim2 p, Θ => .andElim2 (toJD p Θ)
  | _, _, .orIntro1 hψ p, Θ => .orIntro1 (lc_toJ hψ) (toJD p Θ)
  | _, _, .orIntro2 hφ p, Θ => .orIntro2 (lc_toJ hφ) (toJD p Θ)
  | _, _, .orElim p₀ p₁ p₂, Θ => .orElim (toJD p₀ Θ) (toJD p₁ Θ) (toJD p₂ Θ)
  | _, _, @LaxND2.laxIntro _ φ p, Θ =>
      JND.circJ_intro IsJ.jmono (lc_toJ (φ := φ) p.lc) (toJD p Θ)
  | _, _, @LaxND2.laxElim _ φ ψ p₁ p₂, Θ =>
      JND.circJ_bind IsJ.jmono IsJ.jvars (lc_toJ (φ := φ) p₁.lc) (lc_toJ (φ := ψ) p₂.lc)
        (toJD p₁ Θ) (toJD p₂ Θ)
  | _, _, @LaxND2.allIntro _ ψ L hψ p, Θ =>
      .allIntro L (lcAt_toJ 1 ψ hψ) fun s hs => (toJ_opn_fvar ψ s) ▸ toJD (p s hs) Θ
  | _, _, @LaxND2.allElim _ ψ _ θ hχ p e, Θ =>
      .allElim (lc_toJ hχ) (toJD p Θ) ((congrArg toJ e).trans (toJ_opn ψ hχ))

/-- **I₁.** -/
theorem interpToJ : InterpToJ := fun _ _ p Θ => ⟨toJD p Θ⟩

/-! ## Fix: J-formulas denote fixed points -/

/-- The fixpoint law `◯χ* → χ*` from a J-derivation of `χ`, under the guards. -/
def fixD : ∀ {Θ : List String} {χ : Fm}, IsJ Θ χ → LC χ →
    LaxND2 (guards Θ) (.imp (.circ (rel χ)) (rel χ))
  | _, _, .var hs, _ =>
      .iden ⟨trivial, trivial⟩ (mem_map_of_mem (fun s => Fm.imp (.circ (.fvar s)) (.fvar s)) hs)
  | _, _, .top, _ =>
      .impIntro ⟨trivial, trivial⟩ (.impIntro trivial (.iden trivial (List.mem_cons_self ..)))
  | _, _, @IsJ.imp _ φ ψ h, hχ =>
      let d := fixD h hχ.2
      .impIntro ⟨lc_rel hχ.1, lc_rel hχ.2⟩ <| .impIntro (lc_rel hχ.1) <|
        .impElim ((d.weaken _).weaken _)
          (.laxElim (φ := .imp (rel φ) (rel ψ))
            (.iden ⟨lc_rel hχ.1, lc_rel hχ.2⟩ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            (.laxIntro (.impElim (.iden ⟨lc_rel hχ.1, lc_rel hχ.2⟩ (List.mem_cons_self ..))
              (.iden (lc_rel hχ.1) (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
  | _, _, @IsJ.and _ φ ψ h₁ h₂, hχ =>
      let d₁ := fixD h₁ hχ.1
      let d₂ := fixD h₂ hχ.2
      .impIntro ⟨lc_rel hχ.1, lc_rel hχ.2⟩ <|
        .andIntro
          (.impElim (d₁.weaken _)
            (.laxElim (φ := .and (rel φ) (rel ψ))
              (.iden ⟨lc_rel hχ.1, lc_rel hχ.2⟩ (List.mem_cons_self ..))
              (.laxIntro (.andElim1 (ψ := rel ψ)
                (.iden ⟨lc_rel hχ.1, lc_rel hχ.2⟩ (List.mem_cons_self ..))))))
          (.impElim (d₂.weaken _)
            (.laxElim (φ := .and (rel φ) (rel ψ))
              (.iden ⟨lc_rel hχ.1, lc_rel hχ.2⟩ (List.mem_cons_self ..))
              (.laxIntro (.andElim2 (φ := rel φ)
                (.iden ⟨lc_rel hχ.1, lc_rel hχ.2⟩ (List.mem_cons_self ..))))))
  | Θ, _, @IsJ.all _ ψ L h, hχ =>
      .impIntro (lcAt_rel 1 ψ hχ) <|
        .allIntro L (lcAt_rel 1 ψ hχ) fun s hs =>
          let d : LaxND2 (guards Θ)
              (.imp (.circ ((rel ψ).opn (.fvar s))) ((rel ψ).opn (.fvar s))) :=
            (rel_opn_fvar ψ s) ▸ fixD (h s hs) (lc_opn (.fvar s) trivial hχ)
          .impElim (d.weaken _)
            (.laxElim (φ := .all (rel ψ))
              (.iden (lcAt_rel 1 ψ hχ) (List.mem_cons_self ..))
              (.laxIntro (.allElim (χ := .fvar s) trivial
                (.iden (lcAt_rel 1 ψ hχ) (List.mem_cons_self ..)) rfl)))
  | Θ, _, @IsJ.allJ _ ψ L h, hχ =>
      .impIntro (lcAt_rel 0 (.allJ ψ) hχ) <|
        .allIntro L (lcAt_rel 0 (.allJ ψ) hχ) fun s hs =>
          let d : LaxND2 (.imp (.circ (.fvar s)) (.fvar s) :: guards Θ)
              (.imp (.circ ((rel ψ).opn (.fvar s))) ((rel ψ).opn (.fvar s))) :=
            (rel_opn_fvar ψ s) ▸ fixD (h s hs) (lc_opn (.fvar s) trivial hχ)
          show LaxND2 _ (.imp (.imp (.circ (.fvar s)) (.fvar s)) ((rel ψ).opn (.fvar s))) from
          .impIntro ⟨trivial, trivial⟩ <|
            .impElim (d.rename (consMono fun _ hx => List.mem_cons_of_mem _ hx))
              (.laxElim (φ := allNuc (rel ψ))
                (.iden (lcAt_rel 0 (.allJ ψ) hχ)
                  (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                (.laxIntro (.impElim
                  (.allElim (χ := .fvar s)
                    (θ := .imp (.imp (.circ (.fvar s)) (.fvar s)) ((rel ψ).opn (.fvar s)))
                    trivial (.iden (lcAt_rel 0 (.allJ ψ) hχ) (List.mem_cons_self ..)) rfl)
                  (.iden ⟨trivial, trivial⟩ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))

/-- **Fix.** -/
theorem fixOfIsJ : FixOfIsJ := fun _ _ h hχ => ⟨fixD h hχ⟩

/-! ## I₂: the guarded calculus into P2LL -/

/-- The translation of derivations under `(−)*`, with the declarations as guards. -/
def relD : ∀ {Θ : List String} {Γ : List Fm} {φ : Fm}, JND IsJ Θ Γ φ →
    LaxND2 (guards Θ ++ Γ.map rel) (rel φ)
  | _, _, _, .iden hφ h => .iden (lc_rel hφ) (List.mem_append_right _ (mem_map_of_mem rel h))
  | _, _, _, .falsoElim φ hφ p => .falsoElim (rel φ) (lc_rel hφ) (relD p)
  | _, _, _, .impIntro hφ p => .impIntro (lc_rel hφ) ((relD p).rename fun _ => mem_append_cons)
  | _, _, _, .impElim p₁ p₂ => .impElim (relD p₁) (relD p₂)
  | _, _, _, .andIntro p₁ p₂ => .andIntro (relD p₁) (relD p₂)
  | _, _, _, .andElim1 p => .andElim1 (relD p)
  | _, _, _, .andElim2 p => .andElim2 (relD p)
  | _, _, _, .orIntro1 hψ p => .orIntro1 (lc_rel hψ) (relD p)
  | _, _, _, .orIntro2 hφ p => .orIntro2 (lc_rel hφ) (relD p)
  | _, _, _, .orElim p₀ p₁ p₂ =>
      .orElim (relD p₀) ((relD p₁).rename fun _ => mem_append_cons)
        ((relD p₂).rename fun _ => mem_append_cons)
  | _, _, _, @JND.allIntro _ _ _ ψ L hψ p =>
      .allIntro L (lcAt_rel 1 ψ hψ) fun s hs => (rel_opn_fvar ψ s) ▸ relD (p s hs)
  | _, _, _, @JND.allElim _ _ _ ψ _ _ hχ p e =>
      .allElim (lc_rel hχ) (relD p) ((congrArg rel e).trans (rel_opn ψ _))
  | _, _, _, @JND.allJIntro _ _ _ ψ L hψ p =>
      .allIntro L (lcAt_rel 0 (.allJ ψ) hψ) fun s hs =>
        show LaxND2 _ (.imp (.imp (.circ (.fvar s)) (.fvar s)) ((rel ψ).opn (.fvar s))) from
        .impIntro ⟨trivial, trivial⟩ ((rel_opn_fvar ψ s) ▸ relD (p s hs))
  | _, _, _, @JND.allJElim _ _ _ ψ χ θ hχ hJ p e =>
      .impElim
        (.allElim (χ := rel χ) (θ := .imp (.imp (.circ (rel χ)) (rel χ)) (rel θ)) (lc_rel hχ)
          (relD p) (by subst e; exact congrArg (Fm.imp (.imp (.circ (rel χ)) (rel χ))) (rel_opn ψ χ)))
        ((fixD hJ hχ).rename fun _ hx => List.mem_append_left _ hx)

/-- **I₂.** -/
theorem interpToP2LL : InterpToP2LL := fun _ _ _ p => ⟨relD p⟩

end P2LL

/-! ## Pins (upper bounds).  The three derivation translations were first run
at `[]` and failed with `propext, Quot.sound` (2026-10-24): `Quot.sound` from
`List.mem_map`, removed by `mem_map_of_mem` above; `propext` from
`Fm.lc_opn` through `LaxND2.lc`, `JND.lc` and the binder cases.  See
`wip/p2ll-STATUS.md`. -/

#axioms_within P2LL.mem_map_of_mem []
#axioms_within P2LL.mem_append_cons []
#axioms_within P2LL.toJD [propext]
#axioms_within P2LL.interpToJ [propext]
#axioms_within P2LL.fixD [propext]
#axioms_within P2LL.fixOfIsJ [propext]
#axioms_within P2LL.relD [propext]
#axioms_within P2LL.interpToP2LL [propext]
