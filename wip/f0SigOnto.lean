import wip.f0SelfSim
import Meta.Audit

/-!
# `σ` is not onto `[t3, ⊤]`, and does not preserve covers

`σ = subBot t3` (`wip/f0SelfSim.lean`) is a faithful embedding of F0 into
`[t3, ⊤]` (`sig_reflects`, `sigN_faithful`).  Matthew's observation: `⊥ ⋖ t2`
(`cover_0_2`), while

    σ ⊥ = t3,    σ t2 = ◯t3 ↠ t3 = g1          (sig_t2, by rfl)

and `t5` lies strictly between them:

    t3 ⊢ t5,   t5 ⊬ t3,   t5 ⊢ g1,   g1 ⊬ t5      (t3_lt_t5_lt_g1)

**PROVED** (`sig_not_onto`): `t5 ∈ [t3, ⊤] ∖ σ(F0)`, so `σ` is not onto:

    ¬ ∃ y, atomFree y ∧ σ y ⊣⊢ t5.

From `σ y ⊣⊢ t5 ⊢ g1 = σ t2`, reflection gives `y ⊢ t2`; by
`low_trichotomy`, `y` is above `◯⊥` (then `◯⊥ ⊢ ¬◯⊥`, absurd), or `y ⊣⊢ ⊥`
(then `σ y ⊣⊢ t3`, against `t5 ⊬ t3`), or `y ⊣⊢ t2` (then `σ y ⊣⊢ g1`, against
`g1 ⊬ t5`).

**PROVED** (`sig_not_cover`): `⊥ ⋖ t2`, but `σ ⊥ = t3` is not covered by
`σ t2 = g1` (the witness `t5` sits strictly between).

**Pen remark (not mechanised).**  F0 is initial among Heyting algebras with a
nucleus, so `σ` is the only such homomorphism `F0 → [t3, ⊤]`; hence `[t3, ⊤]`
is not isomorphic to F0 in that structure.

**OPEN**: whether `[t3, ⊤] ≅ F0` as a bare poset.

The two non-trivial cells (`t5 ⊢ g1`, `g1 ⊬ t5`) are re-certified here by the
subframe tableau (`_out/gen8.lean`, untrusted producer; checked in the kernel);
`t3 ⊢ t5` is `∨`-introduction and `t5 ⊬ t3` is `nd_t5_t3`.  The explorer's
`F0/Order` cells are over the ρ-formulas, with no bridge lemma to
`rnSub`/`gap`, so they are not used.  Pins `[propext, Quot.sound]`.
-/

open PLLFormula

namespace PLLND
namespace F0
namespace SigOnto

open SemUI RNEmbed Sig
open PLLND.LaxInfinite (atomFree)

/-- `c1 = ◯t3`. -/
def c1F : PLLFormula := .somehow t3

/-- `g1 = c1 ↠ t3`. -/
def g1F : PLLFormula := .ifThen c1F t3

theorem g1F_eq : gap 1 = g1F := rfl

/-- **`σ t2 = g1`.** -/
theorem sig_t2 : sig (rnSub 2) = gap 1 := rfl

/-! ## The cells -/

theorem t5_le_g1F : Deriv [t5] g1F :=
  derivTab (.impR t5 g1F (.orL t3 t4 (.orL e ne (.impR c1F t3 (.orL e ne (.orL t3 t4 (.ax t3) (.ax t3)) (.impL e bot (.orL t3 t4 (.ax e) (.ax e)) .bot))) (.impL e bot (.impR c1F t3 (.impL e bot (.orL e ne (.orL t3 t4 (.ax e) (.ax e)) (.orL t3 t4 (.ax t3) (.impL t3 e (.ax t3) (.ax e)))) .bot)) .bot)) (.impL t3 e (.orR e ne (.impR c1F t3 (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.boxR bot (.impL t3 e (.orL t3 t4 (.orL e ne (.boxL bot .bot) (.impL e bot (.boxL t3 (.boxLoc bot (.ax t3))) .bot)) (.boxL t3 (.orL e ne (.boxL bot .bot) (.impL e bot (.boxLoc bot (.ax t3)) .bot)))) (.boxL bot .bot))))) (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e)))))) (.impR c1F t3 (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e)))))))
    (by decide +kernel)

-- g1_t5: countermodel, 8 worlds, refutes = true
def M_g1_t5 : SubTab.SubCM :=
  ⟨8, 0, [[true, true, true, true, true, true, true, true],
 [false, true, true, true, true, true, true, true],
 [false, false, true, false, false, false, false, false],
 [false, false, false, true, false, false, false, false],
 [false, false, false, false, true, true, false, false],
 [false, false, false, false, false, true, false, false],
 [false, false, false, false, false, false, true, true],
 [false, false, false, false, false, false, false, true]],
    [false, false, true, false, true, false, false, true],
    [[], [], [], [], [], [], [], []]⟩


theorem g1_not_le_t5 : [gap 1] ⊬ t5 := fun h =>
  SubTab.SubCM.refutes_sound (m := M_g1_t5) (by decide +kernel) (Deriv.impIntro h)

/-- **`t3 < t5 < g1`.** -/
theorem t3_lt_t5_lt_g1 :
    Deriv [rnSub 3] (rnSub 5) ∧ ([rnSub 5] ⊬ rnSub 3) ∧
      Deriv [rnSub 5] (gap 1) ∧ ([gap 1] ⊬ rnSub 5) :=
  ⟨Deriv.orIntro1 (Deriv.iden (.head _)), nd_t5_t3, t5_le_g1F, g1_not_le_t5⟩

/-! ## `σ` is not onto -/

/-- **`t5 ∉ σ(F0)`**: `σ` is not onto `[t3, ⊤]`. -/
theorem sig_not_onto : ¬ ∃ y : PLLFormula, atomFree y = true ∧ Interd (sig y) (rnSub 5) := by
  rintro ⟨y, hy, hi⟩
  obtain ⟨_, h53, h5g, hg5⟩ := t3_lt_t5_lt_g1
  have hyt2 : Deriv [y] (rnSub 2) :=
    sig_reflects_ctx (Deriv.cutHead hi.1 (h5g : Deriv [rnSub 5] (sig (rnSub 2))))
  rcases low_trichotomy y hy with hey | hyb | hyn
  · -- `◯⊥ ⊢ y ⊢ ¬◯⊥`
    exact nd_e_bot (Deriv.impElim (Deriv.cutHead hey hyt2) (Deriv.iden (.head _)))
  · -- `y ⊣⊢ ⊥`, so `σ y ⊢ t3`
    have hs : Deriv [sig y] (sig .falsePLL) :=
      subBot_deriv t3 (fun χ hχ => by rw [List.mem_singleton.mp hχ]; exact hy) rfl hyb.1
    exact h53 (Deriv.cutHead hi.2 hs)
  · -- `y ⊣⊢ ¬◯⊥`, so `g1 ⊢ σ y`
    have hs : Deriv [sig notOBot] (sig y) :=
      subBot_deriv t3 (fun χ hχ => by rw [List.mem_singleton.mp hχ]; rfl) hy hyn.2
    exact hg5 (Deriv.cutHead hs hi.1)

/-! ## `σ` does not preserve covers -/

/-- **`⊥ ⋖ t2`, but `σ ⊥ = t3` is not covered by `σ t2 = g1`.** -/
theorem sig_not_cover :
    Covers (rnSub 0) (rnSub 2) ∧ ¬ Covers (sig (rnSub 0)) (sig (rnSub 2)) := by
  refine ⟨cover_0_2, fun hc => ?_⟩
  obtain ⟨h35, h53, h5g, hg5⟩ := t3_lt_t5_lt_g1
  rcases hc.2.2 (rnSub 5) (rnSub_vf 5) h35 h5g with hi | hi
  · exact h53 hi.1
  · exact hg5 hi.2

end SigOnto
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.SigOnto.sig_t2 [propext, Quot.sound]
#axioms_within PLLND.F0.SigOnto.t5_le_g1F [propext, Quot.sound]
#axioms_within PLLND.F0.SigOnto.g1_not_le_t5 [propext, Quot.sound]
#axioms_within PLLND.F0.SigOnto.t3_lt_t5_lt_g1 [propext, Quot.sound]
#axioms_within PLLND.F0.SigOnto.sig_not_onto [propext, Quot.sound]
#axioms_within PLLND.F0.SigOnto.sig_not_cover [propext, Quot.sound]
