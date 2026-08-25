/-
BiLax round 2 — the pipeline, end to end.

A countermodel is supplied as PLAIN FINITE DATA (`FinBranch`), the
saturation certificate is produced by COMPUTATION (`by decide`), and
the conclusion is a KERNEL-CHECKED non-derivability theorem.  Nothing
between the searcher and the kernel needs to be trusted.

Axiom profile of the results below: `[propext, Quot.sound]` — no
choice, no `native_decide`, no `sorry`.
-/
import BiLax.Check

namespace BiLax

/-- The branch refuting `¬◯⊥`, as a searcher would emit it:
worlds `0 ≤ 1`, `1` fallible, `Rc` pointing at the top. -/
def negOBotBranch : FinBranch where
  n := 2
  riB x y := decide (x.val ≤ y.val)
  rmB x y := decide (x.val ≤ y.val)
  rcB _ y := decide (y.val = 1)
  falB x := decide (x.val = 1)
  LL x := if x.val = 0 then [emb (.somehow .falsePLL)] else [.bot]
  RR x := if x.val = 0 then
      [emb (.ifThen (.somehow .falsePLL) .falsePLL), .bot] else []

/-- The saturation certificate, by computation. -/
theorem negOBotBranch_ok : negOBotBranch.checkB = true := by decide

/-- **`⊬ ¬◯⊥`, via the pipeline.** -/
theorem pipeline_negOBot :
    ¬ Nonempty (PLLND.LaxND [] (.ifThen (.somehow .falsePLL) .falsePLL)) :=
  negOBotBranch.not_laxND_of_check negOBotBranch_ok (0 : Fin 2)
    (by simp) (by decide)

/-- The branch refuting `◯p ⊢ p` — no fallible world needed. -/
def boxpBranch : FinBranch where
  n := 2
  riB x y := decide (x.val ≤ y.val)
  rmB x y := decide (x.val ≤ y.val)
  rcB _ y := decide (y.val = 1)
  falB _ := false
  LL x := if x.val = 0 then [emb (.somehow (.prop "p"))] else [emb (.prop "p")]
  RR x := if x.val = 0 then [emb (.prop "p")] else []

theorem boxpBranch_ok : boxpBranch.checkB = true := by decide

/-- **`◯p ⊬ p`, via the pipeline.** -/
theorem pipeline_boxp :
    ¬ Nonempty (PLLND.LaxND [.somehow (.prop "p")] (.prop "p")) :=
  boxpBranch.not_laxND_of_check boxpBranch_ok (0 : Fin 2)
    (by
      intro ψ hψ
      simp only [List.mem_singleton] at hψ
      subst hψ
      decide)
    (by decide)

/-! ## Pins -/

/--
info: 'BiLax.pipeline_negOBot' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms pipeline_negOBot

/--
info: 'BiLax.pipeline_boxp' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms pipeline_boxp

end BiLax
