/-
# `Meta.Tactics` — the repository's Mathlib tactic bundle

**Why this exists.**  Until 2026-09-03 `FRJ/Basic.lean` carried a blanket
`import Mathlib` and `LaxLogic/PLLFormula.lean` an `import Mathlib.Tactic`,
so every module downstream — the whole FRJ development, the engine, and
therefore `lake exe pll` — inherited the entire library.  A cold clone
running the decider built `Mathlib.CategoryTheory`, `Mathlib.MeasureTheory`,
`Mathlib.NumberTheory` and the rest before printing a verdict (Matthew,
2026-09-03).  Neither foundation module needed any of it: `FRJ.Basic`
compiles against Batteries alone (its `Finset` mentions are all comments
explaining that Finset was AVOIDED, `Classical.choice` being the reason),
and `PLLFormula`'s only Mathlib use was a legacy `Set`-valued subformula
island, now `LaxLogic/PLLSubformulaSet.lean`.

**What this is.**  The tactics the PROOFS in this repository actually use,
in one auditable list, so that a module needing them says so explicitly
instead of inheriting them from a foundation module.  Definitions,
engines and executables should NOT import this: the runtime closure of
`lake exe pll` is meant to stay Mathlib-free (the def/proof split of
`docs/decider-outputs-design.md`).

Add a line here when a proof needs a new tactic, and say which tactic in
the comment — the point of the file is that the list is readable.
-/

import Aesop                           -- aesop (its own package, not Mathlib)
import Mathlib.Tactic.ByContra          -- by_contra
import Mathlib.Tactic.Cases             -- rcases-family extensions
import Mathlib.Tactic.Contrapose        -- contrapose
import Mathlib.Tactic.Convert           -- convert
import Mathlib.Tactic.Ext               -- ext
import Mathlib.Tactic.FinCases          -- fin_cases
import Mathlib.Tactic.Lemma             -- the `lemma` keyword
import Mathlib.Tactic.Linarith          -- linarith
import Mathlib.Tactic.NormNum           -- norm_num
import Mathlib.Tactic.Push              -- push_neg
import Mathlib.Tactic.Relation.Rfl      -- rfl extensions
import Mathlib.Tactic.Set               -- set … with …
import Mathlib.Tactic.SimpRw            -- simp_rw
import Mathlib.Tactic.SplitIfs          -- split_ifs
import Mathlib.Tactic.Tauto             -- tauto
import Mathlib.Tactic.Use               -- use
import Mathlib.Logic.Relation           -- Relation.ReflTransGen (Step.lean)
