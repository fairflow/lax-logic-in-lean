import Mathlib

/-!
# Believers on small Heyting algebras, machine-computed (§3b-5)

A believer is a nucleus `j` — inflationary, idempotent, meet-preserving.  On a
finite `SemilatticeInf` this is a *decidable* predicate, so we enumerate the
believers on the 3-chain and exhibit sceptic / credulous / intermediate ones
side by side, kernel-checked by `decide`.

The larger enumerations (the 4-chain, the 2×2 Boolean algebra, and the two
five-element non-linear Heyting algebras, with the closed/open/neither
classification of every believer) are in `ExamplesClean.lean`, over bare
inductive carriers whose audits avoid both `native_decide` and the choice
that Mathlib's `Fin`/`Finset` vocabulary brings into statements.  The two
`native_decide` counts this file carried until 2026-11-01 (`chain4_card`,
`boolean22_card`) were replaced by the kernel-checked counts there.
-/

namespace BeliefLax

/-- `j` is a **nucleus** (believer): inflationary, idempotent, meet-preserving. -/
abbrev IsNucleusFun {H : Type*} [SemilatticeInf H] [Fintype H] [DecidableEq H]
    [DecidableLE H] (j : H → H) : Prop :=
  (∀ x, x ≤ j x) ∧ (∀ x, j (j x) = j x) ∧ (∀ x y, j (x ⊓ y) = j x ⊓ j y)

/-! ### The 3-element chain `Fin 3` (`⊥ < m < ⊤`): exactly four believers -/

/-- The 3-chain has exactly **four** nuclei. -/
theorem chain3_card :
    (Finset.univ.filter fun j : Fin 3 → Fin 3 => IsNucleusFun j).card = 4 := by decide

/-- Total **sceptic** `j = id` (`◯M ⟺ M`). -/
theorem chain3_sceptic : IsNucleusFun (id : Fin 3 → Fin 3) := by decide
/-- Totally **credulous** `j = fun _ => ⊤` (`◯M ⟺ ⊤`). -/
theorem chain3_credulous : IsNucleusFun (fun _ => (2 : Fin 3)) := by decide
/-- **Closed** (dogmatic) `c_m(x) = x ⊔ m`, i.e. `[0↦1, 1↦1, 2↦2]`. -/
theorem chain3_closed : IsNucleusFun (![1, 1, 2] : Fin 3 → Fin 3) := by decide
/-- **Open** (hypothetical) `u_m(x) = m ⇨ x`, i.e. `[0↦0, 1↦2, 2↦2]`. -/
theorem chain3_open : IsNucleusFun (![0, 2, 2] : Fin 3 → Fin 3) := by decide
/-- Open ≠ closed *already on the 3-chain* — constructive richness (cf. §3b-2). -/
theorem chain3_open_ne_closed : (![0, 2, 2] : Fin 3 → Fin 3) ≠ ![1, 1, 2] := by decide

end BeliefLax

#print axioms BeliefLax.chain3_card
#print axioms BeliefLax.chain3_open_ne_closed
