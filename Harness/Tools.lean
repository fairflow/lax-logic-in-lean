import Harness.Statements
import LaxLogic.PLL.ND.Theorems
import LaxLogic.PLL.Search.Search
import LaxLogic.PLL.SubTab.Engine
import CertifyAdoption.CheckDeriv

/-!
# The decider's adapters: `fincm`, `ljfo`, and the copy of `enum`

2026-10-27, F0 re-implementation plan step 4
(`docs/engine-adoption-statements.md` §2.2, §2.4, §3 and §9; status in
`docs/f0-step4-STATUS.md`).  The statements of `Harness/Statements.lean`,
proved here as instances of existing lemmas, and the tools built on them:

* `fincmNo : Certifier PLLFormula (FinCM × Nat) (fun φ => Holds φ → False)`
  and the disprover `fincmDisprover`;
* `ljfoYes : Certifier PLLFormula DerivTree Holds` and the prover
  `ljfoProver`;
* `enumDisprover`, a verbatim copy of the one in
  `tools/SubTab/Settings.lean`, which cannot be imported beside
  `Harness/Settings.lean` because both declare `Harness.tools`.

`Holds` is `PLLND.SubTab.Holds φ := Nonempty ([] ⊢ φ)` throughout (M1, M9).
Both certificates are Boolean-checked data.  The producers are UNTRUSTED
(`partial` underneath): a wrong proposal can only be REJECTED by its
certifier, never give a wrong answer.

The project's `Harness.config` (read by the lints) is the one declared in
`CertifyAdoption.lean`, imported through `CertifyAdoption.CheckDeriv`; it is
not moved, since no environment holds a second one.
-/

open PLLND Certify

namespace PLLDecider

/-! ## The statements, proved -/

/-- `FincmNoSound`: `FinCM.not_provable_of_check` at the empty context. -/
theorem fincmNo_sound : FincmNoSound :=
  fun _ _ _ h => FinCM.not_provable_of_check h

/-- `LjfoYesSound`: `LJFO.laxND_of_checkDeriv` at the empty context. -/
theorem ljfoYes_sound : LjfoYesSound :=
  fun _ _ h => LJFO.laxND_of_checkDeriv h

/-- `HoldsImpIff`: the deduction theorem at the empty context. -/
theorem holds_imp_iff : HoldsImpIff :=
  fun _ _ => deduction_iff

/-! ## The certifiers -/

/-- **`fincm`**: a finite constraint model with a world, checked against
`⊢ φ` by `FinCM.checkB`. -/
def fincmNo : Certifier PLLFormula (FinCM × Nat) (fun φ => SubTab.Holds φ → False) where
  check φ c := FinCM.checkB c.1 c.2 [] φ
  sound φ c h := fincmNo_sound φ c.1 c.2 h

/-- **`ljfo`**: an LJF◯ derivation tree, checked by `checkDeriv` at the
goal `decideSeq [] φ`. -/
def ljfoYes : Certifier PLLFormula LJFO.DerivTree SubTab.Holds where
  check φ t := LJFO.checkDeriv (LJFO.decideSeq [] φ) t
  sound φ t h := ljfoYes_sound φ t h

/-! ## The producers (untrusted) and their budgets -/

/-- The closure cap of the `fincm` producer: `Search.Config.emitClosureCap`'s
default, fixed (it does not grow with the budget). -/
def fincmClosureCap : Nat := 12

/-- The `fincm` producer.  `CounterEmit.emit` on the normal form
`Search.nf φ` (a PLL equivalent), then `CounterEmit.simplify` against `φ`
itself; the certifier re-checks on `φ`, as `Search.settleWhy` does.

**Budget.**  `b` is the node budget of `emit`'s G4c pre-check, `200 · b`
visited sequents (200 000 at `b = 1000`, `Search.defaultFindBudget`): a
proof found, or a cut-off, gives `none`, so a raised budget can turn a
cut-off into a countermodel.  The budget does NOT bound the model
construction `CounterEmit.build`, which is exponential in the subformula
closure; that stage is bounded only by the fixed closure cap
`fincmClosureCap` (12): above it the producer gives `none` at every budget.
`simplify` is checker-gated deletion, polynomial in the model. -/
def fincmProduce (φ : PLLFormula) (b : Nat) : Option (FinCM × Nat) :=
  let φ' := Search.nf φ
  if (CounterEmit.closureOf [] φ').length ≤ fincmClosureCap then
    (CounterEmit.emit [] φ' (budget := some (200 * b))).map
      fun (M, w) => CounterEmit.simplify M w [] φ
  else none

/-- The `ljfo` producer: `emitTree` (iterative deepening over `LSeq.succs`,
`CertifyAdoption/CheckDeriv.lean`) at the goal `decideSeq [] φ`.

**Budget.**  `b / 25` is the depth bound of the iterative deepening (40 at
`b = 1000`, the depth the exemplars of `CheckDeriv.lean` were emitted at;
160 and 640 after one and two raises by 4).  The cost is exponential in the
depth on failing branches.  `none` (no tree within the bound) is never a
refutation. -/
def ljfoProduce (φ : PLLFormula) (b : Nat) : Option LJFO.DerivTree :=
  CertifyAdoption.CheckDeriv.emitTree (b / 25) (LJFO.decideSeq [] φ)

/-! ## The tools -/

/-- The disprover `fincm`. -/
def fincmDisprover : Disprover PLLFormula SubTab.Holds where
  name := "fincm"
  RCert := FinCM × Nat
  certifier := fincmNo
  produce := fincmProduce

/-- The prover `ljfo`. -/
def ljfoProver : Prover PLLFormula SubTab.Holds where
  name := "ljfo"
  Cert := LJFO.DerivTree
  certifier := ljfoYes
  produce := ljfoProduce

/-- The finite-model enumeration as a disprover: smallest-first models on
at most 6 worlds, at most `50 · budget` models, as `SubCM` tables (no
fallible world).  Copied verbatim from `tools/SubTab/Settings.lean`
(2026-10-15), which stays as it is (gate G5). -/
def enumDisprover : Disprover PLLFormula SubTab.Holds where
  name := "enum"
  RCert := SubTab.SubCM
  certifier := SubTab.no
  produce φ b := (PllFast.firstHitCap φ 6 (50 * b)).map
    fun m => PllFast.bmToSubCM m (PllFast.atomsL φ).eraseDups

end PLLDecider

/-! ## Axiom pins (each watched failing at a smaller list; `docs/f0-step4-STATUS.md`) -/

#axioms_within PLLDecider.fincmNo_sound [propext, Quot.sound]
#axioms_within PLLDecider.ljfoYes_sound [propext, Quot.sound]
#axioms_within PLLDecider.holds_imp_iff [propext]
#axioms_within PLLDecider.fincmNo [propext, Quot.sound]
#axioms_within PLLDecider.ljfoYes [propext, Quot.sound]
#axioms_within PLLDecider.fincmDisprover [propext, Quot.sound]
#axioms_within PLLDecider.ljfoProver [propext, Quot.sound]
#axioms_within PLLDecider.enumDisprover [propext, Quot.sound]

/-! ## Lean certify gates (R2, R3) -/

/-- info: R3 passes: the evaluation path of PLLDecider.fincmNo is structural -/
#guard_msgs in #certify_structural PLLDecider.fincmNo

/-- info: R2 passes: the property of PLLDecider.fincmNo mentions no budget -/
#guard_msgs in #certify_statement PLLDecider.fincmNo

/-- info: R3 passes: the evaluation path of PLLDecider.ljfoYes is structural -/
#guard_msgs in #certify_structural PLLDecider.ljfoYes

/-- info: R2 passes: the property of PLLDecider.ljfoYes mentions no budget -/
#guard_msgs in #certify_statement PLLDecider.ljfoYes
