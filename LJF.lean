/-
# LJF and LJF◯ — the focused sequent calculi

Split out of `LaxLogic/` on 2026-08-22 to modularise the development.
The dependency runs ONE WAY: `LJF` imports `LaxLogic` modules (formulas,
natural deduction, the constraint semantics); `LaxLogic` no longer
imports any `LJF` module.

* `LJF.Base`, `LJF.Complete` — LJF for IPC.
* `LJF.O*` — LJF◯, the lax extension: `OCore`, `OUniverse`, `ORows`,
  `OHeight`, `OFuel`, `O`, `OSearch`, `OBridge`, `OAudit`.

`LJF.OBridge` carries `bridge_iff` and `FocalizationPLL`, which are what
make an LJF◯ answer an answer about PLL at all.
-/
import LJF.Base
import LJF.Complete
import LJF.OCore
import LJF.OUniverse
import LJF.ORows
import LJF.OHeight
import LJF.OFuel
import LJF.O
import LJF.OSearch
import LJF.OBridge
import LJF.OAudit
