/-
Copyright (c) 2026 Matthew Fairtlough. All rights reserved.
-/
import LaxLogic.QLL.Notation
import Mathlib.Order.Notation

/-!
# `LaxLogic.QLL.NotationOrder` — `⊥` and `⊤` for QLL formulas

Mathlib's `⊥` and `⊤`, scoped to `LaxLogic.QLL`: the formula `.bot`/`.top` where a
formula is expected, `Bot.bot`/`Top.top` everywhere else
(`LaxLogic/Util/Connectives.lean`).  A separate module because the QLL core does
not import Mathlib, and a second `⊥` syntax beside Mathlib's would make every `⊥`
ambiguous.  Printing uses `⊥`/`⊤` wherever this module is loaded.
-/

namespace LaxLogic.QLL

scoped macro_rules | `(⊥) => `(fm_bot%)
scoped macro_rules | `(⊤) => `(fm_top%)

end LaxLogic.QLL
