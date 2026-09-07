/-
# `LaxLogic.QLL.Tests` — every gate in one target

`lake build LaxLogic.QLL.Tests` runs all of them.  They are `#guard`s and
`example`s, so a failure is a build failure; there is nothing to read.
-/
import LaxLogic.QLL.Smoke
import LaxLogic.QLL.SurfaceTests
import LaxLogic.QLL.JudgementTests
import LaxLogic.QLL.CertifyTests
import LaxLogic.QLL.InterpTests
import LaxLogic.QLL.DenoteTests
import LaxLogic.QLL.SoundTests
import LaxLogic.QLL.CLP
import LaxLogic.QLL.Weaken
