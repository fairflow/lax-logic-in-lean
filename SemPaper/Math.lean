/-
The environment of the semantics paper, "Semantics and decision for PLL", for `{stmt}`
and the tables: the shared notation table (`PaperKit/Math.lean`; the
sections set `paperkit.notation` to `"sem"`) and the modules whose
declarations the paper displays.  All are library modules except
`wip.f0Nuclear`, where F0's Heyting algebra and nucleus are proved, and the
`wip.esakiaNuclear*` modules of the duality (v0.2).
-/
import PaperKit.Math
import LaxLogic.PLL.ND.NDCore
import LaxLogic.PLL.Semantics.Subframe
import LaxLogic.PLL.Semantics.Completeness
import LaxLogic.PLL.Semantics.FiniteModel
import LaxLogic.PLL.Semantics.Countermodel
import LaxLogic.PLL.SubTab.Translate
import LaxLogic.PLL.SubTab.Complete
import LaxLogic.PLL.SubTab.Engine
import LaxLogic.PLL.SubTab.Facts
import LaxLogic.PLL.SubTab.Gates
import LaxLogic.PLL.G4.G4HComp
import LaxLogic.PLL.G4.G4Dec
import LaxLogic.PLL.G4.G4Gap
import FRJ.Gbu.W.LaxND
import FRJ.Gbu.W.Saturate
import LaxLogic.ClosedFragmentLattice
import wip.f0Nuclear
import wip.esakiaNuclearFinProofs
import wip.esakiaNuclearFinProofs2
import wip.esakiaNuclearFinProofs3
import wip.esakiaNuclearBridgeProofs
import wip.esakiaNuclearGenProofs
import wip.esakiaNuclearCells
