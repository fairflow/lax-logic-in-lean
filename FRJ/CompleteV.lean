/-
# Completeness of the repaired calculus — the transfer baseline

Every completeness theorem of the PAPER family transfers to the repaired
calculus by post-composition with `provableV_of_provable` (paper ⊆
repaired, `FRJ/CalculusV.lean`).  These are the FREE corollaries: they
exploit nothing of the RefAt relaxation, and in particular they cannot
close the #80/#81-shaped gaps — the frames those live on are exactly the
ones `Endpoints` excludes.  The repair-exploiting completeness of `FRJV`
beyond endpoint-seeing frames is the OPEN campaign target
(`docs/refat-plan.md`, review section 2026-08-26); per the standing rule
it gets NO declaration here while open.
-/
import FRJ.Saturate
import FRJ.Erase
import FRJ.CalculusV

namespace FRJ

/-- Baseline: `FRJV` is complete on endpoint-seeing frames — every modal
cone contains a `≤`-maximal world.  Free transfer of
`completeness_of_endpoints`. -/
theorem completenessV_of_endpoints {K : Kripke} {G : Form} (hep : K.Endpoints)
    (hK : ¬ K.valid G) : ProvableV G :=
  provableV_of_provable (completeness_of_endpoints hep hK)

/-- Baseline: `FRJV` is complete on cone-grounded frames. -/
theorem completenessV_of_coneGrounded {K : Kripke} {G : Form}
    (hg : K.ConeGrounded) (hK : ¬ K.valid G) : ProvableV G :=
  provableV_of_provable (completeness_of_coneGrounded hg hK)

/-- Baseline: `FRJV` is complete on discrete frames. -/
theorem completenessV_of_discrete {K : Kripke} {G : Form}
    (hdisc : ∀ a u : K.W, K.le a u → u = a)
    (hK : ¬ K.valid G) : ProvableV G :=
  provableV_of_provable (completeness_of_discrete hdisc hK)

/-- Baseline: `FRJV` is complete for `◯`-free goals on infallible
frames. -/
theorem completenessV_via_closure {G : Form}
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (K : Kripke) (hinf : K.Infallible) (hK : ¬ K.valid G) : ProvableV G :=
  provableV_of_provable (completeness_via_closure hcf K hinf hK)

/-- Baseline: the supply-conditional completeness transfers too (the
supplies feed the PAPER promise joins, unchanged in `FRJV`). -/
theorem completenessV_of_supply {K : Kripke} {G : Form}
    (psup : PledgeSupply K G)
    (hsup : CircSupply K G)
    (hK : ¬ K.valid G) : ProvableV G :=
  provableV_of_provable (completeness_of_supply psup hsup hK)

end FRJ
