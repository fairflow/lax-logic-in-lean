/-
# Step 0 of the FRJV completeness campaign — CLOSED AS FOUND

The ◯-free control (docs/next-session.md, Matthew 2026-08-26) asked:
does the model-to-tree method prove completeness on the fragment where
Fiorentini–Ferrari's paper answer is known?  The record search answered
before any new proof was written: `FRJ/Minimal.lean` already mechanises
Theorem 6.2(i) — `completenessData` turns an infallible countermodel of
a ◯-free goal into an `FRJ(G)`-derivation, BY THE VERY RECURSION the
campaign planned (`minMod`, whose `MinModStmt` carries the `sub`/`cov`
invariants, and whose `.circ` case is the explicitly marked ◯-boundary).

This file adds the one missing composition: the paper calculus embeds in
the repaired one (`toVr`), so ◯-free completeness holds for FRJV too.
The full campaign is now exactly: extend `minMod` past its `.circ`
case — the ◯-delta (promise joins, join arity) and nothing else.
-/
import FRJ.Minimal
import FRJ.CalculusV

namespace FRJ

/-- **◯-free completeness of the REPAIRED calculus**: an infallible
countermodel of a ◯-free goal yields an FRJV derivation.  The fragment
control of the completeness campaign, closed by composition:
`completeness` (Theorem 6.2(i), `FRJ/Minimal.lean`) with the embedding
`provableV_of_provable`. -/
theorem completenessV_circFree {G : Form}
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (K : Kripke) (hinf : K.Infallible) (hK : ¬ K.valid G) :
    ProvableV G :=
  provableV_of_provable (completeness hcf K hinf hK)

/-- info: 'FRJ.completenessV_circFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completenessV_circFree

end FRJ
