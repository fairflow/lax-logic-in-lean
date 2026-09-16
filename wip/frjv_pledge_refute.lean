/-
# `PledgeSupply` refuted on a concrete model (2026-08-26)

The general defect is `FRJ.V.not_pledgeFam_of_circ_mem`
(`FRJ/SaturateV.lean`): a pledge family for `F` cannot exist where
`◯F ∈ Λ*_a`.  This file realises the configuration: on sepM (the
#80/#81 frame) at world 2 with `F = ⊥` and goal `G80`,

    ◯⊥ ∈ Λ*₂,   ⊥ ∈ sfR G80,   2 ⊮ ⊥,

so `PledgeSupply sepMK G80` is uninhabited and the supply-conditional
completeness route (`V.completeness_of_supply`) is VACUOUS here — on
the very frame of the two incompleteness witnesses.  The live route is
the transported-cov refinement (Lemma A′,
`docs/frjv-completeness-plan.md`).
-/
import FRJ.SaturateV
import FRJ.WitnessV
import FRJ.Search.Pin

open FRJ FRJ.Search

namespace FRJVPledgeRefute

/-- sepM as a `Tab`: order edges 01,02,03,04,12,13,23; modal 2R3;
world 3 fallible; empty valuation. -/
def sepM : Tab :=
  { n := 5, root := 0,
    leT := [[true,true,true,true,true],[false,true,true,true,false],
            [false,false,true,true,false],[false,false,false,true,false],
            [false,false,false,false,true]],
    rmT := [[true,false,false,false,false],[false,true,false,false,false],
            [false,false,true,true,false],[false,false,false,true,false],
            [false,false,false,false,true]],
    falT := [false,false,false,true,false],
    atomsT := [[],[],[],[],[]] }

theorem sepM_ok : sepM.okB = true := by decide
theorem sepM_root : sepM.root < sepM.n := by decide

def K : Kripke := sepM.toKripke sepM_ok sepM_root

/-- `PledgeSupply` is uninhabited on sepM at goal `G80`: apply the
supply at world 2, demand `⊥`, and hit the defect site `◯⊥ ∈ Λ*₂`. -/
theorem not_pledgeSupply_sepM_G80 : V.PledgeSupply K WitnessV.G80 → False :=
  fun psup =>
    V.not_pledgeFam_of_circ_mem (K := K) (a := ⟨2, by decide⟩)
      (F := .bot) (by decide)
      (psup ⟨2, by decide⟩ .bot (by decide) (by decide) (by decide))

/-- info: 'FRJVPledgeRefute.not_pledgeSupply_sepM_G80' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_pledgeSupply_sepM_G80

end FRJVPledgeRefute
