import F0.Names
import wip.rnEmbed

/-!
# Gate (outside the F0 library): `F0.t` agrees with the catalogue's `rnSub`

2026-10-22.  `F0/Names.lean` transcribes (as `F0.t`) `PLLND.RNEmbed.rnSub`
(`wip/rnEmbed.lean`) so that the F0 library stays free of `wip/`.  This
file, which may import `wip/`, checks the transcription for `n ≤ 12` (the search domain of `t`).
It is not part of any library; check it with

    lake build wip.rnEmbed F0.Names
    lake env lean tools/F0/RNSourceGate.lean
-/

theorem F0.RNSourceGate.rnSub_agree :
    (List.range 13).all (fun n => F0.t n == PLLND.RNEmbed.rnSub n) = true := by decide

#axioms_within F0.RNSourceGate.rnSub_agree [propext, Quot.sound]
