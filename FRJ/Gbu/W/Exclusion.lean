/-
# The exclusion half of the Gbu◯ / FRJW duality

Both directions of mutual exclusion, free from the two banked soundness
results (`pll_of_provableGbuC`, `soundnessW`) — a Gbu◯ proof and an
FRJW disproof of the same goal cannot coexist, since one forces
PLL-validity and the other refutes it.

The other half of the duality — JOINT EXHAUSTIVENESS, no goal escapes
both — is FRJW completeness under another name, and is OPEN.  Its
constructive form is the dichotomy

    decideGbuW : ∀ G, ProvableGbuC G ⊕ DisprovableW G

(the W-successor of the stood-down W5/W6 database route); no
declaration for it exists, per the open-status rule.
-/
import FRJ.Gbu.Circ
import FRJ.SoundW

namespace FRJ.Gbu.LJFT

open FRJ

/-- A Gbu◯ proof of `G` excludes an FRJW disproof of `G`. -/
theorem not_disprovableW_of_provableGbuC {G : Form}
    (h : ProvableGbuC G) : ¬ DisprovableW G :=
  fun hd => FRJ.soundnessW hd (pll_of_provableGbuC h)

/-- An FRJW disproof of `G` excludes a Gbu◯ proof of `G`. -/
theorem not_provableGbuC_of_disprovableW {G : Form}
    (h : DisprovableW G) : ¬ ProvableGbuC G :=
  fun hp => FRJ.soundnessW h (pll_of_provableGbuC hp)

/--
info: 'FRJ.Gbu.LJFT.not_disprovableW_of_provableGbuC' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_disprovableW_of_provableGbuC

/--
info: 'FRJ.Gbu.LJFT.not_provableGbuC_of_disprovableW' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_provableGbuC_of_disprovableW

end FRJ.Gbu.LJFT
