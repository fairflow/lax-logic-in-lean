import CK.G4CK
import CK.Hilbert
import Meta.Rules
import Meta.Slime

/-!
# `CK.Audit` — the transcription checks

`#rules` prints each family as inference figures, to be compared line by
line with Figures 1 and 2 of arXiv:2602.16880v2; `#slime` reports computed
indices in conclusions (there must be none).
-/

#rules CK.G4CK
#rules CK.CKH
#slime CK.G4CK
#slime CK.CKH
#slime CK.Axiom
