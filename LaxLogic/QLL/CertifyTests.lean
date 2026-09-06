/-
# `LaxLogic.QLL.CertifyTests` — the checker's output is a derivation

The point of this file is mostly in the *types*.  `d_identity` below has type
`qd[⊢ λu. u : ⊤ ⊃ ⊤]` and its value comes out of `certify`.
Nothing proves that the checker is sound; the type says it.
-/
import LaxLogic.QLL.Certify
import LaxLogic.QLL.Judgement

namespace LaxLogic.QLL.CertifyTests

open Form Pf LaxLogic.QLL.Surface

/-! ## Accepted, with the derivation extracted

`Option.get` on a proof that the check succeeded.  If `certify` returned
something that was not a derivation of the stated formula, these would not
typecheck. -/

/--
The certificate for `⊢ λu.u : ⊤ ⊃ ⊤`, straight out of the checker.

The *type* is the claim: had `certify` returned anything that was not a
derivation of that formula from that context, this would not elaborate.  The
`#guard` then says the checker actually succeeded rather than returning `none`.
-/
def d_identity : Option qd[⊢ λu. u : ⊤ ⊃ ⊤] :=
  (certify [] qp[λu. u] qf[⊤ ⊃ ⊤]).toOption.map Prod.fst

#guard d_identity.isSome

/-! ## Accept / reject, as data -/

private def ok {α : Type} (r : Except Err (α × List (Pf × Form))) : Bool := r.toOption.isSome
private def obs {α : Type} (r : Except Err (α × List (Pf × Form))) : List (Pf × Form) :=
  match r with | .ok (_, o) => o | .error _ => []

#guard ok (certify [] qp[λu. u] qf[⊤ ⊃ ⊤])
#guard ok (certify [] qp[val∀ *] qf[◯∀ ⊤])
#guard ok (certify [] qp[⟨λu. u | x⟩]
             qf[∀x. P(x) ⊃ P(x)])
#guard ok (certify [(qp[p], qf[◯∃ ⊤])]
             qp[let∃ u ⇐ p in val∃ u] qf[◯∃ ⊤])

/-! ## Obligations survive a successful certification -/

#guard obs (certify [(pair star star, pred "C" []), (qp[z], qf[⊤])] qp[z] top)
        == [(pair star star, pred "C" [])]

/-! ## Gates — each watched failing -/

#guard ! ok (certify [] qp[λu. u] qf[⊤ ⊃ ⊥])
#guard ! ok (certify [] qp[val∀ *] qf[◯∃ ⊤])
#guard ! ok (certify [] qp[π₁ *] top)
#guard ! ok (certify [] (bvar 3) top)

/-! ## Refused β-redexes

Derivable, and refused — the documented limit of bidirectional checking of
Curry-style terms.  An elimination whose subject is a non-inferable
introduction form cannot be inspected.  Never a mis-acceptance: the return type
forbids that. -/

-- (λu.u) * : ⊤
#guard ! ok (certify [] qp[(λu. u) *] top)
-- case (ι_c *) of [ι_x(z) → z] : ⊤
#guard ! ok (certify [] qp[case ι[c] * of [ι[x](u) → u]] top)
-- but π₁(*, *) IS accepted, because `pair` infers — so the limit is precisely
-- "the subject must infer", not "no redexes"
#guard ok (certify [] qp[π₁ (*, *)] top)
-- and π_c(⟨* | x⟩) is now accepted too: inference for ∀ decides local
-- closedness rather than refusing outright
#guard ok (certify [] qp[π[c] ⟨* | x⟩] top)

end LaxLogic.QLL.CertifyTests
