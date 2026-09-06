/-
# `LaxLogic.QLL.CertifyTests` — the checker's output is a derivation

The point of this file is mostly in the *types*.  `d_identity` below has type
`Derives (lam (bvar 0)) [] (imp ⊤ ⊤)` and its value comes out of `certify`.
Nothing proves that the checker is sound; the type says it.
-/
import LaxLogic.QLL.Certify

namespace LaxLogic.QLL.CertifyTests

open Form Pf

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
def d_identity : Option (Derives (lam (bvar 0)) [] (imp top top)) :=
  (certify [] (lam (bvar 0)) (imp top top)).toOption.map Prod.fst

#guard d_identity.isSome

/-! ## Accept / reject, as data -/

private def ok {α : Type} (r : Except Err (α × List (Pf × Form))) : Bool := r.toOption.isSome
private def obs {α : Type} (r : Except Err (α × List (Pf × Form))) : List (Pf × Form) :=
  match r with | .ok (_, o) => o | .error _ => []

#guard ok (certify [] (lam (bvar 0)) (imp top top))
#guard ok (certify [] (val Q.all star) (circ Q.all top))
#guard ok (certify [] (gen (lam (bvar 0)))
             (forall_ (imp (pred "P" [Tm.bvar 0]) (pred "P" [Tm.bvar 0]))))
#guard ok (certify [(fvar "p", circ Q.ex top)]
             (letQ Q.ex (fvar "p") (val Q.ex (bvar 0))) (circ Q.ex top))

/-! ## Obligations survive a successful certification -/

#guard obs (certify [(pair star star, pred "C" []), (fvar "z", top)] (fvar "z") top)
        == [(pair star star, pred "C" [])]

/-! ## Gates — each watched failing -/

#guard ! ok (certify [] (lam (bvar 0)) (imp top bot))
#guard ! ok (certify [] (val Q.all star) (circ Q.ex top))
#guard ! ok (certify [] (fst star) top)
#guard ! ok (certify [] (bvar 3) top)

-- The documented restriction: `⟨p | x⟩` is checkable but not inferable, so a
-- type-level β-redex is reported rather than accepted.
#guard ! ok (certify [] (inst (Tm.fvar "c") (gen star)) top)

end LaxLogic.QLL.CertifyTests
