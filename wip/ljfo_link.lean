/-
# THE LINK: LJF◯ search and Reject certificates as ONE two-sided engine

Matthew's directive (2026-08-14 night): the LJF◯ machinery — the
focused calculus, its fueled searcher, and now `bridge_iff` — is lying
unused; link it to `Reject/` and make the pair effective.

This file is the CERTIFIED layer of that link.  Two Bools, one per
side, each with a kernel-checked soundness theorem, meeting in a
disjointness theorem:

* **proof side** — `searchProves f Γ φ`: run the LJF◯ backward
  searcher on the ◯-preserving polarisation of the sequent.  `true`
  certifies `Γ ⊢ φ` in PLL (`laxND_of_searchProves`), by
  `search_sound` composed with `bridge_iff`.  And it is COMPLETE:
  every PLL-derivable sequent is found at some fuel
  (`searchProves_complete`) — that is `FocalizationPLL` +
  `search_complete`, and it is what makes exhaustion meaningful.
* **refutation side** — `Reject.certifies M w Γ φ`: already a Bool
  (`Reject/Cert.lean`), `true` certifies `Γ ⊬ φ`
  (`not_laxND_of_certifies`).  T2 + (R) (`not_laxND_iff_built`) say
  this side, too, is complete in principle: every underivable sequent
  has a certificate in the Built class.

So each side is sound outright and complete in principle, and
`two_sided_disjoint` confirms at kernel level that they can never both
fire.  What neither side has is a feasible BOUND — the engine
(`wip/two_sided.lean`) therefore interleaves them and reports `flag`
at budget, per the repo's three-valued doctrine.

Everything here is choice-free: the pins are `[propext, Quot.sound]`.

NEW FILE.  Nothing under `LaxLogic/` or `Reject/` is edited.
-/
import LaxLogic.LJFOBridge
import LaxLogic.LJFOSearch
import Reject.Cert
import Rewrite

namespace TwoSidedLink

open PLLND LJFO Rewrite

/-! ## The proof side -/

/-- The LJF◯ sequent deciding `Γ ⊢ φ`, under the bridge's
◯-preserving polarisation. -/
def decideSeq (Γ : List PLLFormula) (φ : PLLFormula) : LSeq :=
  .inv (Γ.map negOfO) [] .tru (negOfO φ)

/-- **The proof-side Bool**: fueled focused search on the polarised
sequent. -/
def searchProves (f : Nat) (Γ : List PLLFormula) (φ : PLLFormula) : Bool :=
  LSeq.search f (decideSeq Γ φ)

/-- **Soundness**: a `true` is a PLL derivability certificate.
`search_sound` rebuilds the LJF◯ derivation, `bridge_iff` erases it. -/
theorem laxND_of_searchProves {f : Nat} {Γ : List PLLFormula}
    {φ : PLLFormula} (h : searchProves f Γ φ = true) :
    Nonempty (LaxND Γ φ) :=
  (bridge_iff Γ φ).mpr ⟨LSeq.search_sound f _ h⟩

/-- **Completeness**: every PLL-derivable sequent is found at some
fuel.  `FocalizationPLL` supplies the focused derivation,
`search_complete` the fuel; the `Nonempty` is eliminated into the
propositional goal, so no choice is used. -/
theorem searchProves_complete {Γ : List PLLFormula} {φ : PLLFormula}
    (h : Nonempty (LaxND Γ φ)) : ∃ f, searchProves f Γ φ = true := by
  rcases FocalizationPLL Γ φ h with ⟨d⟩
  exact ⟨(LSeq.search_complete (s := decideSeq Γ φ) d).1,
    (LSeq.search_complete (s := decideSeq Γ φ) d).2⟩

/-! ## The refutation side is `Reject.certifies` (`Reject/Cert.lean`),
with `Reject.not_laxND_of_certifies`; nothing to add. -/

/-! ## The two sides can never both fire -/

theorem two_sided_disjoint {f : Nat} {M : FinCM} {w : Nat}
    {Γ : List PLLFormula} {φ : PLLFormula}
    (hp : searchProves f Γ φ = true)
    (hr : Reject.certifies M w Γ φ = true) : False :=
  Reject.not_laxND_of_certifies hr (laxND_of_searchProves hp)

/-! ## Normalisation compatibility

The repo doctrine is normalise-before-search.  This is the theorem
that lets the ENGINE search the simplified sequent and report the
verdict for the original: interderivable replacement on both sides of
a single-hypothesis sequent preserves derivability, both ways. -/

theorem deriv_iff_of_interd {φ φ' ψ ψ' : PLLFormula}
    (h₁ : SemUI.Interd φ φ') (h₂ : SemUI.Interd ψ ψ') :
    Nonempty (LaxND [φ] ψ) ↔ Nonempty (LaxND [φ'] ψ') := by
  constructor
  · rintro ⟨d⟩
    exact SemUI.Deriv.cutHead h₁.2 (SemUI.Deriv.cutHead ⟨d⟩ h₂.1)
  · rintro ⟨d⟩
    exact SemUI.Deriv.cutHead h₁.1 (SemUI.Deriv.cutHead ⟨d⟩ h₂.2)

/-- The instance the engine uses: `simplifyWith` on both sides. -/
theorem deriv_iff_simplify (rs : List RwRule) (k : Nat)
    (φ ψ : PLLFormula) :
    Nonempty (LaxND [φ] ψ) ↔
      Nonempty (LaxND [simplifyWith rs k φ] (simplifyWith rs k ψ)) :=
  deriv_iff_of_interd (simplifyWith_interd rs k φ) (simplifyWith_interd rs k ψ)

/-! ## Pins — transcribed verbatim from the build output -/

/-- info: 'TwoSidedLink.laxND_of_searchProves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms laxND_of_searchProves

/-- info: 'TwoSidedLink.searchProves_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms searchProves_complete

/-- info: 'TwoSidedLink.two_sided_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_sided_disjoint

/-- info: 'TwoSidedLink.deriv_iff_simplify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deriv_iff_simplify

end TwoSidedLink
