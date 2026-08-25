# Which result are you reproducing?

Soundness-and-completeness-against-a-semantics is one possibility among
several, and it is the one this workflow was built on — so assuming it is
the *only* one is the known blind spot. Decide the kind at Stage 1,
because each needs a different encoding and each fails differently.

## Soundness + completeness w.r.t. a semantics

*Shape.* A `Kripke`-like structure; `force`; the calculus as an indexed
inductive; soundness by induction on derivations; completeness by a model
construction, or via a second calculus.

*Watch for.* Completeness is nearly free against an over-permissive rule
table, so **screen soundness first**. If the semantics is the definition
of the logic (as in `IPL A := ∀ K, K.valid A`) then no proof system for
the base logic is needed anywhere — check, because it saves a lot.

*Make the model construction `Type`-valued.* Extracting a derivation from
an existence proof needs `choose` or `Nonempty.some`, both choice; and a
`Type`-valued construction is the searcher of Stage 4, for free.

## Cut elimination / structural admissibility

*Shape.* A termination measure carried by the statement, and rank/level
induction over it.

*Watch for.* The measure must be designed **before** the judgment is
typed: retrofitting one usually means re-indexing every constructor.
Contraction is where contraction-free calculi actually fail — the G4iLL
counterexample in this repo is exactly that.

## Termination / decidability

*Shape.* A well-founded order on sequents plus a decision procedure.

*Watch for.* The bound that makes the proof easy is routinely
unrunnable. Expect to prove decidability with an infeasible bound and
then, separately, extract a searcher that does not use it (this is Stage
4, and it is why Stages 3 and 4 are distinct).

## Interpolation / definability

*Shape.* A construction on derivations producing a formula, plus two
inclusions.

*Watch for.* The construction usually needs the calculus *focused* or
otherwise normalised first; budget that as its own adoption.

## Conservativity / faithfulness of a translation

*Shape.* Two calculi and an erasure or embedding, with a theorem each way.

*Watch for.* Green slime. If a constructor's index is a computed term
(`Γ ∪ Δ`, `Γ.erase A`) the transport lemmas cannot be stated cleanly.
Contexts as `List`, extended only by `φ :: Γ`, with identity taking
`φ ∈ Γ` so exchange/weakening/contraction are *admissible*, is the shape
that stays cast-free — `LaxLogic/PLLNDCore.lean` is the worked example.

## Focalisation / completeness of a search strategy

*Shape.* A focused calculus, plus completeness against the unfocused one.

*Watch for.* Polarity assignment is a statement-level decision with
real consequences; get it signed off. Flags threading through every
judgment multiply the cases.

## The subformula property

*Shape.* A closure operation and an invariant on derivations.

*Watch for.* It is usually needed as a *lemma for* something else, and
its statement is where the side conditions of the rule table become
visible. If it will not go through, suspect the rule table, not the
proof.
