/-
# `LaxLogic.QLL.Check` — deciding whether a proof term proves a formula

A *type checker for derivations*, not a prover.  Given `Γ`, a proof term `p`
and a goal `M`, it decides whether `p` is a derivation of `M` from `Γ`.  Every
constructor of `Pf` names exactly one rule of Fig. 5, so the term drives the
recursion: there is no search and no backtracking.

## Why it is bidirectional

Fig. 5's proof terms are Curry-style — `λz.p` carries no annotation — so not
every term determines its own formula.  Four cannot be inferred:

| term | what is missing |
| :-- | :-- |
| `lam p`    | the antecedent `M` of `M ⊃ N` |
| `inl p`    | the other disjunct |
| `inr q`    | the other disjunct |
| `pack t p` | `M`, since recovering it from `M[t/x]` needs anti-unification |

Everything else *can* synthesise, but only when its subterms do: `gen (lam …)`
cannot, because the body is a `lam`.  So `check` handles every introduction
form in its own right and `infer` is the convenience, not the other way round.
Inference does dispose of the awkwardness noted in `Smoke.lean`: `circE`'s `M`
never has to be guessed, because inferring the head premise gives `◯_Q M`.

## What it returns

Not a `Bool`.  A successful check returns the derivation's **residual
obligations** — the non-variable entries of `Γ`, which by the reading recorded
on `Derivable.subst` are constraint terms supplied under a typing condition
whose refinement is still outstanding.  This is the same ledger the shallow
`LaxLogic.Obligation` keeps.

## No `Subst`

Fig. 5's `Subst` is not a rule of `Derivable` — see the note there.  It was
invisible in the proof term, so a term-driven checker could never have been
complete for a family containing it.  With it gone there is no fragment
caveat and no `isSubstFree` precondition anywhere: `check` is intended to be
complete for all of `Derivable`.

## Status of the harness theorems

Soundness is being proved in `Sound.lean`.  Completeness is **OPEN**, and no
declaration asserts it: it needs a renaming lemma, because `Derivable` admits
*any* fresh name while `check` picks one.
-/
import LaxLogic.QLL.Deriv

namespace LaxLogic.QLL

/-! ## Fresh names -/

/--
A name not occurring in `used`: every name in the list concatenated onto a
`"z"`, so the result is strictly longer than any of them.

Crude on purpose.  A counter would need a search to avoid collisions, and the
freshness property is wanted as a *theorem* for soundness, not as a runtime
check.
-/
def freshFor : List String → String
  | []      => "z"
  | s :: ss => s ++ freshFor ss

theorem freshFor_length : ∀ ss : List String,
    (freshFor ss).length = 1 + (ss.map String.length).sum
  | []      => rfl
  | s :: ss => by
      simp [freshFor, String.length_append, freshFor_length ss]
      omega

theorem length_le_sum : ∀ (ss : List String) (s : String), s ∈ ss →
    s.length ≤ (ss.map String.length).sum
  | [],      _, h => absurd h (by simp)
  | t :: ts, s, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · simp
      · have := length_le_sum ts s h'; simp; omega

/-- `freshFor` does what its name says.  Soundness will need this. -/
theorem freshFor_notMem (ss : List String) : freshFor ss ∉ ss := by
  intro h
  have h1 := length_le_sum ss _ h
  have h2 := freshFor_length ss
  omega

/-! ## Size is preserved by opening

The checker recurses on opened bodies, which are not structural subterms of the
binder, so termination is by `Pf.size`.  Opening with a *variable* leaves the
size alone; opening an individual leaves it alone for any term, since `openI`
touches only the embedded `Tm`s. -/

theorem size_openP (k : Nat) (z : String) (p : Pf) :
    (Pf.openP k (.fvar z) p).size = p.size := by
  induction p generalizing k with
  | bvar i => by_cases h : i = k <;> simp [Pf.openP, Pf.size, h]
  | _ => simp_all [Pf.openP, Pf.size]

theorem size_openI (k : Nat) (u : Tm) (p : Pf) :
    (Pf.openI k u p).size = p.size := by
  induction p generalizing k <;> simp_all [Pf.openI, Pf.size]

/-! ## Errors -/

/-- Why a check failed.  Carries enough to locate the fault. -/
inductive Err where
  /-- A de Bruijn index escaped its binder: the term is not locally closed. -/
  | looseIndex (i : Nat)
  /-- A free proof variable with no variable entry in the context. -/
  | unbound (x : String)
  /-- The inferred formula had the wrong shape for the rule the term names. -/
  | expected (shape : String) (got : Form)
  /-- Inferred and required formulas differ. -/
  | mismatch (required got : Form)
  /-- A term that cannot be inferred appeared where no goal was available. -/
  | notInferable (term : String)
  /-- `∃E`'s eigenvariable escaped into the conclusion. -/
  | escapes (a : String) (K : Form)
  /-- `◯E` mixed the two modalities, which Fig. 5 does not permit. -/
  | modalityClash (found required : Q)
  deriving Repr, DecidableEq

/-- The formula attached to a *variable* entry of the context. -/
def Ctx.lookup? (Γ : Ctx) (x : String) : Option Form :=
  match Γ with
  | []                 => none
  | (.fvar y, M) :: Γ' => if y = x then some M else Ctx.lookup? Γ' x
  | _ :: Γ'            => Ctx.lookup? Γ' x

/-! ## The checker -/

mutual

/--
Synthesise the formula a proof term proves, when the term determines it.

`Γ` is a recursive argument rather than a fixed parameter because the binder
rules extend it.  The measure is `2 * size`, one below `check`'s, so that
`check`'s deferral to `infer` at the *same* term still decreases.
-/
def infer : Ctx → Pf → Except Err Form
  | _, .bvar i       => .error (.looseIndex i)
  | Γ, .fvar x       => match Γ.lookup? x with
                        | some M => .ok M
                        | none   => .error (.unbound x)
  | _, .star         => .ok .top
  | Γ, .exf M p      => do let _ ← check Γ p .bot; pure M
  | Γ, .pair p q     => do let M ← infer Γ p; let N ← infer Γ q; pure (.and M N)
  | Γ, .fst r        => do match ← infer Γ r with
                           | .and M _ => pure M
                           | A        => .error (.expected "∧" A)
  | Γ, .snd r        => do match ← infer Γ r with
                           | .and _ N => pure N
                           | A        => .error (.expected "∧" A)
  | Γ, .app p q      => do match ← infer Γ p with
                           | .imp M N => do let _ ← check Γ q M; pure N
                           | A        => .error (.expected "⊃" A)
  | Γ, .val q p      => do let M ← infer Γ p; pure (.circ q M)
  | Γ, .inst t p     => do match ← infer Γ p with
                           | .forall_ M => pure (M.openAt 0 t)
                           | A          => .error (.expected "∀" A)
  | Γ, .letQ q p b   => do
      match ← infer Γ p with
      | .circ q' M =>
          if q' ≠ q then .error (.modalityClash q' q) else
          let z := freshFor (Ctx.fvP Γ ++ b.fvP)
          match ← infer ((Pf.fvar z, M) :: Γ) (b.openPWith z) with
          | .circ q'' N => if q'' = q then pure (.circ q N)
                           else .error (.modalityClash q'' q)
          | A           => .error (.expected "◯" A)
      | A => .error (.expected "◯" A)
  | Γ, .gen p        => do
      let a := freshFor (Ctx.fvI Γ ++ p.fvI)
      let A ← infer Γ (p.openIWith a)
      pure (.forall_ (Form.closeWith a A))
  | Γ, .caseOr r p q => do
      match ← infer Γ r with
      | .or M N =>
          let y := freshFor (Ctx.fvP Γ ++ p.fvP)
          let K ← infer ((Pf.fvar y, M) :: Γ) (p.openPWith y)
          let z := freshFor (Ctx.fvP Γ ++ q.fvP)
          let _ ← check ((Pf.fvar z, N) :: Γ) (q.openPWith z) K
          pure K
      | A => .error (.expected "∨" A)
  | Γ, .caseEx r p   => do
      match ← infer Γ r with
      | .exists_ M =>
          let a := freshFor (Ctx.fvI Γ ++ p.fvI ++ M.fv)
          let z := freshFor (Ctx.fvP Γ ++ p.fvP)
          let K ← infer ((Pf.fvar z, M.openWith a) :: Γ) ((p.openIWith a).openPWith z)
          if a ∈ K.fv then .error (.escapes a K) else pure K
      | A => .error (.expected "∃" A)
  | _, .lam _        => .error (.notInferable "λz.p")
  | _, .inl _        => .error (.notInferable "ι₁(p)")
  | _, .inr _        => .error (.notInferable "ι₂(q)")
  | _, .pack _ _     => .error (.notInferable "ι_t(p)")
  termination_by _ p => 2 * p.size
  decreasing_by
    all_goals try simp_wf
    all_goals try simp only [Pf.size, size_openP, size_openI, Pf.openPWith, Pf.openIWith]
    all_goals omega

/--
Check a proof term against a goal.

Every *introduction* form is handled here, because the goal supplies what a
Curry-style term omits.  Inferring them as well (in `infer`) is a convenience
that works only when their subterms happen to infer: `gen (lam …)` does not,
which is why `gen` needs a check-mode case and not merely an inference one.

The eliminations that produce their result from a branch — `caseOr`, `caseEx`,
`letQ` — are also handled here, checking the branches against the goal.  That
is strictly more complete than inferring one branch and comparing, and for
`caseEx` it makes the eigenvariable condition automatic: the fresh individual
is chosen away from the goal, so it cannot escape into it.
-/
def check : Ctx → Pf → Form → Except Err Unit
  | Γ, .lam p,        .imp M N    => do
      let z := freshFor (Ctx.fvP Γ ++ p.fvP)
      check ((Pf.fvar z, M) :: Γ) (p.openPWith z) N
  | _, .lam _,        A           => .error (.expected "⊃" A)
  | Γ, .inl p,        .or M _     => check Γ p M
  | _, .inl _,        A           => .error (.expected "∨" A)
  | Γ, .inr q,        .or _ N     => check Γ q N
  | _, .inr _,        A           => .error (.expected "∨" A)
  | Γ, .pack t p,     .exists_ M  => check Γ p (M.openAt 0 t)
  | _, .pack _ _,     A           => .error (.expected "∃" A)
  | Γ, .pair p q,     .and M N    => do let _ ← check Γ p M; check Γ q N
  | _, .pair _ _,     A           => .error (.expected "∧" A)
  | Γ, .gen p,        .forall_ M  =>
      let a := freshFor (Ctx.fvI Γ ++ p.fvI ++ M.fv)
      check Γ (p.openIWith a) (M.openWith a)
  | _, .gen _,        A           => .error (.expected "∀" A)
  | Γ, .val q p,      .circ q' M  =>
      if q = q' then check Γ p M else .error (.modalityClash q q')
  | _, .val _ _,      A           => .error (.expected "◯" A)
  | Γ, .caseOr r p q, K           => do
      match ← infer Γ r with
      | .or M N =>
          let y := freshFor (Ctx.fvP Γ ++ p.fvP)
          let _ ← check ((Pf.fvar y, M) :: Γ) (p.openPWith y) K
          let z := freshFor (Ctx.fvP Γ ++ q.fvP)
          check ((Pf.fvar z, N) :: Γ) (q.openPWith z) K
      | A => .error (.expected "∨" A)
  | Γ, .caseEx r p,   K           => do
      match ← infer Γ r with
      | .exists_ M =>
          let a := freshFor (Ctx.fvI Γ ++ p.fvI ++ M.fv ++ K.fv)
          let z := freshFor (Ctx.fvP Γ ++ p.fvP)
          check ((Pf.fvar z, M.openWith a) :: Γ) ((p.openIWith a).openPWith z) K
      | A => .error (.expected "∃" A)
  | Γ, .letQ q p b,   .circ q' N  =>
      if q ≠ q' then .error (.modalityClash q q') else do
      match ← infer Γ p with
      | .circ q'' M =>
          if q'' ≠ q then .error (.modalityClash q'' q) else
          let z := freshFor (Ctx.fvP Γ ++ b.fvP)
          check ((Pf.fvar z, M) :: Γ) (b.openPWith z) (.circ q N)
      | A => .error (.expected "◯" A)
  | _, .letQ _ _ _,   A           => .error (.expected "◯" A)
  | Γ, .exf M p,      K           =>
      if M = K then do let _ ← check Γ p .bot; pure () else .error (.mismatch K M)
  | Γ, p,             M           => do
      let A ← infer Γ p
      if A = M then pure () else .error (.mismatch M A)
  termination_by _ p _ => 2 * p.size + 1
  decreasing_by
    all_goals try simp_wf
    all_goals try simp only [Pf.size, size_openP, size_openI, Pf.openPWith, Pf.openIWith]
    all_goals omega

end

/--
The entry point.  On success, the derivation's residual obligations: the
non-variable entries of the context.
-/
def checkTop (Γ : Ctx) (p : Pf) (M : Form) : Except Err (List (Pf × Form)) := do
  let _ ← check Γ p M
  pure (Ctx.obligations Γ)

end LaxLogic.QLL
