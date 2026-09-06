/-
# `LaxLogic.QLL.Certify` — a checker that returns the derivation

`Check.lean` decides whether a proof term proves a formula and returns
`Unit`, leaving soundness — "an accepted term really is a derivation" — as a
theorem to prove.  This module returns the derivation itself:

    infer : (Γ) → (p) → Except Err (Σ M, Derives p Γ M)
    check : (Γ) → (p) → (M) → Except Err (Derives p Γ M)

so soundness is not proved, it is **typed**.  There is no theorem, and no gap
between what the checker accepts and what the calculus derives.  This is only
possible because `Derives` is `Type`-valued.

## What it is *not* complete for

Bidirectional checking of Curry-style terms cannot inspect an elimination whose
subject is a non-inferable introduction form.  Concretely, these are derivable
and are **refused**:

    (λu.u) *                        `app` of a `lam`
    case (ι_c *) of [ι_x(z) → z]    `caseEx` of a `pack`

while `π₁(*, *)` is accepted, because `pair` does infer.  So the checker is
complete for terms in which every elimination's subject infers — normal terms,
in particular — and refuses certain β-redexes.  It never mis-accepts: the
return type forbids it.

This is a property of the bidirectional discipline, not of anything chosen
here, and it was true of the earlier `Check.lean` too.  An earlier revision of
this header claimed the checker was "complete for all of `Derivable`"; that was
wrong, and the corpus in the commit that deleted `Check.lean` is what showed it.

Completeness in the precise sense — every derivation of a *normal* term is
found — remains a genuine theorem and is **OPEN**; nothing here asserts it, and
it will need a renaming lemma, since `Derives` admits any fresh name while the
checker picks one.

## Inference for `∀`

`⟨p | x⟩` infers by closing the inferred body over the fresh individual, which
must then re-open to meet `allI`'s premise — and that roundtrip holds only for
locally closed formulas.  Rather than thread `lc` hypotheses through every
case, local closedness is *decided at the one place it is needed*
(`Form.decLcAt`), and a body with a loose index is refused with
`notLocallyClosed`.  That cannot arise for well-formed input, and it is a
refusal, never a mis-acceptance.

`allI`'s freshness condition mentions the formula, but the eigenvariable is
chosen before the formula is known.  `Form.not_mem_fv_closeWith` closes that
gap: whatever `A` turns out to be, `a` does not occur free in `closeWith a A`.

An earlier revision refused `⟨p | x⟩` in inference position outright, which
made this module incomplete where `Check.lean` was not — `π_c(⟨* | x⟩) : ⊤` is
derivable and was rejected.  That gap is closed and `Check.lean` is gone.

-/
import LaxLogic.QLL.Kit

namespace LaxLogic.QLL

/-- A formula together with a derivation of it. -/
abbrev Inferred (Γ : Ctx) (p : Pf) := Σ M : Form, Derives p Γ M

mutual

/-- Synthesise a formula *and a derivation of it*. -/
def infer' : (Γ : Ctx) → (p : Pf) → Except Err (Inferred Γ p)
  | _, .bvar i   => .error (.looseIndex i)
  | Γ, .fvar x   =>
      match h : Γ.lookup? x with
      | some M => .ok ⟨M, .var (lookup_mem h)⟩
      | none   => .error (.unbound x)
  | _, .star     => .ok ⟨.top, .topI⟩
  | Γ, .exf M p  => do
      let d ← check' Γ p .bot
      pure ⟨M, .botE d⟩
  | Γ, .pair p q => do
      let ⟨M, dp⟩ ← infer' Γ p
      let ⟨N, dq⟩ ← infer' Γ q
      pure ⟨.and M N, .andI dp dq⟩
  | Γ, .fst r    => do
      let ⟨A, dr⟩ ← infer' Γ r
      match A, dr with
      | .and M _, d => pure ⟨M, .andE₁ d⟩
      | A,        _ => .error (.expected "∧" A)
  | Γ, .snd r    => do
      let ⟨A, dr⟩ ← infer' Γ r
      match A, dr with
      | .and _ N, d => pure ⟨N, .andE₂ d⟩
      | A,        _ => .error (.expected "∧" A)
  | Γ, .app p q  => do
      let ⟨A, dp⟩ ← infer' Γ p
      match A, dp with
      | .imp M N, d => do
          let dq ← check' Γ q M
          pure ⟨N, .impE d dq⟩
      | A,        _ => .error (.expected "⊃" A)
  | Γ, .val q p  => do
      let ⟨M, dp⟩ ← infer' Γ p
      pure ⟨.circ q M, .circI dp⟩
  | Γ, .inst t p => do
      let ⟨A, dp⟩ ← infer' Γ p
      match A, dp with
      | .forall_ M, d => pure ⟨M.openAt 0 t, .allE t d rfl⟩
      | A,          _ => .error (.expected "∀" A)
  | Γ, .letQ q p b => do
      let ⟨A, dp⟩ ← infer' Γ p
      match A, dp with
      | .circ q' M, d =>
          if hq : q' = q then
            let z := freshFor (Ctx.fvP Γ ++ b.fvP)
            do
              let ⟨B, db⟩ ← infer' ((Pf.fvar z, M) :: Γ) (b.openPWith z)
              match B, db with
              | .circ q'' N, e =>
                  if hq2 : q'' = q then
                    pure ⟨.circ q N,
                      .circE z (freshP_freshFor Γ b) (hq ▸ d) (hq2 ▸ e)⟩
                  else .error (.modalityClash q'' q)
              | B, _ => .error (.expected "◯" B)
          else .error (.modalityClash q' q)
      | A, _ => .error (.expected "◯" A)
  | Γ, .caseOr r p q => do
      let ⟨A, dr⟩ ← infer' Γ r
      match A, dr with
      | .or M N, d =>
          let y := freshFor (Ctx.fvP Γ ++ p.fvP)
          let z := freshFor (Ctx.fvP Γ ++ q.fvP)
          do
            let ⟨K, d1⟩ ← infer' ((Pf.fvar y, M) :: Γ) (p.openPWith y)
            let d2 ← check' ((Pf.fvar z, N) :: Γ) (q.openPWith z) K
            pure ⟨K, .orE y z (freshP_freshFor Γ p) (freshP_freshFor Γ q) d d1 d2⟩
      | A,       _ => .error (.expected "∨" A)
  | Γ, .caseEx r p => do
      let ⟨A, dr⟩ ← infer' Γ r
      match A, dr with
      | .exists_ M, d =>
          let a := freshFor (Ctx.fvI Γ ++ p.fvI ++ M.fv)
          let z := freshFor (Ctx.fvP Γ ++ p.fvP)
          do
            let ⟨K, db⟩ ← infer' ((Pf.fvar z, M.openWith a) :: Γ) ((p.openIWith a).openPWith z)
            if hK : a ∈ K.fv then
              .error (.escapes a K)
            else
              pure ⟨K, .exE a z (freshI_freshFor Γ p M) hK (freshP_freshFor Γ p) d db⟩
      | A,          _ => .error (.expected "∃" A)
  | _, .lam _    => .error (.notInferable "λz.p")
  | _, .inl _    => .error (.notInferable "ι₁(p)")
  | _, .inr _    => .error (.notInferable "ι₂(q)")
  | _, .pack _ _ => .error (.notInferable "ι_t(p)")
  | Γ, .gen p    => do
      let a := freshFor (Ctx.fvI Γ ++ p.fvI)
      let ⟨A, d⟩ ← infer' Γ (p.openIWith a)
      if h : Form.lc A then
        pure ⟨.forall_ (Form.closeWith a A),
          .allI a
            ⟨(freshFor_notMem_of_mem_append (A := Ctx.fvI Γ) (B := p.fvI) rfl).1,
             (freshFor_notMem_of_mem_append (A := Ctx.fvI Γ) (B := p.fvI) rfl).2,
             Form.not_mem_fv_closeWith a A⟩
            ((Form.openWith_closeWith a h).symm ▸ d)⟩
      else
        .error (.notLocallyClosed A)
  termination_by _ p => 2 * p.size
  decreasing_by
    all_goals try simp_wf
    all_goals try simp only [Pf.size, size_openP, size_openI, Pf.openPWith, Pf.openIWith]
    all_goals omega

/-- Check a proof term against a goal, returning the derivation. -/
def check' : (Γ : Ctx) → (p : Pf) → (M : Form) → Except Err (Derives p Γ M)
  | Γ, .lam p, .imp M N => do
      let z := freshFor (Ctx.fvP Γ ++ p.fvP)
      let d ← check' ((Pf.fvar z, M) :: Γ) (p.openPWith z) N
      pure (.impI z (freshP_freshFor Γ p) d)
  | _, .lam _, A => .error (.expected "⊃" A)
  | Γ, .inl p, .or M _ => do
      let d ← check' Γ p M
      pure (.orI₁ d)
  | _, .inl _, A => .error (.expected "∨" A)
  | Γ, .inr q, .or _ N => do
      let d ← check' Γ q N
      pure (.orI₂ d)
  | _, .inr _, A => .error (.expected "∨" A)
  | Γ, .pack t p, .exists_ M => do
      let d ← check' Γ p (M.openAt 0 t)
      pure (.exI t d)
  | _, .pack _ _, A => .error (.expected "∃" A)
  | Γ, .gen p, .forall_ M => do
      let a := freshFor (Ctx.fvI Γ ++ p.fvI ++ M.fv)
      let d ← check' Γ (p.openIWith a) (M.openWith a)
      pure (.allI a (freshI_freshFor Γ p M) d)
  | _, .gen _, A => .error (.expected "∀" A)
  | Γ, .pair p q, .and M N => do
      let d ← check' Γ p M
      let e ← check' Γ q N
      pure (.andI d e)
  | _, .pair _ _, A => .error (.expected "∧" A)
  | Γ, p, M => do
      let ⟨A, d⟩ ← infer' Γ p
      if h : A = M then
        pure (h ▸ d)
      else
        .error (.mismatch M A)
  termination_by _ p _ => 2 * p.size + 1
  decreasing_by
    all_goals try simp_wf
    all_goals try simp only [Pf.size, size_openP, size_openI, Pf.openPWith, Pf.openIWith]
    all_goals omega

end

/--
The entry point: on success, the derivation *and* its residual obligations —
the non-variable entries of the context.
-/
def certify (Γ : Ctx) (p : Pf) (M : Form) :
    Except Err (Derives p Γ M × List (Pf × Form)) := do
  let d ← check' Γ p M
  pure (d, Ctx.obligations Γ)

end LaxLogic.QLL
