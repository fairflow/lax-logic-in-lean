/-
# `LaxLogic.QLL.Certify` — a checker that returns the derivation

`Check.lean` decides whether a proof term proves a formula and returns
`Unit`, leaving soundness — "an accepted term really is a derivation" — as a
theorem to prove.  This module returns the derivation itself:

    infer : (Γ) → (p) → Except Err (Σ A, Derives p Γ A)
    check : (Γ) → (p) → (A) → Except Err (Derives p Γ A)

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
gap: whatever `C` turns out to be, `a` does not occur free in `closeWith a C`.

An earlier revision refused `⟨p | x⟩` in inference position outright, which
made this module incomplete where `Check.lean` was not — `π_c(⟨* | x⟩) : ⊤` is
derivable and was rejected.  That gap is closed and `Check.lean` is gone.

-/
import LaxLogic.QLL.Kit

namespace LaxLogic.QLL

/-- C formula together with a derivation of it. -/
abbrev Inferred (Γ : Ctx) (p : Pf) := Σ A : Form, Derives p Γ A

mutual

/-- Synthesise a formula *and a derivation of it*. -/
def infer' : (Γ : Ctx) → (p : Pf) → Except Err (Inferred Γ p)
  | _, .bvar i   => .error (.looseIndex i)
  | Γ, .fvar x   =>
      match h : Γ.lookup? x with
      | some A => .ok ⟨A, .var (lookup_mem h)⟩
      | none   => .error (.unbound x)
  | _, .star     => .ok ⟨.top, .topI⟩
  | Γ, .exf A p  => do
      let d ← check' Γ p .bot
      pure ⟨A, .botE d⟩
  | Γ, .pair p q => do
      let ⟨A, dp⟩ ← infer' Γ p
      let ⟨B, dq⟩ ← infer' Γ q
      pure ⟨.and A B, .andI dp dq⟩
  | Γ, .fst r    => do
      let ⟨C, dr⟩ ← infer' Γ r
      match C, dr with
      | .and A _, d => pure ⟨A, .andE₁ d⟩
      | C,        _ => .error (.expected "∧" C)
  | Γ, .snd r    => do
      let ⟨C, dr⟩ ← infer' Γ r
      match C, dr with
      | .and _ B, d => pure ⟨B, .andE₂ d⟩
      | C,        _ => .error (.expected "∧" C)
  | Γ, .app p q  => do
      let ⟨C, dp⟩ ← infer' Γ p
      match C, dp with
      | .imp A B, d => do
          let dq ← check' Γ q A
          pure ⟨B, .impE d dq⟩
      | C,        _ => .error (.expected "↠" C)
  | Γ, .val q p  => do
      let ⟨A, dp⟩ ← infer' Γ p
      pure ⟨.circ q A, .circI dp⟩
  | Γ, .inst t p => do
      let ⟨C, dp⟩ ← infer' Γ p
      match C, dp with
      | .forall_ A, d => pure ⟨A.openAt 0 t, .allE t d rfl⟩
      | C,          _ => .error (.expected "∀" C)
  | Γ, .letQ q p b => do
      let ⟨C, dp⟩ ← infer' Γ p
      match C, dp with
      | .circ q' A, d =>
          if hq : q' = q then
            let z := freshFor (Ctx.fvP Γ ++ b.fvP)
            do
              let ⟨Y, db⟩ ← infer' ((Pf.fvar z, A) :: Γ) (b.openPWith z)
              match Y, db with
              | .circ q'' B, e =>
                  if hq2 : q'' = q then
                    pure ⟨.circ q B,
                      .circE z (freshP_freshFor Γ b) (hq ▸ d) (hq2 ▸ e)⟩
                  else .error (.modalityClash q'' q)
              | Y, _ => .error (.expected "◯" Y)
          else .error (.modalityClash q' q)
      | C, _ => .error (.expected "◯" C)
  | Γ, .caseOr r p q => do
      let ⟨C, dr⟩ ← infer' Γ r
      match C, dr with
      | .or A B, d =>
          let y := freshFor (Ctx.fvP Γ ++ p.fvP)
          let z := freshFor (Ctx.fvP Γ ++ q.fvP)
          do
            let ⟨K, d1⟩ ← infer' ((Pf.fvar y, A) :: Γ) (p.openPWith y)
            let d2 ← check' ((Pf.fvar z, B) :: Γ) (q.openPWith z) K
            pure ⟨K, .orE y z (freshP_freshFor Γ p) (freshP_freshFor Γ q) d d1 d2⟩
      | C,       _ => .error (.expected "∨" C)
  | Γ, .caseEx r p => do
      let ⟨C, dr⟩ ← infer' Γ r
      match C, dr with
      | .exists_ A, d =>
          let a := freshFor (Ctx.fvI Γ ++ p.fvI ++ A.fv)
          let z := freshFor (Ctx.fvP Γ ++ p.fvP)
          do
            let ⟨K, db⟩ ← infer' ((Pf.fvar z, A.openWith a) :: Γ) ((p.openIWith a).openPWith z)
            if hK : a ∈ K.fv then
              .error (.escapes a K)
            else
              pure ⟨K, .exE a z (freshI_freshFor Γ p A) hK (freshP_freshFor Γ p) d db⟩
      | C,          _ => .error (.expected "∃" C)
  | _, .lam _    => .error (.notInferable "λz.p")
  | _, .inl _    => .error (.notInferable "ι₁(p)")
  | _, .inr _    => .error (.notInferable "ι₂(q)")
  | _, .pack _ _ => .error (.notInferable "ι_t(p)")
  | Γ, .gen p    => do
      let a := freshFor (Ctx.fvI Γ ++ p.fvI)
      let ⟨C, d⟩ ← infer' Γ (p.openIWith a)
      if h : Form.lc C then
        pure ⟨.forall_ (Form.closeWith a C),
          .allI a
            ⟨(freshFor_notMem_of_mem_append (X := Ctx.fvI Γ) (Y := p.fvI) rfl).1,
             (freshFor_notMem_of_mem_append (X := Ctx.fvI Γ) (Y := p.fvI) rfl).2,
             Form.not_mem_fv_closeWith a C⟩
            ((Form.openWith_closeWith a h).symm ▸ d)⟩
      else
        .error (.notLocallyClosed C)
  termination_by _ p => 2 * p.size
  decreasing_by
    all_goals try simp_wf
    all_goals try simp only [Pf.size, size_openP, size_openI, Pf.openPWith, Pf.openIWith]
    all_goals omega

/-- Check a proof term against a goal, returning the derivation. -/
def check' : (Γ : Ctx) → (p : Pf) → (A : Form) → Except Err (Derives p Γ A)
  | Γ, .lam p, .imp A B => do
      let z := freshFor (Ctx.fvP Γ ++ p.fvP)
      let d ← check' ((Pf.fvar z, A) :: Γ) (p.openPWith z) B
      pure (.impI z (freshP_freshFor Γ p) d)
  | _, .lam _, C => .error (.expected "↠" C)
  | Γ, .inl p, .or A _ => do
      let d ← check' Γ p A
      pure (.orI₁ d)
  | _, .inl _, C => .error (.expected "∨" C)
  | Γ, .inr q, .or _ B => do
      let d ← check' Γ q B
      pure (.orI₂ d)
  | _, .inr _, C => .error (.expected "∨" C)
  | Γ, .pack t p, .exists_ A => do
      let d ← check' Γ p (A.openAt 0 t)
      pure (.exI t d)
  | _, .pack _ _, C => .error (.expected "∃" C)
  | Γ, .gen p, .forall_ A => do
      let a := freshFor (Ctx.fvI Γ ++ p.fvI ++ A.fv)
      let d ← check' Γ (p.openIWith a) (A.openWith a)
      pure (.allI a (freshI_freshFor Γ p A) d)
  | _, .gen _, C => .error (.expected "∀" C)
  | Γ, .pair p q, .and A B => do
      let d ← check' Γ p A
      let e ← check' Γ q B
      pure (.andI d e)
  | _, .pair _ _, C => .error (.expected "∧" C)
  | Γ, p, A => do
      let ⟨C, d⟩ ← infer' Γ p
      if h : C = A then
        pure (h ▸ d)
      else
        .error (.mismatch A C)
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
def certify (Γ : Ctx) (p : Pf) (A : Form) :
    Except Err (Derives p Γ A × List (Pf × Form)) := do
  let d ← check' Γ p A
  pure (d, Ctx.obligations Γ)

end LaxLogic.QLL
