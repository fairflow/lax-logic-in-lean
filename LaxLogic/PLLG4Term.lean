import LaxLogic.PLLG4Set

/-!
# Proof terms for G4iLL″, and a fuel-free proof searcher

`G4sh` (`PLLG4Set.lean`) is `Prop`-valued: its derivations carry no data, which
is why the verified decider (`PLLG4Dec.lean`) can only answer `Bool`.  For
proof *exploration* we want the derivation itself.

`G4cTm Γ C` provides it: the proof terms of the repaired calculus G4iLL″, a
`Type`-valued mirror of `G4sh`'s sixteen rules over **list** contexts, in the
same discipline as `Tm` (`PLLTerms.lean`) — indices built only from variables,
constructors and cons; side conditions as plain list-membership propositions;
no `Finset`, no decidability instances.  A value of `G4cTm Γ C` is a
*kernel-checkable certificate* of derivability.

`prove` is a **fuel-free** backward searcher into that type.  It is `partial`,
so Lean demands no termination measure — hence no `decideFuel` and no `enum`;
the exponential fuel of `PLLG4Dec.lean` was an artefact of *proving* the
decider total, not of searching.  Termination in practice is by the loop check
alone: the visited set is keyed by `(canon Γ, C)` where `canon` removes
duplicates (keeping last occurrences), so re-deriving a formula already
present leaves the key unchanged and the revisit is caught.  Along any search
path the context only grows by consing subformula pieces, of which there are
finitely many, so keys must repeat.

`proveBounded` is the same search with one extra piece of threaded state: a
global budget of search nodes.  Every node entered (revisits included) costs
one unit, and a failed branch hands its *remaining* budget to the next
alternative, so the cap is on the **whole search tree**, not per branch or
per depth — exactly what tames the exponential grind on sequents that are
unprovable but missed by the countermodel battery.  Budget exhaustion is an
honest "unknown": it never asserts anything about the sequent.  See
`G4cTm.findBounded` for the precise reading of the result.

Trust is factored exactly as it should be: `prove` is *untrusted* code, but
anything it emits inhabits `G4cTm Γ C`, and

* `G4cTm.sound`    : every term projects to a `G4s` derivation, hence
  `G4cTm.toG4c` / `G4cTm.toTm`: a term certifies PLL provability;
* `G4cTm.ofG4c`    : conversely every `G4c`-derivable sequent has a term, so
  nothing is out of the searcher's reach in principle
  (`G4cTm.equiv_tm : Nonempty (G4cTm Γ C) ↔ Nonempty (Tm Γ C)`).

If the searcher builds a term, Lean's typechecker checks it — soundness is
the type system's job, not the search code's.
-/

open PLLFormula

namespace PLLND

/-- Proof terms of the repaired calculus G4iLL″ over list contexts: a
`Type`-valued mirror of `G4sh`'s rules (`insert` becomes cons, side conditions
are list membership). -/
inductive G4cTm : List PLLFormula → PLLFormula → Type
  | init {Γ : List PLLFormula} {a : String} (h : prop a ∈ Γ) : G4cTm Γ (prop a)
  | botL {Γ : List PLLFormula} {C : PLLFormula} (h : falsePLL ∈ Γ) : G4cTm Γ C
  | andR {Γ : List PLLFormula} {A B : PLLFormula} :
      G4cTm Γ A → G4cTm Γ B → G4cTm Γ (A.and B)
  | orR1 {Γ : List PLLFormula} {A B : PLLFormula} :
      G4cTm Γ A → G4cTm Γ (A.or B)
  | orR2 {Γ : List PLLFormula} {A B : PLLFormula} :
      G4cTm Γ B → G4cTm Γ (A.or B)
  | impR {Γ : List PLLFormula} {A B : PLLFormula} :
      G4cTm (A :: Γ) B → G4cTm Γ (A.ifThen B)
  | laxR {Γ : List PLLFormula} {A : PLLFormula} :
      G4cTm Γ A → G4cTm Γ A.somehow
  | laxL {Γ : List PLLFormula} {A B : PLLFormula} (h : A.somehow ∈ Γ) :
      G4cTm (A :: Γ) B.somehow → G4cTm Γ B.somehow
  | andL {Γ : List PLLFormula} {A B C : PLLFormula} (h : A.and B ∈ Γ) :
      G4cTm (A :: B :: Γ) C → G4cTm Γ C
  | orL {Γ : List PLLFormula} {A B C : PLLFormula} (h : A.or B ∈ Γ) :
      G4cTm (A :: Γ) C → G4cTm (B :: Γ) C → G4cTm Γ C
  | impLProp {Γ : List PLLFormula} {a : String} {B C : PLLFormula}
      (h : (prop a).ifThen B ∈ Γ) (ha : prop a ∈ Γ) :
      G4cTm (B :: Γ) C → G4cTm Γ C
  | impLAnd {Γ : List PLLFormula} {A B D C : PLLFormula}
      (h : (A.and B).ifThen D ∈ Γ) :
      G4cTm (A.ifThen (B.ifThen D) :: Γ) C → G4cTm Γ C
  | impLOr {Γ : List PLLFormula} {A B D C : PLLFormula}
      (h : (A.or B).ifThen D ∈ Γ) :
      G4cTm (A.ifThen D :: B.ifThen D :: Γ) C → G4cTm Γ C
  | impLImp {Γ : List PLLFormula} {A B D C : PLLFormula}
      (h : (A.ifThen B).ifThen D ∈ Γ) :
      G4cTm (B.ifThen D :: Γ) (A.ifThen B) → G4cTm (D :: Γ) C → G4cTm Γ C
  | impLLax {Γ : List PLLFormula} {A B C : PLLFormula}
      (h : A.somehow.ifThen B ∈ Γ) :
      G4cTm Γ A → G4cTm (B :: Γ) C → G4cTm Γ C
  | impLLaxLax {Γ : List PLLFormula} {A B X C : PLLFormula}
      (h : A.somehow.ifThen B ∈ Γ) (hX : X.somehow ∈ Γ) :
      G4cTm (X :: Γ) A.somehow → G4cTm (B :: Γ) C → G4cTm Γ C

namespace G4cTm

/-- Display a proof term as its rule tree. -/
def pretty {Γ : List PLLFormula} {C : PLLFormula} : G4cTm Γ C → String
  | .init _ => "init"
  | .botL _ => "⊥L"
  | .andR a b => s!"(∧R {a.pretty} {b.pretty})"
  | .orR1 a => s!"(∨R₁ {a.pretty})"
  | .orR2 a => s!"(∨R₂ {a.pretty})"
  | .impR a => s!"(→R {a.pretty})"
  | .laxR a => s!"(◯R {a.pretty})"
  | .laxL _ a => s!"(◯L {a.pretty})"
  | .andL _ a => s!"(∧L {a.pretty})"
  | .orL _ a b => s!"(∨L {a.pretty} {b.pretty})"
  | .impLProp _ _ a => s!"(→Lₐₜ {a.pretty})"
  | .impLAnd _ a => s!"(→L∧ {a.pretty})"
  | .impLOr _ a => s!"(→L∨ {a.pretty})"
  | .impLImp _ a b => s!"(→L→ {a.pretty} {b.pretty})"
  | .impLLax _ a b => s!"(→L◯ {a.pretty} {b.pretty})"
  | .impLLaxLax _ _ a b => s!"(→L◯◯ {a.pretty} {b.pretty})"

end G4cTm

/-- Canonical loop-check key: remove duplicates keeping the *last*
occurrence, so consing a formula already present leaves the key unchanged. -/
def canon : List PLLFormula → List PLLFormula
  | [] => []
  | A :: Γ => if A ∈ Γ then canon Γ else A :: canon Γ

mutual

/-- **Fuel-free backward proof search** for G4iLL″, emitting the proof term.
Untrusted `partial` code; terminates by the visited-set loop check (see the
file header).  Success is self-certifying: the result inhabits `G4cTm Γ C`. -/
partial def prove (V : List (List PLLFormula × PLLFormula))
    (Γ : List PLLFormula) (C : PLLFormula) : Option (G4cTm Γ C) :=
  let key := (canon Γ, C)
  if key ∈ V then none
  else
    (if h : falsePLL ∈ Γ then some (G4cTm.botL h) else none)
    <|> proveRight (key :: V) Γ C
    <|> proveLeft (key :: V) Γ C

/-- Right rules (with `init` folded into the atom case). -/
partial def proveRight (V : List (List PLLFormula × PLLFormula))
    (Γ : List PLLFormula) : (C : PLLFormula) → Option (G4cTm Γ C)
  | .prop a => if h : prop a ∈ Γ then some (G4cTm.init h) else none
  | .falsePLL => none
  | .and A B => do
      let t₁ ← prove V Γ A
      let t₂ ← prove V Γ B
      some (G4cTm.andR t₁ t₂)
  | .or A B =>
      (do some (G4cTm.orR1 (← prove V Γ A)))
      <|> (do some (G4cTm.orR2 (← prove V Γ B)))
  | .ifThen A B => do
      some (G4cTm.impR (← prove V (A :: Γ) B))
  | .somehow A =>
      (do some (G4cTm.laxR (← prove V Γ A)))
      <|> Γ.attach.findSome? fun ⟨F, hF⟩ =>
            match F, hF with
            | .somehow X, h => do
                some (G4cTm.laxL h (← prove V (X :: Γ) (somehow A)))
            | _, _ => none

/-- Left rules, tried on each context formula in turn. -/
partial def proveLeft (V : List (List PLLFormula × PLLFormula))
    (Γ : List PLLFormula) (C : PLLFormula) : Option (G4cTm Γ C) :=
  Γ.attach.findSome? fun ⟨F, hF⟩ =>
    match F, hF with
    | .and A B, h => do
        some (G4cTm.andL h (← prove V (A :: B :: Γ) C))
    | .or A B, h => do
        let t₁ ← prove V (A :: Γ) C
        let t₂ ← prove V (B :: Γ) C
        some (G4cTm.orL h t₁ t₂)
    | .ifThen (.prop a) B, h =>
        if ha : prop a ∈ Γ then do
          some (G4cTm.impLProp h ha (← prove V (B :: Γ) C))
        else none
    | .ifThen (.and A B) D, h => do
        some (G4cTm.impLAnd h (← prove V (A.ifThen (B.ifThen D) :: Γ) C))
    | .ifThen (.or A B) D, h => do
        some (G4cTm.impLOr h (← prove V (A.ifThen D :: B.ifThen D :: Γ) C))
    | .ifThen (.ifThen A B) D, h => do
        let t₁ ← prove V (B.ifThen D :: Γ) (A.ifThen B)
        let t₂ ← prove V (D :: Γ) C
        some (G4cTm.impLImp h t₁ t₂)
    | .ifThen (.somehow A) B, h =>
        (do let t₁ ← prove V Γ A
            let t₂ ← prove V (B :: Γ) C
            some (G4cTm.impLLax h t₁ t₂))
        <|> Γ.attach.findSome? fun ⟨X, hXf⟩ =>
              match X, hXf with
              | .somehow x, hX => do
                  let t₁ ← prove V (x :: Γ) (somehow A)
                  let t₂ ← prove V (B :: Γ) C
                  some (G4cTm.impLLaxLax h hX t₁ t₂)
              | _, _ => none
    | _, _ => none

end

/-- Search a sequent from scratch. -/
def G4cTm.find (Γ : List PLLFormula) (C : PLLFormula) : Option (G4cTm Γ C) :=
  prove [] Γ C

/-! ## The node-budgeted searcher

`proveBounded` mirrors `prove` rule for rule (same rules, same try order —
**keep the two in sync**), but threads a global node budget through the
search: state `Nat` is the remaining budget, and failure *preserves* it, so
sequential alternatives (`<|>`, `firstM`) draw from one shared pool.  One
unit is spent per `proveBounded` entry, i.e. per visited sequent (loop-check
revisits included, since the `canon`-key lookup is real work too).

Two honesty notes, both *by construction* rather than as theorems (`partial`
definitions are opaque to Lean's logic, so no lemma can relate `prove` and
`proveBounded` — the trust story is unaffected, because any emitted term
inhabits `G4cTm Γ C` and is checked by the kernel):

* the budget only ever truncates the search, so `none` under an exhausted
  budget means "not settled within the budget" — never underivability;
* the budget is inert until it reaches `0`, so a run that finishes with
  budget to spare made exactly the same rule attempts, in the same order,
  as the fuel-free `prove`.

Since both searchers are `partial`, neither reduces in the kernel; discovery
stays evaluation-side (`#eval` / `#guard`), and found terms are pinned and
kernel-checked as usual.  (A structurally recursive searcher — recursion on
the budget itself — would additionally reduce in the kernel on small
budgets, but it would have to share its budget across siblings through an
explicit work-list machine; that is a different engine, not a variant of
this one.) -/

/-- The budget-threading monad for `proveBounded`: an `Option` computation
over a `Nat` state (remaining node budget).  Unfolds to
`Nat → Option α × Nat`; crucially, failure returns the *remaining* budget,
so alternation continues from wherever the failed branch left off. -/
abbrev BudgetM (α : Type) : Type := OptionT (StateM Nat) α

instance {α : Type} : Inhabited (BudgetM α) := ⟨failure⟩

/-- Spend one unit of search budget; fail when the pool is dry.  This is the
single point where the budget is consumed or checked. -/
@[inline] def BudgetM.spendNode : BudgetM Unit := do
  match (← OptionT.lift (get : StateM Nat Nat)) with
  | 0 => failure
  | f + 1 => OptionT.lift (set f : StateM Nat Unit)

mutual

/-- Node-budgeted mirror of `prove` (see the section header).  Untrusted
`partial` code, same as `prove`; success is self-certifying. -/
partial def proveBounded (V : List (List PLLFormula × PLLFormula))
    (Γ : List PLLFormula) (C : PLLFormula) : BudgetM (G4cTm Γ C) := do
  BudgetM.spendNode
  let key := (canon Γ, C)
  if key ∈ V then failure
  else
    (if h : falsePLL ∈ Γ then pure (G4cTm.botL h) else failure)
    <|> proveRightBounded (key :: V) Γ C
    <|> proveLeftBounded (key :: V) Γ C

/-- Right rules, budgeted (mirror of `proveRight`). -/
partial def proveRightBounded (V : List (List PLLFormula × PLLFormula))
    (Γ : List PLLFormula) : (C : PLLFormula) → BudgetM (G4cTm Γ C)
  | .prop a => if h : prop a ∈ Γ then pure (G4cTm.init h) else failure
  | .falsePLL => failure
  | .and A B => do
      let t₁ ← proveBounded V Γ A
      let t₂ ← proveBounded V Γ B
      pure (G4cTm.andR t₁ t₂)
  | .or A B =>
      (do pure (G4cTm.orR1 (← proveBounded V Γ A)))
      <|> (do pure (G4cTm.orR2 (← proveBounded V Γ B)))
  | .ifThen A B => do
      pure (G4cTm.impR (← proveBounded V (A :: Γ) B))
  | .somehow A =>
      (do pure (G4cTm.laxR (← proveBounded V Γ A)))
      <|> Γ.attach.firstM fun ⟨F, hF⟩ =>
            match F, hF with
            | .somehow X, h => do
                pure (G4cTm.laxL h (← proveBounded V (X :: Γ) (somehow A)))
            | _, _ => failure

/-- Left rules, budgeted (mirror of `proveLeft`). -/
partial def proveLeftBounded (V : List (List PLLFormula × PLLFormula))
    (Γ : List PLLFormula) (C : PLLFormula) : BudgetM (G4cTm Γ C) :=
  Γ.attach.firstM fun ⟨F, hF⟩ =>
    match F, hF with
    | .and A B, h => do
        pure (G4cTm.andL h (← proveBounded V (A :: B :: Γ) C))
    | .or A B, h => do
        let t₁ ← proveBounded V (A :: Γ) C
        let t₂ ← proveBounded V (B :: Γ) C
        pure (G4cTm.orL h t₁ t₂)
    | .ifThen (.prop a) B, h =>
        if ha : prop a ∈ Γ then do
          pure (G4cTm.impLProp h ha (← proveBounded V (B :: Γ) C))
        else failure
    | .ifThen (.and A B) D, h => do
        pure (G4cTm.impLAnd h (← proveBounded V (A.ifThen (B.ifThen D) :: Γ) C))
    | .ifThen (.or A B) D, h => do
        pure (G4cTm.impLOr h (← proveBounded V (A.ifThen D :: B.ifThen D :: Γ) C))
    | .ifThen (.ifThen A B) D, h => do
        let t₁ ← proveBounded V (B.ifThen D :: Γ) (A.ifThen B)
        let t₂ ← proveBounded V (D :: Γ) C
        pure (G4cTm.impLImp h t₁ t₂)
    | .ifThen (.somehow A) B, h =>
        (do let t₁ ← proveBounded V Γ A
            let t₂ ← proveBounded V (B :: Γ) C
            pure (G4cTm.impLLax h t₁ t₂))
        <|> Γ.attach.firstM fun ⟨X, hXf⟩ =>
              match X, hXf with
              | .somehow x, hX => do
                  let t₁ ← proveBounded V (x :: Γ) (somehow A)
                  let t₂ ← proveBounded V (B :: Γ) C
                  pure (G4cTm.impLLaxLax h hX t₁ t₂)
              | _, _ => failure
    | _, _ => failure

end

/-- **Node-budget-capped search** from scratch.  Returns the search result
together with the *remaining* budget.  Reading the pair:

* `(some t, _)`   — proof found; `t` is kernel-checkable exactly as with
  `find` (a smaller budget can only lose proofs, never invent them);
* `(none, k + 1)` — the search space was exhausted with budget to spare:
  the run made the same attempts as the fuel-free `find`, so this is the
  same (certificate-free, see the trust note) `none` that `find` returns;
* `(none, 0)`     — the budget ran out (or the search finished exactly as
  it hit `0` — indistinguishable, so read it conservatively): honest
  **unknown**, never a negative verdict.

`budget - remaining` is the number of nodes visited — a free profiler for
tuning budgets in probe sessions. -/
def G4cTm.findBounded (budget : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    Option (G4cTm Γ C) × Nat :=
  Id.run (StateT.run (OptionT.run (proveBounded [] Γ C)) budget)

/-! ## The bridge: terms certify provability, provability yields terms -/

namespace G4cTm

/-- **Soundness by projection**: a proof term yields a `G4s` derivation of the
corresponding set-sequent (choice-free `toFin` form). -/
theorem sound' : ∀ {Γ : List PLLFormula} {C : PLLFormula},
    G4cTm Γ C → G4s (toFin Γ) C := by
  intro Γ C t
  induction t with
  | init h => exact ⟨0, .init (mem_toFin.mpr h)⟩
  | botL h => exact ⟨0, .botL (mem_toFin.mpr h)⟩
  | andR _ _ ih₁ ih₂ =>
      obtain ⟨n₁, d₁⟩ := ih₁; obtain ⟨n₂, d₂⟩ := ih₂
      exact ⟨_, .andR (d₁.mono (Nat.le_max_left n₁ n₂))
        (d₂.mono (Nat.le_max_right n₁ n₂))⟩
  | orR1 _ ih => obtain ⟨n, d⟩ := ih; exact ⟨n + 1, .orR1 d⟩
  | orR2 _ ih => obtain ⟨n, d⟩ := ih; exact ⟨n + 1, .orR2 d⟩
  | impR _ ih =>
      obtain ⟨n, d⟩ := ih
      rw [toFin_cons] at d
      exact ⟨n + 1, .impR d⟩
  | laxR _ ih => obtain ⟨n, d⟩ := ih; exact ⟨n + 1, .laxR d⟩
  | laxL h _ ih =>
      obtain ⟨n, d⟩ := ih
      rw [toFin_cons] at d
      exact ⟨n + 1, .laxL (mem_toFin.mpr h) d⟩
  | andL h _ ih =>
      obtain ⟨n, d⟩ := ih
      rw [toFin_cons, toFin_cons] at d
      exact ⟨n + 1, .andL (mem_toFin.mpr h) d⟩
  | orL h _ _ ih₁ ih₂ =>
      obtain ⟨n₁, d₁⟩ := ih₁; obtain ⟨n₂, d₂⟩ := ih₂
      rw [toFin_cons] at d₁ d₂
      exact ⟨_, .orL (mem_toFin.mpr h)
        ((d₁.mono (Nat.le_max_left n₁ n₂)))
        ((d₂.mono (Nat.le_max_right n₁ n₂)))⟩
  | impLProp h ha _ ih =>
      obtain ⟨n, d⟩ := ih
      rw [toFin_cons] at d
      exact ⟨n + 1, .impLProp (mem_toFin.mpr h)
        (mem_toFin.mpr ha) d⟩
  | impLAnd h _ ih =>
      obtain ⟨n, d⟩ := ih
      rw [toFin_cons] at d
      exact ⟨n + 1, .impLAnd (mem_toFin.mpr h) d⟩
  | impLOr h _ ih =>
      obtain ⟨n, d⟩ := ih
      rw [toFin_cons, toFin_cons] at d
      exact ⟨n + 1, .impLOr (mem_toFin.mpr h) d⟩
  | impLImp h _ _ ih₁ ih₂ =>
      obtain ⟨n₁, d₁⟩ := ih₁; obtain ⟨n₂, d₂⟩ := ih₂
      rw [toFin_cons] at d₁ d₂
      exact ⟨_, .impLImp (mem_toFin.mpr h)
        (d₁.mono (Nat.le_max_left n₁ n₂)) (d₂.mono (Nat.le_max_right n₁ n₂))⟩
  | impLLax h _ _ ih₁ ih₂ =>
      obtain ⟨n₁, d₁⟩ := ih₁; obtain ⟨n₂, d₂⟩ := ih₂
      rw [toFin_cons] at d₂
      exact ⟨_, .impLLax (mem_toFin.mpr h)
        (d₁.mono (Nat.le_max_left n₁ n₂)) (d₂.mono (Nat.le_max_right n₁ n₂))⟩
  | impLLaxLax h hX _ _ ih₁ ih₂ =>
      obtain ⟨n₁, d₁⟩ := ih₁; obtain ⟨n₂, d₂⟩ := ih₂
      rw [toFin_cons] at d₁ d₂
      exact ⟨_, .impLLaxLax (mem_toFin.mpr h)
        (mem_toFin.mpr hX)
        (d₁.mono (Nat.le_max_left n₁ n₂)) (d₂.mono (Nat.le_max_right n₁ n₂))⟩

/-- Legacy `toFinset` form, derived; statement-tainted through
`List.toFinset`.  The clean chain uses `sound'`. -/
theorem sound {Γ : List PLLFormula} {C : PLLFormula} (t : G4cTm Γ C) :
    G4s Γ.toFinset C := by
  rw [← toFin_eq_toFinset]
  exact t.sound'

/-- A proof term certifies `G4c` derivability. -/
theorem toG4c {Γ : List PLLFormula} {C : PLLFormula} (t : G4cTm Γ C) :
    G4c Γ C := G4c.iff_setFin.mpr t.sound' 

/-- A proof term certifies PLL provability (via `G4c.equiv_tm`). -/
theorem toTm {Γ : List PLLFormula} {C : PLLFormula} (t : G4cTm Γ C) :
    Nonempty (Tm Γ C) := G4c.equiv_tm.mp t.toG4c

private theorem nonempty_ofSet :
    ∀ {n : Nat} {Γs : Finset PLLFormula} {E : PLLFormula}, G4sh n Γs E →
    ∀ {Γ : List PLLFormula}, toFin Γ = Γs → Nonempty (G4cTm Γ E) := by
  intro n Γs E d
  induction d with
  | init h =>
      intro Γ hΓ; subst hΓ
      exact ⟨.init (mem_toFin.mp h)⟩
  | botL h =>
      intro Γ hΓ; subst hΓ
      exact ⟨.botL (mem_toFin.mp h)⟩
  | andR _ _ ih₁ ih₂ =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t₁⟩ := ih₁ rfl; obtain ⟨t₂⟩ := ih₂ rfl
      exact ⟨.andR t₁ t₂⟩
  | orR1 _ ih =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t⟩ := ih rfl
      exact ⟨.orR1 t⟩
  | orR2 _ ih =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t⟩ := ih rfl
      exact ⟨.orR2 t⟩
  | @impR _ _ A B _ ih =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t⟩ := ih (Γ := A :: Γ) (by rw [toFin_cons])
      exact ⟨.impR t⟩
  | laxR _ ih =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t⟩ := ih rfl
      exact ⟨.laxR t⟩
  | @laxL _ _ A B h _ ih =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t⟩ := ih (Γ := A :: Γ) (by rw [toFin_cons])
      exact ⟨.laxL (mem_toFin.mp h) t⟩
  | @andL _ _ A B _ h _ ih =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t⟩ := ih (Γ := A :: B :: Γ)
        (by rw [toFin_cons, toFin_cons])
      exact ⟨.andL (mem_toFin.mp h) t⟩
  | @orL _ _ A B _ h _ _ ih₁ ih₂ =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t₁⟩ := ih₁ (Γ := A :: Γ) (by rw [toFin_cons])
      obtain ⟨t₂⟩ := ih₂ (Γ := B :: Γ) (by rw [toFin_cons])
      exact ⟨.orL (mem_toFin.mp h) t₁ t₂⟩
  | @impLProp _ _ a B _ h ha _ ih =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t⟩ := ih (Γ := B :: Γ) (by rw [toFin_cons])
      exact ⟨.impLProp (mem_toFin.mp h) (mem_toFin.mp ha) t⟩
  | @impLAnd _ _ A B D _ h _ ih =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t⟩ := ih (Γ := A.ifThen (B.ifThen D) :: Γ)
        (by rw [toFin_cons])
      exact ⟨.impLAnd (mem_toFin.mp h) t⟩
  | @impLOr _ _ A B D _ h _ ih =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t⟩ := ih (Γ := A.ifThen D :: B.ifThen D :: Γ)
        (by rw [toFin_cons, toFin_cons])
      exact ⟨.impLOr (mem_toFin.mp h) t⟩
  | @impLImp _ _ A B D _ h _ _ ih₁ ih₂ =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t₁⟩ := ih₁ (Γ := B.ifThen D :: Γ) (by rw [toFin_cons])
      obtain ⟨t₂⟩ := ih₂ (Γ := D :: Γ) (by rw [toFin_cons])
      exact ⟨.impLImp (mem_toFin.mp h) t₁ t₂⟩
  | @impLLax _ _ A B _ h _ _ ih₁ ih₂ =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t₁⟩ := ih₁ rfl
      obtain ⟨t₂⟩ := ih₂ (Γ := B :: Γ) (by rw [toFin_cons])
      exact ⟨.impLLax (mem_toFin.mp h) t₁ t₂⟩
  | @impLLaxLax _ _ A B X _ h hX _ _ ih₁ ih₂ =>
      intro Γ hΓ; subst hΓ
      obtain ⟨t₁⟩ := ih₁ (Γ := X :: Γ) (by rw [toFin_cons])
      obtain ⟨t₂⟩ := ih₂ (Γ := B :: Γ) (by rw [toFin_cons])
      exact ⟨.impLLaxLax (mem_toFin.mp h) (mem_toFin.mp hX)
        t₁ t₂⟩

/-- **Completeness in principle**: every `G4c`-derivable sequent has a proof
term — nothing is out of the searcher's reach. -/
theorem ofG4c {Γ : List PLLFormula} {C : PLLFormula} (h : G4c Γ C) :
    Nonempty (G4cTm Γ C) := by
  obtain ⟨n, d⟩ := G4c.iff_setFin.mp h
  exact nonempty_ofSet d rfl

/-- **G4iLL″ proof terms = PLL proof terms**, at the level of inhabitation. -/
theorem equiv_tm {Γ : List PLLFormula} {C : PLLFormula} :
    Nonempty (G4cTm Γ C) ↔ Nonempty (Tm Γ C) :=
  ⟨fun ⟨t⟩ => t.toTm, fun h => ofG4c (G4c.equiv_tm.mpr h)⟩

end G4cTm

/-! ## Smoke tests -/

-- ⊢ ⊥ → ⊥
#eval (G4cTm.find [] (falsePLL.ifThen falsePLL)).map (·.pretty)

-- p ⊢ ◯p  (the unit)
#eval (G4cTm.find [prop "p"] (prop "p").somehow).map (·.pretty)

-- ◯p ⊢ p  (no escape: expect `none`, matching the verified decider)
#eval (G4cTm.find [(prop "p").somehow] (prop "p")).map (·.pretty)

-- The gap sequent  ◯((◯p → r) → ◯p), ◯p → r ⊢ r :
-- G4c derives it; the naive calculus `G4` does not (`PLLG4Gap`).
#eval
  let φ₁ := ((((prop "p").somehow).ifThen (prop "r")).ifThen
    ((prop "p").somehow)).somehow
  let φ₂ := ((prop "p").somehow).ifThen (prop "r")
  (G4cTm.find [φ₁, φ₂] (prop "r")).map (·.pretty)

-- `sound` is statement-tainted (`List.toFinset`); everything else in the
-- bridge is choice-free.
/--
info: 'PLLND.G4cTm.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G4cTm.sound

/-- info: 'PLLND.G4cTm.sound'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms G4cTm.sound'

/-- info: 'PLLND.G4cTm.ofG4c' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms G4cTm.ofG4c

/-- info: 'PLLND.G4cTm.equiv_tm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms G4cTm.equiv_tm

end PLLND
