import LaxLogic.PLL.G4.G4Set

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

`proveM` is a **fuel-free** backward searcher into that type.  It is `partial`,
so Lean demands no termination measure — hence no `decideFuel` and no `enum`;
the exponential fuel of `PLLG4Dec.lean` was an artefact of *proving* the
decider total, not of searching.  Termination in practice is by the loop check
alone: the visited set is keyed by `(canon Γ, C)` where `canon` removes
duplicates (keeping last occurrences), so re-deriving a formula already
present leaves the key unchanged and the revisit is caught.  Along any search
path the context only grows by consing subformula pieces, of which there are
finitely many, so keys must repeat.  A failure memo prunes failing subgoals
met on several branches; each failure is stored with the loop-check cuts it
depended on and reused only where those ancestors are present (corrected
2026-10-19: an unconditional memo lost derivable sequents, see `proveM`).

`proveBounded` is the same search with one extra piece of threaded state: a
global budget of search nodes.  Every node entered (revisits included) costs
one unit, and a failed branch hands its *remaining* budget to the next
alternative, so the cap is on the **whole search tree**, not per branch or
per depth — exactly what tames the exponential grind on sequents that are
unprovable but missed by the countermodel battery.  Budget exhaustion is an
honest "unknown": it never asserts anything about the sequent.  See
`G4cTm.findBounded` for the precise reading of the result.

Trust is factored exactly as it should be: `proveM` is *untrusted* code, but
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

-- Structural hash, for order-canonical loop keys.
deriving instance Hashable for PLLFormula

/-- **Order-canonical loop key** (UI-track optimisation, `g4ill_probe.hkey`).
`canon` already removes duplicates (contraction is admissible in G4iLL″);
sorting the deduplicated context by `hash` makes the key insensitive to the
*order* of hypotheses too, so sequents reached by the same rules in a different
order share a key and the visited-set check catches the revisit.  The key is the
canonical multiset itself, compared structurally, so a hash collision can only
*miss* a cut (a little extra search), never make a wrong one: soundness and
termination are unchanged, the search space only shrinks. -/
def ckey (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula × PLLFormula :=
  ((canon Γ).mergeSort (fun a b => compare (hash a) (hash b) |>.isLE), C)

/-- A canonical sequent key, as computed by `ckey`. -/
abbrev SeqKey : Type := List PLLFormula × PLLFormula

/-- The **dependency-aware failure memo**: a key found underivable, mapped to
the *dependency set* of that failure — the keys of the node's ancestors (on
the branch where the failure was found) that loop-check cuts below it hit,
directly or through a reused memo entry.  `[]` is an unconditional failure.
A key searched again and failing again keeps the latest dependency set.
Keyed by `ckey` (homogeneous, so no dependent proof term is ever stored). -/
abbrev FailMemo := Std.HashMap SeqKey (List SeqKey)

/-- Search state shared by `proveM` and `proveBounded`: the failure memo, and
an accumulator of the dependencies (cut keys and the dependency sets of reused
memo entries) met since the current node was entered. -/
structure MemoState where
  memo : FailMemo := ∅
  cuts : List SeqKey := []

/-- The dependency set of a memoised failure of `key`, if that failure may be
reused under the ancestors `V`: only when every key it depends on is among
them. -/
@[inline] def MemoState.reusable (s : MemoState) (V : List SeqKey) (key : SeqKey) :
    Option (List SeqKey) :=
  match s.memo[key]? with
  | some D => if D.all (· ∈ V) then some D else none
  | none => none

/-- Record dependencies met: a loop-check cut (`[key]`) or a reused failure. -/
@[inline] def MemoState.note (s : MemoState) (D : List SeqKey) : MemoState :=
  { s with cuts := D ++ s.cuts }

/-- Close a failed node with ancestors `V`: its dependency set `D` is the part
of the accumulator lying in `V` (the node's own key, and every key of the
subtree, drops out); memoise `D` when `record`, and hand it up by restoring the
parent's accumulator `saved` with `D` added. -/
@[inline] def MemoState.fail (s : MemoState) (V : List SeqKey) (key : SeqKey)
    (saved : List SeqKey) (record : Bool := true) : MemoState :=
  let D := if s.cuts.isEmpty then [] else V.filter (· ∈ s.cuts)
  { memo := if record then s.memo.insert key D else s.memo, cuts := D ++ saved }

/-- First `some` in a short-circuiting monadic scan, threading the memo. -/
partial def firstSomeM {α β : Type} (xs : List α)
    (f : α → StateM MemoState (Option β)) : StateM MemoState (Option β) := do
  match xs with
  | [] => return none
  | x :: rest => match ← f x with
    | some b => return (some b)
    | none => firstSomeM rest f

mutual

/-- **Fuel-free backward proof search** for G4iLL″ with a dependency-aware
failure memo.  `V` is the path-local ancestor set (functional, so it
backtracks) driving the loop check; the `StateM` memo records failures, so a
failing subgoal reached on many branches is searched again only when its
recorded failure depended on an ancestor that the current branch lacks.

**Why the memo carries dependencies** (corrected 2026-10-19).  A failure can be
caused by a loop-check cut (`key ∈ V`) below it, and is then conditional on
`V`: the same sequent can be derivable on a branch that lacks the cut
ancestor.  Until 2026-10-19 every failure was memoised as unconditional, and
reusing a conditional one gave a false `none` on derivable sequents (the
regression in `Search/Run.lean`).  Now a failure is stored with its
dependency set `D` (`MemoState.fail`) and reused only when `D ⊆ V`
(`MemoState.reusable`).

**What a `none` means** (an argument about this code, not a theorem).  Write
`Der_S(s)` for: `s` has a `G4cTm` derivation in which no node's key (`ckey`)
lies in `S` and no key repeats along a branch.  At a failing node every rule
instance of G4c is tried, so by induction over the search a call with
ancestors `V` that fails with dependency set `D` has `D ⊆ V` and
`¬ Der_D(s)`:

* a cut (`key ∈ V`) fails with `D = [key]`;
* a memo entry is reused only under ancestors containing its `D`;
* a node fails only when every rule instance has a premise failing with some
  `D' ⊆ key :: V`; its `D` is the union of these minus `key`, which may be
  dropped because `Der_D(s)` asks the premises to avoid `key` anyway.

Reuse across sequents with the same key is sound because `Der_D` depends on
the key alone: equal keys mean the same context set and succedent, and as
`ckey` is a stable sort of the deduplicated context, consing one formula onto
two such sequents again gives equal keys.  At the root `V = []`, so `D = []`,
and `¬ Der_∅(s)` is G4c-underivability: a derivation with fewest nodes
repeats no key along a branch (the rules see only the set of the context, so
the upper of two same-key nodes, transported down, replaces the lower).  So
a `none` is *intended* to mean "not G4c-derivable", hence (`G4c.equiv_tm`)
not PLL-derivable.  It is **not a certificate**: `proveM` is `partial`, its
body is invisible to Lean's logic, and no lemma relates it to `G4c`.  A
refutation needs a kernel-checked countermodel (`PLLND.Search.settle`'s
`.refuted`).

Success is self-certifying (the result inhabits `G4cTm Γ C`).  Successes are
not cached — they carry a dependent term, and returning on the first success
already makes them cheap — and a successful subtree hands no dependencies up,
since it is not the cause of any failure. -/
partial def proveM (V : List SeqKey)
    (Γ : List PLLFormula) (C : PLLFormula) : StateM MemoState (Option (G4cTm Γ C)) := do
  let key := ckey Γ C
  if key ∈ V then
    modify (·.note [key]); return none
  if let some D := (← get).reusable V key then
    modify (·.note D); return none
  if h : falsePLL ∈ Γ then return some (G4cTm.botL h)
  let saved := (← get).cuts
  modify fun s => { s with cuts := [] }
  let r ← match ← proveRightM (key :: V) Γ C with
    | some t => pure (some t)
    | none => proveLeftM (key :: V) Γ C
  match r with
  | some t => modify (fun s => { s with cuts := saved }); return some t
  | none => modify (·.fail V key saved); return none

/-- Right rules (with `init` folded into the atom case). -/
partial def proveRightM (V : List SeqKey)
    (Γ : List PLLFormula) : (C : PLLFormula) → StateM MemoState (Option (G4cTm Γ C))
  | .prop a => pure (if h : prop a ∈ Γ then some (G4cTm.init h) else none)
  | .falsePLL => pure none
  | .and A B => do
      match ← proveM V Γ A with
      | none => return none
      | some t₁ => match ← proveM V Γ B with
        | none => return none
        | some t₂ => return some (G4cTm.andR t₁ t₂)
  | .or A B => do
      match ← proveM V Γ A with
      | some t => return some (G4cTm.orR1 t)
      | none => match ← proveM V Γ B with
        | some t => return some (G4cTm.orR2 t)
        | none => return none
  | .ifThen A B => do
      match ← proveM V (A :: Γ) B with
      | some t => return some (G4cTm.impR t)
      | none => return none
  | .somehow A => do
      match ← proveM V Γ A with
      | some t => return some (G4cTm.laxR t)
      | none => firstSomeM Γ.attach (fun ⟨F, hF⟩ =>
          match F, hF with
          | .somehow X, h => do
              match ← proveM V (X :: Γ) (somehow A) with
              | some t => return some (G4cTm.laxL h t)
              | none => return none
          | _, _ => pure none)

/-- Left rules, tried on each context formula in turn. -/
partial def proveLeftM (V : List SeqKey)
    (Γ : List PLLFormula) (C : PLLFormula) : StateM MemoState (Option (G4cTm Γ C)) :=
  firstSomeM Γ.attach (fun ⟨F, hF⟩ =>
    match F, hF with
    | .and A B, h => do
        match ← proveM V (A :: B :: Γ) C with
        | some t => return some (G4cTm.andL h t)
        | none => return none
    | .or A B, h => do
        match ← proveM V (A :: Γ) C with
        | none => return none
        | some t₁ => match ← proveM V (B :: Γ) C with
          | none => return none
          | some t₂ => return some (G4cTm.orL h t₁ t₂)
    | .ifThen (.prop a) B, h => do
        if ha : prop a ∈ Γ then
          match ← proveM V (B :: Γ) C with
          | some t => return some (G4cTm.impLProp h ha t)
          | none => return none
        else return none
    | .ifThen (.and A B) D, h => do
        match ← proveM V (A.ifThen (B.ifThen D) :: Γ) C with
        | some t => return some (G4cTm.impLAnd h t)
        | none => return none
    | .ifThen (.or A B) D, h => do
        match ← proveM V (A.ifThen D :: B.ifThen D :: Γ) C with
        | some t => return some (G4cTm.impLOr h t)
        | none => return none
    | .ifThen (.ifThen A B) D, h => do
        match ← proveM V (B.ifThen D :: Γ) (A.ifThen B) with
        | none => return none
        | some t₁ => match ← proveM V (D :: Γ) C with
          | none => return none
          | some t₂ => return some (G4cTm.impLImp h t₁ t₂)
    | .ifThen (.somehow A) B, h => do
        let b1 ← (do
          match ← proveM V Γ A with
          | none => return (none : Option (G4cTm Γ C))
          | some t₁ => match ← proveM V (B :: Γ) C with
            | none => return none
            | some t₂ => return some (G4cTm.impLLax h t₁ t₂))
        match b1 with
        | some t => return some t
        | none => firstSomeM Γ.attach (fun ⟨X, hXf⟩ =>
            match X, hXf with
            | .somehow x, hX => do
                match ← proveM V (x :: Γ) (somehow A) with
                | none => return none
                | some t₁ => match ← proveM V (B :: Γ) C with
                  | none => return none
                  | some t₂ => return some (G4cTm.impLLaxLax h hX t₁ t₂)
            | _, _ => pure none)
    | _, _ => pure none)

end

/-- Search a sequent from scratch (with a fresh failure memo).  `some t` is a
kernel-checkable derivation.  `none` means the search space was exhausted; by
the argument in `proveM`'s docstring that is intended to mean "not
G4c-derivable", but it is **untrusted** — `proveM` is `partial`, so nothing
about it is proved — and is not a refutation.  Until 2026-10-19 the failure
memo also returned `none` on some derivable sequents; earlier `none` verdicts
are not evidence of underivability. -/
def G4cTm.find (Γ : List PLLFormula) (C : PLLFormula) : Option (G4cTm Γ C) :=
  (proveM [] Γ C).run' {}

/-! ## The node-budgeted searcher

`proveBounded` mirrors `proveM` rule for rule (same rules, same try order,
same dependency-aware failure memo — **keep the two in sync**), but threads a
global node budget through the search: the `Nat` in the state is the
remaining budget, and failure *preserves* it, so sequential alternatives
(`<|>`, `firstM`) draw from one shared pool.  One unit is spent per
`proveBounded` entry, i.e. per visited sequent (loop-check revisits and memo
hits included, since the `canon`-key lookup is real work too).

Two notes, both *by construction* rather than as theorems (`partial`
definitions are opaque to Lean's logic, so no lemma can relate `proveM` and
`proveBounded` — the trust story is unaffected, because any emitted term
inhabits `G4cTm Γ C` and is checked by the kernel):

* the budget only ever truncates the search, so `none` under an exhausted
  budget means "not settled within the budget" — never underivability;
* the budget is inert until it reaches `0`, so a run that finishes with
  budget to spare made exactly the same rule attempts, memo entries and memo
  reuses, in the same order, as the fuel-free `proveM`.

Since both searchers are `partial`, neither reduces in the kernel; discovery
stays evaluation-side (`#eval` / `#guard`), and found terms are pinned and
kernel-checked as usual.  (A structurally recursive searcher — recursion on
the budget itself — would additionally reduce in the kernel on small
budgets, but it would have to share its budget across siblings through an
explicit work-list machine; that is a different engine, not a variant of
this one.) -/

/-- The budget-threading monad for `proveBounded`: an `Option` computation
over a state of remaining node budget PLUS the memo state of `proveM` — the
full UI-track composition (budget × memo × canonical key, the `g4bM`
shape).  Failure returns the *remaining* state, so alternation continues
from wherever the failed branch left off and memoised failures accumulate
across branches. -/
abbrev BudgetM (α : Type) : Type := OptionT (StateM (Nat × MemoState)) α

instance {α : Type} : Inhabited (BudgetM α) := ⟨failure⟩

/-- Read the whole state (budget, memo state). -/
@[inline] def BudgetM.getState : BudgetM (Nat × MemoState) :=
  OptionT.lift (get : StateM (Nat × MemoState) (Nat × MemoState))

/-- Update the memo state, leaving the budget alone. -/
@[inline] def BudgetM.modifyMemo (f : MemoState → MemoState) : BudgetM Unit :=
  OptionT.lift (modify (fun s => (s.1, f s.2)) : StateM (Nat × MemoState) Unit)

/-- Spend one unit of search budget; fail when the pool is dry.  This is the
single point where the budget is consumed or checked.  Exhaustion is
STICKY — failing at `0` leaves the pool at `0` and nothing refills it — so
a subgoal failure observed with budget still remaining involved no
truncation anywhere inside it. -/
@[inline] def BudgetM.spendNode : BudgetM Unit := do
  match (← BudgetM.getState).1 with
  | 0 => failure
  | f + 1 =>
      OptionT.lift (modify (fun s => (f, s.2)) : StateM (Nat × MemoState) Unit)

mutual

/-- Node-budgeted mirror of `proveM` (see the section header, and `proveM`'s
docstring for the failure memo).  Untrusted `partial` code, same as `proveM`;
success is self-certifying. -/
partial def proveBounded (V : List SeqKey)
    (Γ : List PLLFormula) (C : PLLFormula) : BudgetM (G4cTm Γ C) := do
  BudgetM.spendNode
  let key := ckey Γ C
  if key ∈ V then
    BudgetM.modifyMemo (·.note [key]); failure
  else match (← BudgetM.getState).2.reusable V key with
  | some D => BudgetM.modifyMemo (·.note D); failure
  | none =>
    let saved := (← BudgetM.getState).2.cuts
    BudgetM.modifyMemo fun m => { m with cuts := [] }
    let r ← OptionT.lift (OptionT.run (
      (if h : falsePLL ∈ Γ then pure (G4cTm.botL h) else failure)
      <|> proveRightBounded (key :: V) Γ C
      <|> proveLeftBounded (key :: V) Γ C))
    match r with
    | some t => BudgetM.modifyMemo (fun m => { m with cuts := saved }); pure t
    | none =>
        -- budget remaining ⟹ the failure was truncation-free (sticky
        -- exhaustion): memoise it with its dependency set, as `proveM` does.
        -- A `none` at exhausted budget is a mere truncation and is NOT
        -- memoised (the whole run then reads as unknown anyway).
        let s ← BudgetM.getState
        BudgetM.modifyMemo (·.fail V key saved (record := s.1 > 0))
        failure

/-- Right rules, budgeted (mirror of `proveRightM`). -/
partial def proveRightBounded (V : List SeqKey)
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

/-- Left rules, budgeted (mirror of `proveLeftM`). -/
partial def proveLeftBounded (V : List SeqKey)
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
  same `none` that `find` returns — intended to mean "not G4c-derivable"
  (the argument in `proveM`'s docstring), but **untrusted**, since the
  searcher is `partial` and nothing about it is proved: not a refutation;
* `(none, 0)`     — the budget ran out (or the search finished exactly as
  it hit `0` — indistinguishable, so read it conservatively): honest
  **unknown**, never a negative verdict.

Until 2026-10-19 the failure memo could also give `(none, k + 1)` on
derivable sequents; such earlier verdicts are not evidence of
underivability.  `budget - remaining` is the number of nodes visited — a free
profiler for tuning budgets in probe sessions. -/
def G4cTm.findBounded (budget : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    Option (G4cTm Γ C) × Nat :=
  let (r, s) :=
    Id.run (StateT.run (OptionT.run (proveBounded [] Γ C))
      (budget, ({} : MemoState)))
  (r, s.1)

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
