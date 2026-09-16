/-
# Verdicts, and the failure log

The distinction this file exists to enforce:

* **not found within bound** — the search did not find a (dis)proof inside
  the `Config` it was given.  A fact about the RUN.
* **no (dis)proof exists** — a fact about the CALCULUS, and a proof of
  incompleteness if the sequent is settled elsewhere.

Spelling those the same way is how a search limitation becomes a claim
about the logic.  `Tools/Search.lean` used to spell the first one
"no-derivation-at-fixpoint", computed from three of the five things that
can truncate a round; measured 2026-08-21, it was wrong on 119 of 119
negative bank results.

## `none_ex` is UNINHABITABLE, on purpose

It carries a proof of `Certified.SearchComplete`, which is a
`def … : Prop` with no proof — OPEN.  So nobody can write down "no
derivation exists" until that statement is proved.  The type enforces
what a docstring could only request.

That is the same device as `RwRule.ok` and `Entry.ok`: put the obligation
in a field, and the unsound record becomes unwritable rather than merely
discouraged.

## The failure log is an asset

Every `none_at` is appended with its engine, its FULL bound, and the
sequent.  Two things fall out:

* **re-run at raised budget is mechanical** — the log IS the frontier
  list, so a flag can never be silently dropped;
* **the incompleteness miner** — a sequent one engine cannot settle that
  another settles by other means is a candidate incompleteness witness.
  It fired for the first time on 2026-08-22: G4c refutes
  `(q8 ∧ q11) ⊃ q15` with a checked 3-world `FinCM` in 0 ms, while
  FRJ(◯) closes cap-free on it and builds nothing.
-/
import Tools.Engines

namespace Verdict

open Engines

/-- Which engine, at which version.  Must name a member of
`Engines.registered`: a result records the engine that produced it, so a
stale engine cannot silently produce a new result. -/
structure EngineId where
  name : String
  version : Nat
  deriving DecidableEq, Repr

def EngineId.ofEngine (e : Engine) : EngineId := ⟨e.name, e.version⟩

def EngineId.registered (i : EngineId) : Bool :=
  Engines.registered.any (fun e => e.name == i.name && e.version == i.version)

/-- The whole `Config`, not a single number: a `none_at` is only useful
if a re-run knows every dimension it can raise. -/
structure Bound where
  rounds : Nat
  jmax : Option Nat      -- `none` = no arity cap (the profile engine)
  pmax : Option Nat
  lamCap : Nat
  maxRS : Nat
  maxIS : Nat
  deriving Repr

def Bound.ofConfig (c : FRJ.Search.Config) : Bound :=
  ⟨c.rounds, some c.jmax, some c.pmax, c.lamCap, c.maxRS, c.maxIS⟩

/-- The profile engine consults no arity cap, so it reports `none` for
both — which is a stronger statement than a large number. -/
def Bound.ofConfigProf (c : FRJ.Search.Config) : Bound :=
  ⟨c.rounds, none, none, c.lamCap, c.maxRS, c.maxIS⟩

def Bound.render (b : Bound) : String :=
  let a (o : Option Nat) := match o with | none => "UNCAPPED" | some k => toString k
  s!"rounds={b.rounds} jmax={a b.jmax} pmax={a b.pmax} lamCap={b.lamCap} \
maxRS={b.maxRS} maxIS={b.maxIS}"

/-- What a positive answer carries. -/
inductive CertKind where
  /-- a countermodel was CONSTRUCTED (FRJ(◯) `modR`, or a checked `FinCM`) -/
  | countermodel (worlds : Nat)
  /-- a proof term (`G4cTm`, or an LJF◯ derivation at a fuel) -/
  | proof (detail : String)
  deriving Repr

/-- Three outcomes.  The two negatives are DIFFERENT OBJECTS. -/
inductive Answer where
  | found (e : EngineId) (c : CertKind)
  /-- NOT FOUND within `b`.  Never a statement about the sequent. -/
  | none_at (e : EngineId) (b : Bound)
  /-- NO (dis)proof EXISTS in this calculus.
  **Uninhabitable today**: `Certified.SearchComplete` is OPEN, so this
  constructor cannot be applied.  That is the point — it names the
  verdict without permitting it. -/
  | none_ex (e : EngineId) (h : Certified.SearchComplete)

def Answer.render : Answer → String
  | .found e (.countermodel w) => s!"FOUND countermodel ({w} worlds) — {e.name} v{e.version}"
  | .found e (.proof d) => s!"FOUND proof ({d}) — {e.name} v{e.version}"
  | .none_at e b => s!"not-found-within-bound — {e.name} v{e.version} — {b.render}"
  | .none_ex e _ => s!"NO (DIS)PROOF EXISTS — {e.name} v{e.version}"

/-- `none_ex` has no producer, and this records WHY rather than leaving it
to be rediscovered.  Two routes would inhabit it:

* SEMANTIC — `AllMet K G` for every `K` (`FRJ/Saturate.lean`), the
  progress lemma of the per-instance fixpoint.  This is W4 completeness.
* SYNTACTIC — a bound on FRJ(◯)'s join arity in terms of the goal's
  finite subformula universe.  `FRJ/Profile.lean` is a step toward this:
  it proves the arity caps ELIMINABLE, so the profile engine consults no
  arity cap at all.  What remains is `lamCap`, and the subsumption
  layer. -/
def NoneExIsOpen : Prop := Certified.SearchComplete

/-! ## The failure log -/

structure LogEntry where
  goal : String
  answer : Answer

/-- One appended line per result, so a killed run loses nothing and a hit
is replayable without re-running the search. -/
def LogEntry.line (l : LogEntry) : String :=
  s!"{l.goal}\t{l.answer.render}"

def append (path : System.FilePath) (l : LogEntry) : IO Unit := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.append
  h.putStrLn l.line
  h.flush

/-- The frontier: every `none_at` in the log, which is exactly the re-run
list.  A flag cannot be silently dropped because it is data, not a
tally. -/
def frontier (ls : List LogEntry) : List LogEntry :=
  ls.filter (fun l => match l.answer with | .none_at _ _ => true | _ => false)

/-- **The incompleteness miner.**  A goal on which one engine reports
`none_at` (or would close cap-free) while ANOTHER engine `found` a
verdict is a candidate incompleteness witness for the first.

Candidate, not witness: a `none_at` is bounded, so it must first be
re-run to a cap-free closure.  `lake exe frjhard --lamcap=200` is how
that was done for `(q8 ∧ q11) ⊃ q15` on 2026-08-22. -/
def candidates (ls : List LogEntry) : List (String × EngineId × EngineId) :=
  ls.filterMap (fun l =>
    match l.answer with
    | .none_at e _ =>
        match ls.find? (fun m => m.goal == l.goal &&
          (match m.answer with | .found _ _ => true | _ => false)) with
        | some ⟨_, .found e' _⟩ => some (l.goal, e, e')
        | _ => none
    | _ => none)

end Verdict
