/-
# Two engines on the same 462 cells: the G4c-completeness oracle and
the LJF◯ focused searcher

Matthew's ask (2026-08-14): for countermodel and proof search we have
the OLD technique — grounded in completeness for `G4c`, then moved
into an oracle for efficiency — and the NEW one based on LJF.  Run
both on the same corpus and compare.

The corpus is the 22 × 22 order matrix of `wip/rho_order.lean`: 462
ordered pairs of certified-distinct closed-fragment classes, each a
genuine `ρi ⊢ ρj` question.

NEW FILE.  Everything under `LaxLogic/LJF*` is imported READ-ONLY —
another agent is completing that theory concurrently and nothing here
edits it.

## What the two engines are, precisely

* **The oracle** (`PLLND.Search.decide`, via the tier ladder
  `decidePosT`/`escalate`).  Backward search in `G4c`; its verdicts
  are certificates because `G4c` is complete for PLL and the search
  emits a proof term the kernel checks.  It also REFUTES, by emitting
  a countermodel — which is why the matrix has only two flags in 462
  cells: most cells are settled by the battery, not by proving.
* **LJF◯** (`LJFO.LSeq.search`, sound at every fuel by
  `LJFO.search_sound`).  Backward search in the polarised focused
  calculus.  Focusing is a search-space discipline: it removes the
  don't-care nondeterminism that makes the unfocused space blow up.

## The asymmetry that governs the comparison, stated up front

`LJFO.search_sound` yields an LJF◯ derivation — a derivation in the
FOCUSED calculus.  Getting from there to `PLLND.LaxND` needs
focalization for PLL, and `docs/ljfo-fidelity.md` §5 records that as
**OPEN**: the erasure bridge exists for the ◯-free calculus `LJF`
(`LaxLogic/LJFComplete.lean`, `sound`/`focalization`) but NOT for
LJF◯.  So:

* an LJF◯ `true` is a certificate **for LJF◯**, and only a
  CONJECTURE for PLL;
* an LJF◯ `false` at fuel `n` is not a refutation at all — search is
  fuel-bounded, so `false` means "not found at this depth".

That is not a defect of the engine; it is the missing half of a
bridge someone is building right now. Until it lands, LJF◯ can be
used here as a CROSS-CHECK (does it agree with the oracle?) and as a
COST comparison, never as a source of PLL results. This file reports
it that way, and any disagreement is a flag on the pair, not a
verdict against either engine.

## Modes

    rhoengines pol      -- the polarisation and its round-trip check
    rhoengines cross    -- both engines on all 462 cells
-/
import LaxLogic.LJFOSearch
import wip.rho_order

open PLLND PLLND.RNC PLLND.RNC.CFX PLLFormula
open LJFO

namespace RhoEngines

abbrev F := PLLFormula

/-! ## Polarisation

The standard assignment: `∨` and atoms and `⊥` positive, `⊃`, `∧`,
`◯` negative, with shifts where the syntax forces one.  `◯` takes a
positive body, so its argument is shifted down. -/

def polN : F → Neg
  | .prop a => .up (.atom a)
  | .falsePLL => .up .fls
  | .or a b => .up (.or (.down (polN a)) (.down (polN b)))
  | .and a b => .and (polN a) (polN b)
  | .ifThen a b => .imp (.down (polN a)) (polN b)
  | .somehow a => .circ (.down (polN a))

/-! ## Erasure, and the round trip

`erN`/`erP` are the erasure of `wip/ljfo_crosscheck.lean` (namespace
`X`), restated here so this file does not depend on that probe.  The
round trip is what makes the polarisation trustworthy: it says the
sequent handed to LJF◯ is a faithful rendering of the PLL cell, not a
different question. -/

mutual
def erP : Pos → F
  | .atom a => .prop a
  | .fls => .falsePLL
  | .or P Q => .or (erP P) (erP Q)
  | .down M => erN M
def erN : Neg → F
  | .up P => erP P
  | .imp Q N => .ifThen (erP Q) (erN N)
  | .and M N => .and (erN M) (erN N)
  | .circ P => .somehow (erP P)
end

/-- **The polarisation is faithful**: erasing it gives the formula
back, on the nose. -/
theorem erN_polN : ∀ φ : F, erN (polN φ) = φ := by
  intro φ
  induction φ with
  | prop a => rfl
  | falsePLL => rfl
  | and a b iha ihb => simp [polN, erN, iha, ihb]
  | or a b iha ihb => simp [polN, erN, erP, iha, ihb]
  | ifThen a b iha ihb => simp [polN, erN, erP, iha, ihb]
  | somehow a iha => simp [polN, erN, erP, iha]

/-- info: 'RhoEngines.erN_polN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms erN_polN

/-- The cell `φ ⊢ ψ` as an LJF◯ sequent. -/
def cellSeq (φ ψ : F) : LSeq := .inv [polN φ] [] .tru (polN ψ)

/-! ## The runs -/

open RhoOrder (rhos rhoF rhoN n discovered)

def polReport : IO Unit := do
  IO.println "=== polarisation: round-trip check on the 22 representatives ==="
  let mut ok := 0
  for i in [0:n] do
    if erN (polN (rhoF i)) == rhoF i then ok := ok + 1
    else IO.println s!"  ROUND-TRIP FAILS at {rhoN i}"
  IO.println s!"round trip: {ok}/{n} (and proved in general: erN_polN)"
  for i in [0:n] do
    IO.println s!"  {rhoN i}: sizeNeg {sizeNeg (polN (rhoF i))}, crank {crankL (rhoF i)}"

/-- The oracle's verdict on a cell, re-derived here so the two engines
are compared on exactly the same question. -/
inductive OVerd where | yes | no | flag
deriving DecidableEq

def OVerd.str : OVerd → String
  | .yes => "⊢" | .no => "⊬" | .flag => "?"

/-- The comparison, done the right way round.

Two corrections to the naive version:

* **LJF◯ fuel is derivation DEPTH, not a node budget.**  Comparing
  "fuel 16" with "budget 20000 nodes" is a category error — they are
  not the same currency.  `ρ3 ⊢ ρ4` is one ∨-introduction and still
  needs fuel 20, because the inversion phases that precede the focus
  each consume a level.  Cost is therefore compared in WALL CLOCK,
  and depth is reported separately as the structural quantity it is.
* **Only the oracle's 158 PROVED cells are run.**  LJF◯ cannot refute
  — a `false` is "not found at this depth" and says nothing — so
  scoring it on the 302 refuted cells would be measuring nothing.
  The question worth asking is: of the derivations the oracle
  certifies, which does the focused search reach, and at what depth?
-/
def crossRun (fuels : List Nat) : IO Unit := do
  let out ← IO.getStdout
  let bat := battery ++ framesRooted5.toArray
  IO.println "=== the two engines on the 462 order cells ==="
  IO.println s!"battery: {bat.size} confluent frames; LJF◯ depth ladder: {fuels}"
  out.flush
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  -- Phase 1: the oracle settles the matrix.
  let mut proved : List (Nat × Nat) := []
  let mut oNo := 0
  let mut oFlag := 0
  let t0 ← IO.monoMsNow
  for i in [0:n] do
    for j in [0:n] do
      if i != j then
        match firstSep bat (vecs.getD i #[]) (vecs.getD j #[]) with
        | some _ => oNo := oNo + 1
        | none =>
          match decidePosT 4 (rhoF i) (rhoF j) with
          | .proved _ => proved := (i, j) :: proved
          | _ => match escalate (rhoF i) (rhoF j) with
                 | some _ => proved := (i, j) :: proved
                 | none => oFlag := oFlag + 1
  let t1 ← IO.monoMsNow
  let provedL := proved.reverse
  IO.println s!"oracle: {provedL.length} derivable, {oNo} refuted by countermodel, {oFlag} flags  [{t1 - t0} ms]"
  IO.println "  (the oracle both proves AND refutes — the refutations are why only two cells are left open)"
  out.flush
  -- Phase 2: LJF◯ on exactly those cells, minimum depth reached.
  IO.println ""
  IO.println "LJF◯ on the oracle's derivable cells — minimum depth at which each is found:"
  let mut reached := 0
  let mut depths : List (Nat × Nat × Nat) := []
  let mut missed : List String := []
  let t2 ← IO.monoMsNow
  for (i, j) in provedL do
    let mut got : Option Nat := none
    for f in fuels do
      if got.isNone then
        if LSeq.search f (cellSeq (rhoF i) (rhoF j)) then got := some f
    match got with
    | some f => reached := reached + 1; depths := (i, j, f) :: depths
    | none => missed := s!"{rhoN i} ⊢ {rhoN j}" :: missed
  let t3 ← IO.monoMsNow
  IO.println s!"reached: {reached}/{provedL.length} within depth {fuels.max?.getD 0}  [{t3 - t2} ms]"
  -- depth histogram
  for f in fuels do
    let c := (depths.filter fun d => d.2.2 == f).length
    if c > 0 then IO.println s!"  depth ≤ {f}: {c} cells"
  if !missed.isEmpty then
    IO.println s!"  not reached at depth {fuels.max?.getD 0}: {missed.length}"
    for m in missed.reverse.take 15 do IO.println s!"    {m}"
  -- Phase 3: the soundness cross-check that actually matters.
  IO.println ""
  IO.println "cross-check: does LJF◯ derive anything the oracle REFUTES?"
  let mut conflicts : List String := []
  for i in [0:n] do
    for j in [0:n] do
      if i != j then
        match firstSep bat (vecs.getD i #[]) (vecs.getD j #[]) with
        | some _ =>
            if fuels.any (fun f => LSeq.search f (cellSeq (rhoF i) (rhoF j))) then
              conflicts := s!"{rhoN i} ⊢ {rhoN j}" :: conflicts
        | none => pure ()
  if conflicts.isEmpty then
    IO.println s!"  NO — 0 conflicts over {oNo} certified countermodels."
    IO.println "  The polarisation and both engines agree everywhere the question is settled."
  else
    IO.println s!"  *** {conflicts.length} CONFLICTS — a certified countermodel against an LJF◯ derivation."
    IO.println "  *** Either the polarisation is wrong or one engine is unsound.  STOP and diagnose."
    for c in conflicts.reverse do IO.println s!"    {c}"
  IO.println ""
  IO.println s!"cost over the same corpus: oracle {t1 - t0} ms (462 cells, proving AND refuting)"
  IO.println s!"                           LJF◯  {t3 - t2} ms ({provedL.length} cells, proving only)"
  IO.println "REMINDER: an LJF◯ success certifies LJF◯ only — focalization for PLL is OPEN"
  IO.println "(docs/ljfo-fidelity.md §5), so these derivations do not yet transfer to PLL."
  IO.println "RHO-ENGINES-DONE"

/-- Single-cell trace: the ladder of fuels with a time for each.  A
comparison that reports "engine B missed this" is worthless unless the
cell is inspected — `ρ3 ⊢ ρ4` is one ∨-introduction, so a miss there
is a harness fault, not an engine limitation. -/
def cellRun (i j : Nat) (fuels : List Nat) : IO Unit := do
  let out ← IO.getStdout
  IO.println s!"cell {rhoN i} ⊢ {rhoN j}"
  IO.println s!"  hypothesis (erased): {pp (rhoF i)}"
  IO.println s!"  goal       (erased): {pp (rhoF j)}"
  IO.println s!"  sizeNeg: hyp {sizeNeg (polN (rhoF i))}, goal {sizeNeg (polN (rhoF j))}"
  let s := cellSeq (rhoF i) (rhoF j)
  IO.println s!"  immediate successor sets: {(LSeq.succs s).length}"
  out.flush
  for f in fuels do
    let t0 ← IO.monoMsNow
    let r := LSeq.search f s
    let t1 ← IO.monoMsNow
    IO.println s!"  fuel {f}: {r}  [{t1 - t0} ms]"
    out.flush

def main (args : List String) : IO Unit := do
  match args with
  | ["cell", a, b] =>
      cellRun (a.toNat!) (b.toNat!) [2,4,6,8,10,12,14,16,18,20,22,24]
  | ["pol"] => polReport
  | "cross" :: rest =>
      let fs := rest.filterMap String.toNat?
      crossRun (if fs.isEmpty then [10, 16, 20, 24, 28, 32] else fs)
  | _ => do polReport; IO.println ""; crossRun [10, 16, 20, 24, 28, 32]

end RhoEngines
