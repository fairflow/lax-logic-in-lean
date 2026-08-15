/-
# THE TWO-SIDED ENGINE: LJF◯ proves, Reject refutes

The effective link Matthew asked for (2026-08-14 night).  For a cell
`[φ] ⊢? ψ`:

* **proof side** — `TwoSidedLink.searchProves`: the LJF◯ focused
  searcher on the bridge's polarisation, climbed along a fuel ladder.
  A hit is a PLL derivability certificate (`laxND_of_searchProves`,
  choice-free).
* **refutation side** — a countermodel in the BUILT class (rooted
  `Rᵢ`-tree, fallible leaves), confirmed by `Reject.certifies`.  A hit
  is an underivability certificate (`not_laxND_of_certifies`).
* neither at budget → `flag`, never dropped.

`two_sided_disjoint` (kernel-checked) says the two sides can never
both fire, so a conflict observed at runtime would be a build defect,
not a mathematical possibility.

## Modes

    twosided corpus [maxfuel]   -- the 462 ρ-order cells vs PLL ground
                                   truth computed the OLD way (battery +
                                   G4c oracle); agreement + cost table
    twosided flags n [fuels…]   -- the two order flags: BUILT trees on
                                   n worlds (the battery stops at 5) +
                                   deep LJF◯

Model source for the corpus run: the existing confluent battery
FILTERED by `Reject.BuiltB` — measuring how much refutation power the
canonical class retains on ≤5 worlds.  The flags run GENERATES the
class directly at 6–7 worlds, where full-frame enumeration is
infeasible but trees are cheap: that is exactly the economy T2 bought.

NEW FILE; nothing existing is edited.
-/
import wip.rho_order
import wip.ljfo_link

open PLLND PLLND.RNC.CFX PLLFormula LJFO Rewrite TwoSidedLink

namespace TwoSided

abbrev F := PLLFormula

open RhoOrder (rhos rhoF rhoN n)

/-! ## The Built subbattery -/

def subBattery : Array FinCM :=
  (battery ++ framesRooted5.toArray).filter Reject.BuiltB

/-! ## The corpus run -/

def fuelLadder (maxF : Nat) : List Nat :=
  [8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 56, 64].filter (· ≤ maxF)

def corpusRun (maxF : Nat) : IO Unit := do
  let out ← IO.getStdout
  let bat := battery ++ framesRooted5.toArray
  let sub := subBattery
  IO.println "=== TWO-SIDED ENGINE: LJF◯ proves / Reject refutes — the 462 ρ-order cells, as PLL questions ==="
  IO.println s!"full battery {bat.size} frames; Built subbattery {sub.size} frames; fuel ladder {fuelLadder maxF}"
  out.flush
  -- vectors over both batteries
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  let svecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => sub.map fun M => vecOf M (rhoF i)
  -- ground truth (the OLD machinery): battery separation / plain-PLL oracle
  let mut gtP := 0; let mut gtR := 0; let mut gtF := 0
  -- engine tallies
  let mut agree := 0
  let mut engP := 0; let mut engR := 0; let mut engF := 0
  let mut conflicts := 0
  let mut fuelHist : List (Nat × Nat) := (fuelLadder maxF).map (·, 0)
  let mut lostRefutations : List String := []
  let mut engFlagCells : List String := []
  let mut tOracle := 0; let mut tLJF := 0; let mut tRej := 0
  for i in [0:n] do
    for j in [0:n] do
      if i != j then
        -- ── ground truth, PLL ──
        let t0 ← IO.monoMsNow
        let gt : Option Bool :=  -- some true ⊢ / some false ⊬ / none flag
          match firstSep bat (vecs.getD i #[]) (vecs.getD j #[]) with
          | some _ => some false
          | none =>
              if provedAt 20000 [rhoF i] (rhoF j) then some true
              else if provedAt 100000 [rhoF i] (rhoF j) then some true
              else none
        let t1 ← IO.monoMsNow
        tOracle := tOracle + (t1 - t0)
        match gt with
        | some true => gtP := gtP + 1
        | some false => gtR := gtR + 1
        | none => gtF := gtF + 1
        -- ── engine: LJF◯ ladder ──
        let t2 ← IO.monoMsNow
        let hitF := (fuelLadder maxF).find? fun f => searchProves f [rhoF i] (rhoF j)
        let t3 ← IO.monoMsNow
        tLJF := tLJF + (t3 - t2)
        -- ── engine: Built refutation, certifies-confirmed ──
        let t4 ← IO.monoMsNow
        let refu : Option (Nat × Nat) := Id.run do
          match firstSep sub (svecs.getD i #[]) (svecs.getD j #[]) with
          | some (fi, w) =>
              let M := sub.getD fi default
              if Reject.certifies M w [rhoF i] (rhoF j) then return some (fi, w)
              else return none
          | none => return none
        let t5 ← IO.monoMsNow
        tRej := tRej + (t5 - t4)
        -- ── verdict + audit ──
        match hitF, refu with
        | some f, some _ =>
            conflicts := conflicts + 1
            IO.println s!"  *** CONFLICT at {rhoN i} ⊢ {rhoN j} — IMPOSSIBLE by two_sided_disjoint; build defect"
        | some f, none =>
            engP := engP + 1
            fuelHist := fuelHist.map fun p => if p.1 == f then (p.1, p.2 + 1) else p
            if gt == some false then
              conflicts := conflicts + 1
              IO.println s!"  *** GT-CONFLICT {rhoN i} ⊢ {rhoN j}: engine proves, battery refutes"
            else if gt == some true then agree := agree + 1
        | none, some _ =>
            engR := engR + 1
            if gt == some true then
              conflicts := conflicts + 1
              IO.println s!"  *** GT-CONFLICT {rhoN i} ⊢ {rhoN j}: engine refutes, oracle proves"
            else if gt == some false then agree := agree + 1
        | none, none =>
            engF := engF + 1
            engFlagCells := s!"{rhoN i}⊢{rhoN j}" :: engFlagCells
            if gt == some false then
              lostRefutations := s!"{rhoN i}⊬{rhoN j}" :: lostRefutations
    IO.println s!"  row {rhoN i} done"
    out.flush
  IO.println ""
  IO.println s!"ground truth (old machinery): {gtP} ⊢, {gtR} ⊬, {gtF} flag   [{tOracle} ms]"
  IO.println s!"engine                      : {engP} ⊢, {engR} ⊬, {engF} flag   [LJF◯ {tLJF} ms + Reject {tRej} ms]"
  IO.println s!"agreement on settled cells  : {agree}/{gtP + gtR}"
  IO.println s!"conflicts                   : {conflicts} (each one is a defect; two_sided_disjoint makes real ones impossible)"
  IO.println ""
  IO.println "proof side, minimum fuel histogram:"
  for (f, c) in fuelHist do
    if c > 0 then IO.println s!"  fuel ≤ {f}: {c} cells"
  IO.println ""
  IO.println s!"refutations LOST by restricting the battery to the Built class (≤5 worlds): {lostRefutations.length}"
  IO.println "  (T2 says a Built countermodel EXISTS for each; the bisimilar tree may need"
  IO.println "   more worlds than 5 — these cells are the tree generator's worklist, not losses)"
  for c in lostRefutations.reverse.take 20 do IO.println s!"    {c}"
  IO.println ""
  IO.println s!"engine flags: {engF}"
  IO.println "TWO-SIDED-CORPUS-DONE"

/-! ## The tree generator: the Built class at n worlds, directly -/

/-- Parent vectors `p : Array Nat` with `p[i] < i` for `i ≥ 1`; node 0
is the root. -/
def parentVectors : (k : Nat) → List (Array Nat)
  | 0 => [#[0]]
  | k + 1 => (parentVectors k).flatMap fun p =>
      (List.range (k + 1)).map fun par => p.push par

/-- Strict ancestor pairs of a parent vector (the `ri` list; `riB`
adds the diagonal itself). -/
def ancPairs (p : Array Nat) : List (Nat × Nat) := Id.run do
  let mut acc : List (Nat × Nat) := []
  for i in [1:p.size] do
    let mut a := i
    while a != 0 do
      a := p.getD a 0
      acc := (a, i) :: acc
  return acc

/-- `rm` from a chosen subset of tree edges: `x rm y` iff the tree
path `x → y` uses only chosen edges.  Transitive by construction and
`⊆ ri`. -/
def rmPairs (p : Array Nat) (es : List Nat) : List (Nat × Nat) := Id.run do
  -- es: the child endpoints of the chosen edges
  let mut acc : List (Nat × Nat) := []
  for i in [1:p.size] do
    let mut a := i
    let mut ok := true
    while a != 0 && ok do
      if es.contains a then
        a := p.getD a 0
        acc := (a, i) :: acc
      else ok := false
  return acc

def leaves (p : Array Nat) : List Nat :=
  (List.range p.size).filter fun w =>
    (List.range p.size).all fun v => v == 0 || p.getD v 0 != w

def subsetsOf : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (subsetsOf xs).flatMap fun s => [s, x :: s]

/-- All Built-class frames on `k+1` worlds (closed corpus: no
valuation). -/
def builtFrames (k : Nat) : List FinCM :=
  (parentVectors k).flatMap fun p =>
    let edges := List.range (k + 1) |>.filter (· != 0)
    (subsetsOf edges).flatMap fun es =>
      (subsetsOf (leaves p)).map fun fs =>
        ⟨k + 1, ancPairs p, rmPairs p es, fs, []⟩

/-- Mutual confluence, for labelling a hit's DerivU relevance. -/
def confl (M : FinCM) : Bool :=
  (List.range M.n).all fun x => (List.range M.n).all fun w =>
    (List.range M.n).all fun v =>
      !(M.rmB x w && M.riB x v) ||
        (List.range M.n).any fun u => M.riB w u && M.rmB v u

/-! ## The flags run -/

def flagCells : List (Nat × Nat) := [(12, 15), (20, 10)]

def flagsRun (worlds : Nat) (fuels : List Nat) : IO Unit := do
  let out ← IO.getStdout
  IO.println s!"=== TWO-SIDED ENGINE on the two order flags — Built trees on {worlds} worlds + LJF◯ at fuels {fuels} ==="
  -- deep LJF◯ first (cheap to try, certificate if it lands)
  for (i, j) in flagCells do
    for f in fuels do
      let t0 ← IO.monoMsNow
      let r := searchProves f [rhoF i] (rhoF j)
      let t1 ← IO.monoMsNow
      IO.println s!"  LJF◯ {rhoN i} ⊢ {rhoN j} fuel {f}: {r}  [{t1 - t0} ms]"
      out.flush
      if r then
        IO.println s!"  ⇒ PROVED (PLL): pin with  laxND_of_searchProves (f := {f}) (by decide)"
  -- the tree hunt
  if worlds ≥ 1 then
    let k := worlds - 1
    let edges := (List.range (k + 1)).filter (· != 0)
    let mut checkedB := 0
    let mut hits := 0
    let mut done := 0
    -- STREAMED: never materialise the frame list (the first cut did,
    -- and at 7 worlds that is millions of FinCM records — it broke a
    -- concurrent run via memory pressure; recorded, not repeated)
    for p in parentVectors k do
      let lv := leaves p
      for es in subsetsOf edges do
        for fs in subsetsOf lv do
          let M : FinCM := ⟨k + 1, ancPairs p, rmPairs p es, fs, []⟩
          done := done + 1
          if done % 100000 == 0 then
            IO.println s!"    …{done} frames"; out.flush
          if Reject.BuiltB M then
            checkedB := checkedB + 1
            for (i, j) in flagCells do
              for w in List.range M.n do
                if M.forceB w (rhoF i) && !(M.forceB w (rhoF j)) then
                  if Reject.certifies M w [rhoF i] (rhoF j) then
                    hits := hits + 1
                    let cf := confl M
                    IO.println s!"  HIT {rhoN i} ⊬ {rhoN j} (PLL): frame ri={M.ri} rm={M.rm} fall={M.fall} world {w}, confluent={cf}"
                    IO.println s!"    pin: ¬ Nonempty (LaxND [{pp (rhoF i)}] ({pp (rhoF j)})) := Reject.not_laxND_of_certifies (M := ⟨{M.n}, {M.ri}, {M.rm}, {M.fall}, []⟩) (w := {w}) (by decide)"
                    if cf then
                      IO.println s!"    frame is mutually confluent ⇒ also refutes DerivU: the CATALOGUE flag settles"
                    out.flush
    IO.println s!"  frames streamed: {done}; passing BuiltB: {checkedB} (control: a shortfall is a generator bug)"
    IO.println s!"  certified hits: {hits}"
    if hits == 0 then
      IO.println s!"  no Built countermodel on {worlds} worlds (edge-generated Rm family) — flags STAND at this size (report, never drop)"
  IO.println "TWO-SIDED-FLAGS-DONE"

/-! ## The closing pass — spend more budget on exactly the engine's
flag cells: deep LJF◯ fuel where the oracle proves, generated Built
trees where the battery refutes. -/

def closeRun (worlds maxF : Nat) : IO Unit := do
  let out ← IO.getStdout
  let bat := battery ++ framesRooted5.toArray
  let sub := subBattery
  IO.println s!"=== CLOSING PASS: deep LJF◯ (≤ {maxF}) on unreached proofs, {worlds}-world Built trees on lost refutations ==="
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  let svecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => sub.map fun M => vecOf M (rhoF i)
  -- the worklists, recomputed
  let mut needProof : List (Nat × Nat) := []
  let mut needRefu : List (Nat × Nat) := []
  for i in [0:n] do
    for j in [0:n] do
      if i != j then
        match firstSep bat (vecs.getD i #[]) (vecs.getD j #[]) with
        | some _ =>
            -- gt-refuted; did the subbattery get it?
            let got := match firstSep sub (svecs.getD i #[]) (svecs.getD j #[]) with
              | some (fi, w) => Reject.certifies (sub.getD fi default) w [rhoF i] (rhoF j)
              | none => false
            if !got then needRefu := (i, j) :: needRefu
        | none =>
            if provedAt 20000 [rhoF i] (rhoF j) || provedAt 100000 [rhoF i] (rhoF j) then
              if ((fuelLadder 32).find? fun f => searchProves f [rhoF i] (rhoF j)).isNone then
                needProof := (i, j) :: needProof
  IO.println s!"worklists: {needProof.length} unreached proofs, {needRefu.length} lost refutations"
  out.flush
  -- deep fuel
  let deep := (fuelLadder maxF).filter (· > 32)
  let mut closedP := 0
  for (i, j) in needProof.reverse do
    let t0 ← IO.monoMsNow
    let hit := deep.find? fun f => searchProves f [rhoF i] (rhoF j)
    let t1 ← IO.monoMsNow
    match hit with
    | some f =>
        closedP := closedP + 1
        IO.println s!"  CLOSED-PROOF {rhoN i} ⊢ {rhoN j} at fuel {f}  [{t1 - t0} ms]"
    | none =>
        IO.println s!"  still open (proof side): {rhoN i} ⊢ {rhoN j} at fuel ≤ {maxF}  [{t1 - t0} ms]"
    out.flush
  -- trees
  let k := worlds - 1
  let edges := (List.range (k + 1)).filter (· != 0)
  IO.println s!"  streaming Built frames on {worlds} worlds"
  out.flush
  let mut open_ := needRefu
  let mut closedR := 0
  let mut done := 0
  for p in parentVectors k do
   let lv := leaves p
   for es in subsetsOf edges do
    for fs in subsetsOf lv do
     let M : FinCM := ⟨k + 1, ancPairs p, rmPairs p es, fs, []⟩
     do
      done := done + 1
      if done % 100000 == 0 then
        IO.println s!"    …{done} frames, {open_.length} cells open"; out.flush
      if !open_.isEmpty && Reject.BuiltB M then
      let mut still : List (Nat × Nat) := []
      for (i, j) in open_ do
        let hit := (List.range M.n).find? fun w =>
          M.forceB w (rhoF i) && !(M.forceB w (rhoF j))
        match hit with
        | some w =>
            if Reject.certifies M w [rhoF i] (rhoF j) then
              closedR := closedR + 1
              IO.println s!"  CLOSED-REFUTATION {rhoN i} ⊬ {rhoN j}: {worlds}-world tree ri={M.ri} rm={M.rm} fall={M.fall} world {w} confluent={confl M}"
            else still := (i, j) :: still
        | none => still := (i, j) :: still
      open_ := still
      if closedR > 0 && open_.isEmpty then
        IO.println "  all lost refutations recovered"; out.flush
  IO.println ""
  IO.println s!"closed by deep fuel: {closedP}/{needProof.length};  closed by {worlds}-world trees: {closedR}/{needRefu.length}"
  IO.println s!"still open after the pass: {needProof.length - closedP} proofs, {open_.length} refutations"
  for (i, j) in open_.reverse do IO.println s!"    open refutation: {rhoN i} ⊬ {rhoN j}"
  IO.println "TWO-SIDED-CLOSE-DONE"

def main (args : List String) : IO Unit := do
  match args with
  | "corpus" :: rest =>
      corpusRun ((rest.head?.bind String.toNat?).getD 32)
  | "flags" :: w :: rest =>
      flagsRun (w.toNat!) (rest.filterMap String.toNat?)
  | "close" :: w :: rest =>
      closeRun (w.toNat!) ((rest.head?.bind String.toNat?).getD 64)
  | _ => corpusRun 32

end TwoSided
