/-
# The catalogue-wide PLL cover sweep (`lake exe rhocover`)

Item 2 of the order campaign (2026-08-24): mechanise what the ρ6/ρ12
worked example did by hand, for every candidate cover edge of the
22-class ρ-catalogue at once.

For each ordered pair the PLL status is computed by the standing
machinery — confluent-battery separation for `⊬` (sound:
`not_derivU_of_checkConf` + `Deriv ⊆ DerivU`), the G4c oracle AND the
LJF◯ ladder for `⊢` (sound: `proved_sound` / `laxND_of_searchProves`;
the ladder reaches the 31 cells the oracle misses at budget 10⁵).
Then every strict pair `a < b` is classified against the scope:

* **COVER**   — every `c` in the scope is EXCLUDED as an interposer
  (`a ⊬ c`, or `c ⊢ a`, or `c ⊬ b`, or `b ⊢ c` — each a settled cell):
  `a ⋖[scope] b` holds, and every conjunct is certificate-backed.
* **BLOCKED** — some `c` PROVABLY interposes (`a < c ∧ c < b`): the
  candidate edge is refuted, with the witness printed.
* **OPEN**    — neither; the undecided cells are printed as frontier
  members, never dropped.  With the 2 standing flag cells
  (`ρ12 ⊢? ρ15`, `ρ20 ⊢? ρ10`) these are the only possible source.

The classification is a COMPUTED VIEW over engine verdicts — the
banked kernel certificates are the facts; this tool says which cover
theorems are within reach and exactly which cells block the rest.

Control: the worked example must come out BLOCKED by ρ9 (the kernel
theorem `RNDB.not_covers_rho6_rho12`); the tool refuses to print a
summary if it does not.
-/
import wip.two_sided
import RNDB.DB
import wip.frjv_consequences

open PLLND PLLND.RNC.CFX PLLFormula LJFO Rewrite TwoSidedLink RhoOrder

namespace RhoCover

/-- `some true` = ⊢ certified, `some false` = ⊬ certified, `none` = open. -/
abbrev Status := Option Bool

def statusMat (maxF : Nat) : IO (Array (Array Status)) := do
  let bat := battery ++ framesRooted5.toArray
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  let mut mat : Array (Array Status) := #[]
  for i in [0:n] do
    let mut row : Array Status := #[]
    for j in [0:n] do
      if i == j then
        row := row.push (some true)
      else
        let s : Status :=
          match firstSep bat (vecs.getD i #[]) (vecs.getD j #[]) with
          | some _ => some false
          | none =>
              if provedAt 20000 [rhoF i] (rhoF j) then some true
              else if provedAt 100000 [rhoF i] (rhoF j) then some true
              else if (TwoSided.fuelLadder maxF).any
                       (fun f => searchProves f [rhoF i] (rhoF j)) then some true
              else none
        row := row.push s
    mat := mat.push row
  return mat

/-- `a < b` certified: `a ⊢ b` and `b ⊬ a`. -/
def lt (mat : Array (Array Status)) (a b : Nat) : Bool :=
  let g := fun x y => (mat.getD x #[]).getD y none
  a != b && g a b == some true && g b a == some false

/-- `c` is EXCLUDED as an interposer of `(a, b)` when one conjunct of
`a < c ∧ c < b` is refuted by a settled cell. -/
def excluded (mat : Array (Array Status)) (a b c : Nat) : Bool :=
  let g := fun x y => mat.getD x #[] |>.getD y none
  g a c == some false || g c a == some true       -- ¬(a < c)
  || g c b == some false || g b c == some true    -- ¬(c < b)

/-- The cells still needed to settle `c`'s interposition. -/
def needed (mat : Array (Array Status)) (a b c : Nat) : List String :=
  let g := fun x y => mat.getD x #[] |>.getD y none
  (if g a c == none then [s!"ρ{a} ⊢? ρ{c}"] else [])
  ++ (if g c a == none then [s!"ρ{c} ⊢? ρ{a}"] else [])
  ++ (if g c b == none then [s!"ρ{c} ⊢? ρ{b}"] else [])
  ++ (if g b c == none then [s!"ρ{b} ⊢? ρ{c}"] else [])

/-- `emit` mode: generate `Certified/RhoSeparations.lean` source — one
`¬ ConfluentU.DerivU` theorem per battery-separable ⊬ cell the database
does NOT yet cover, each `by decide`-checkable, plus its PLL transfer
and its `Entry`.  Output goes to stdout; the wrapper splits it. -/
def emitMode : IO Unit := do
  let bat := battery ++ framesRooted5.toArray
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  let idx : PLLFormula → Option Nat := fun φ =>
    (List.range n).find? (fun i => rhoF i == φ)
  let mut banked : List (Nat × Nat) := []
  for e in RNDB.allEntries do
    if e.claim.rel == RNDB.Rel.nle then
      match idx e.claim.lhs, idx e.claim.rhs with
      | some i, some j => banked := (i, j) :: banked
      | _, _ => pure ()
  let mut count := 0
  for i in [0:n] do
    for j in [0:n] do
      if i != j && !banked.contains (i, j) then
        match firstSep bat (vecs.getD i #[]) (vecs.getD j #[]) with
        | some (fi, w) =>
            let M := bat.getD fi default
            count := count + 1
            IO.println s!"THM|/-- `ρ{i} ⊬ᵤ ρ{j}` (PCLL): battery separation, frame {fi}, world {w}. -/"
            IO.println s!"THM|theorem sepU_{i}_{j} : ¬ PLLND.ConfluentU.DerivU [RhoOrder.rhoF {i}] (RhoOrder.rhoF {j}) :="
            IO.println s!"THM|  PLLND.RNC.not_derivU_of_checkConf (M := {PLLND.Search.srcOfCM M}) (w := {w}) (by decide) (by decide)"
            IO.println s!"THM|"
            IO.println s!"THM|theorem rho_{i}_nle_{j} : ¬ PLLND.SemUI.Deriv [RhoOrder.rhoF {i}] (RhoOrder.rhoF {j}) :="
            IO.println s!"THM|  nle_of_nleU sepU_{i}_{j}"
            IO.println s!"THM|"
            IO.println s!"ENT|def nle_{i}_{j} : Entry := sepEntry \"sep-{count}\" {i} {j} {M.n} (by decide) RhoSeps.rho_{i}_nle_{j}"
        | none => pure ()
  IO.println s!"EMIT-COUNT {count}"
  IO.println "RHOCOVER-DONE"

/-- The candidate formulas the cover sweep's lattice failures predict:
each is a join/meet the Lindenbaum order MUST contain but the 22-class
catalogue lacks a home for.  `probe` orders each against the catalogue
(and against the other candidates): a `k` with both directions ⊢
identifies it with class `ρk`; no such `k` = a NEW class. -/
def candidates : List (String × PLLFormula) :=
  [ ("ρ9∨ρ19",      .or (rhoF 9) (rhoF 19))
  , ("ρ18∨ρ20",     .or (rhoF 18) (rhoF 20))
  , ("ρ5∨ρ19",      .or (rhoF 5) (rhoF 19))
  , ("ρ6∨ρ19",      .or (rhoF 6) (rhoF 19))
  , ("ρ7∨ρ13",      .or (rhoF 7) (rhoF 13))
  , ("ρ9∨ρ13",      .or (rhoF 9) (rhoF 13))
  , ("ρ12∨ρ18",     .or (rhoF 12) (rhoF 18))
  , ("ρ12∨ρ18∨ρ20", .or (rhoF 12) (.or (rhoF 18) (rhoF 20)))
  , ("ρ10∧ρ20",     .and (rhoF 10) (rhoF 20))
  , ("ρ10∧ρ21",     .and (rhoF 10) (rhoF 21))
  , ("ρ12∧ρ15",     .and (rhoF 12) (rhoF 15))
  , ("ρ15∧ρ21",     .and (rhoF 15) (rhoF 21)) ]

/-- Three-valued conjunction over a list of statuses. -/
def andS (l : List Status) : Status :=
  if l.any (· == some false) then some false
  else if l.all (· == some true) then some true
  else none

def probeMode (maxF : Nat) : IO Unit := do
  let bat := battery ++ framesRooted5.toArray
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  -- candidate decompositions: (name, formula, join-of, meet-of)
  let cands : List (String × PLLFormula × List Nat × List Nat) :=
    [ ("ρ9∨ρ19",      .or (rhoF 9) (rhoF 19),                [9, 19],      [])
    , ("ρ18∨ρ20",     .or (rhoF 18) (rhoF 20),               [18, 20],     [])
    , ("ρ5∨ρ19",      .or (rhoF 5) (rhoF 19),                [5, 19],      [])
    , ("ρ6∨ρ19",      .or (rhoF 6) (rhoF 19),                [6, 19],      [])
    , ("ρ7∨ρ13",      .or (rhoF 7) (rhoF 13),                [7, 13],      [])
    , ("ρ9∨ρ13",      .or (rhoF 9) (rhoF 13),                [9, 13],      [])
    , ("ρ12∨ρ18",     .or (rhoF 12) (rhoF 18),               [12, 18],     [])
    , ("ρ12∨ρ18∨ρ20", .or (rhoF 12) (.or (rhoF 18) (rhoF 20)), [12, 18, 20], [])
    , ("ρ10∧ρ20",     .and (rhoF 10) (rhoF 20),              [],           [10, 20])
    , ("ρ10∧ρ21",     .and (rhoF 10) (rhoF 21),              [],           [10, 21])
    , ("ρ12∧ρ15",     .and (rhoF 12) (rhoF 15),              [],           [12, 15])
    , ("ρ15∧ρ21",     .and (rhoF 15) (rhoF 21),              [],           [15, 21])
    -- round 2 (2026-08-25): the remaining hub joins (every node with ≥2
    -- upper covers spawns a cube of joins; these are its unprobed
    -- vertices), the co-hub meets, and the ◯-shift generators.
    , ("ρ9∨ρ17",      .or (rhoF 9) (rhoF 17),                [9, 17],      [])
    , ("ρ9∨ρ13∨ρ17",  .or (rhoF 9) (.or (rhoF 13) (rhoF 17)), [9, 13, 17], [])
    , ("ρ9∨ρ16",      .or (rhoF 9) (rhoF 16),                [9, 16],      [])
    , ("ρ16∨ρ19",     .or (rhoF 16) (rhoF 19),               [16, 19],     [])
    , ("ρ9∨ρ16∨ρ19",  .or (rhoF 9) (.or (rhoF 16) (rhoF 19)), [9, 16, 19], [])
    , ("ρ11∨ρ12",     .or (rhoF 11) (rhoF 12),               [11, 12],     [])
    , ("ρ16∨ρ17",     .or (rhoF 16) (rhoF 17),               [16, 17],     [])
    , ("ρ8∨ρ18",      .or (rhoF 8) (rhoF 18),                [8, 18],      [])
    , ("ρ11∨ρ18",     .or (rhoF 11) (rhoF 18),               [11, 18],     [])
    , ("ρ10∨ρ15",     .or (rhoF 10) (rhoF 15),               [10, 15],     [])
    , ("ρ8∨ρ20",      .or (rhoF 8) (rhoF 20),                [8, 20],      [])
    , ("ρ6∧ρ7",       .and (rhoF 6) (rhoF 7),                [],           [6, 7])
    , ("ρ16∧ρ19",     .and (rhoF 16) (rhoF 19),              [],           [16, 19])
    , ("ρ13∧ρ17",     .and (rhoF 13) (rhoF 17),              [],           [13, 17])
    , ("ρ9∧ρ13",      .and (rhoF 9) (rhoF 13),               [],           [9, 13])
    , ("ρ7∧ρ14",      .and (rhoF 7) (rhoF 14),               [],           [7, 14])
    , ("ρ6∧ρ14",      .and (rhoF 6) (rhoF 14),               [],           [6, 14])
    , ("ρ12∧ρ20",     .and (rhoF 12) (rhoF 20),              [],           [12, 20])
    , ("ρ8∧ρ18",      .and (rhoF 8) (rhoF 18),               [],           [8, 18])
    , ("◯ρ4",         .somehow (rhoF 4),                     [],           [])
    , ("◯ρ5",         .somehow (rhoF 5),                     [],           [])
    , ("◯ρ6",         .somehow (rhoF 6),                     [],           [])
    , ("◯ρ8",         .somehow (rhoF 8),                     [],           [])
    , ("◯ρ9",         .somehow (rhoF 9),                     [],           [])
    , ("◯ρ11",        .somehow (rhoF 11),                    [],           []) ]
  let cvecs : Array (Array (Array Bool)) :=
    cands.toArray.map fun (_, X, _, _) => bat.map fun M => vecOf M X
  let out ← IO.getStdout
  -- the settled 22-matrix, with the DB overlay
  IO.println "building the 22-matrix (with DB overlay)…"; out.flush
  let mat0 ← statusMat maxF
  let idx : PLLFormula → Option Nat := fun φ =>
    (List.range n).find? (fun i => rhoF i == φ)
  let mut mat := mat0
  for e in RNDB.allEntries do
    if e.claim.rel == RNDB.Rel.nle then
      match idx e.claim.lhs, idx e.claim.rhs with
      | some i, some j =>
          if (mat.getD i #[]).getD j none == none then
            mat := mat.set! i ((mat.getD i #[]).set! j (some false))
      | _, _ => pure ()
  let g := fun (x y : Nat) => (mat.getD x #[]).getD y none
  -- residual single cell by search, X → Y (used only where laws are
  -- silent).  MODEST budgets on purpose: a residual cell that resists
  -- them is FLAGGED `?` and listed, never ground at — the G4c oracle
  -- at 10⁵ on a composite goal is where the first two probe runs died.
  let search := fun (tag : String) (vX : Array (Array Bool)) (X : PLLFormula)
                    (vY : Array (Array Bool)) (Y : PLLFormula) => do
    match firstSep bat vX vY with
    | some _ => pure (some false)
    | none =>
        IO.println s!"  residual search: {tag}"; (← IO.getStdout).flush
        if provedAt 20000 [X] Y then pure (some true)
        else if (TwoSided.fuelLadder (min maxF 24)).any
                  (fun f => searchProves f [X] Y) then pure (some true)
        else pure none
  IO.println s!"=== catalogue-extension probe: {cands.length} candidates vs the 22 (lattice laws first, search residual, LJF◯ ≤ {maxF}) ==="
  out.flush
  let pr := fun (s : Status) => match s with
    | some true => "⊢" | some false => "⊬" | none => "?"
  let mut fwds : Array (Array Status) := #[]
  let mut bwds : Array (Array Status) := #[]
  for ci in [0:cands.length] do
    let (name, X, ors, ands) := cands.getD ci ("", falsePLL, [], [])
    let vX := cvecs.getD ci #[]
    let mut fwd : Array Status := #[]   -- X → ρk
    let mut bwd : Array Status := #[]   -- ρk → X
    for k in [0:n] do
      -- X → ρk
      let f : Status ←
        if !ors.isEmpty then pure (andS (ors.map (g · k)))   -- ⋁S ⊢ k iff ∀a. a ⊢ k
        else if ands.any (fun a => g a k == some true) then pure (some true)  -- A∧B ≤ A ≤ k
        else search s!"{name} → ρ{k}" vX X (vecs.getD k #[]) (rhoF k)
      -- ρk → X
      let b : Status ←
        if !ands.isEmpty then pure (andS (ands.map (g k ·)))  -- k ⊢ ⋀S iff ∀a. k ⊢ a
        else if ors.any (fun a => g k a == some true) then pure (some true)   -- k ≤ A ≤ A∨B
        else search s!"ρ{k} → {name}" (vecs.getD k #[]) (rhoF k) vX X
      fwd := fwd.push f
      bwd := bwd.push b
    fwds := fwds.push fwd
    bwds := bwds.push bwd
    let idents := (List.range n).filter fun k =>
      fwd.getD k none == some true && bwd.getD k none == some true
    let above := (List.range n).filter fun k =>
      bwd.getD k none == some true && fwd.getD k none == some false
    let below := (List.range n).filter fun k =>
      fwd.getD k none == some true && bwd.getD k none == some false
    let openC := (List.range n).filter fun k =>
      fwd.getD k none == none || bwd.getD k none == none
    match idents with
    | [k] => IO.println s!"IDENT {name} ≡ ρ{k}"
    | [] => IO.println s!"NEW   {name}   strictly above {above.map (s!"ρ{·}")}, strictly below {below.map (s!"ρ{·}")}, open cells at {openC.map (s!"ρ{·}")}"
    | ks => IO.println s!"CONTROL FAILED: {name} identified with TWO classes {ks} — catalogue distinctness violated"
    out.flush
  -- candidate × candidate, by the same laws (search residual)
  IO.println ""
  for ci in [0:cands.length] do
    for cj in [0:cands.length] do
      if ci != cj then
        let (ni, X, orsI, andsI) := cands.getD ci ("", falsePLL, [], [])
        let (nj, Y, orsJ, andsJ) := cands.getD cj ("", falsePLL, [], [])
        let d : Status ←
          if !orsI.isEmpty then pure (andS (orsI.map (fun a => (bwds.getD cj #[]).getD a none)))
          else if !andsJ.isEmpty then pure (andS (andsJ.map (fun b => (fwds.getD ci #[]).getD b none)))
          else if orsJ.any (fun b => (fwds.getD ci #[]).getD b none == some true) then pure (some true)
          else if andsI.any (fun a => (bwds.getD cj #[]).getD a none == some true) then pure (some true)
          else search s!"{ni} → {nj}" (cvecs.getD ci #[]) X (cvecs.getD cj #[]) Y
        IO.println s!"CAND {ni} → {nj}: {pr d}"
    out.flush
  IO.println "PROBE-DONE"

/-- `rtable` mode: the operation tables over the ρ-catalogue R (the 22
known distinct classes, open-ended).  For each `ρi ⊙ ρj` (⊙ ∈ {∧,∨,⊃})
and each `◯ρi`, the verdict against R:

* `ρk`  — mutual derivability with class k certified both ways;
* `∉R`  — for EVERY k one direction is certified refuted: the result
  provably lies outside the currently known classes;
* `?`   — neither, at the stated budgets (flagged, never dropped).

Lattice laws first (for ∧/∨ one direction is EXACT from the settled
order matrix), battery separation next, bounded search last.  The
matrix is TOTAL: the last open cell ρ12 ⊢? ρ15 was settled NEGATIVE
through the repaired calculus (`FRJVConsequences.rho12_nle_rho15`,
kernel-pinned; applied as an overlay below). -/
def rtableMode (maxF : Nat) : IO Unit := do
  let bat := battery ++ framesRooted5.toArray
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  let out ← IO.getStdout
  IO.println "building the settled 22-matrix (DB overlay + V-overlay)…"; out.flush
  let mat0 ← statusMat maxF
  let idx : PLLFormula → Option Nat := fun φ =>
    (List.range n).find? (fun i => rhoF i == φ)
  let mut mat := mat0
  for e in RNDB.allEntries do
    if e.claim.rel == RNDB.Rel.nle then
      match idx e.claim.lhs, idx e.claim.rhs with
      | some i, some j =>
          if (mat.getD i #[]).getD j none == none then
            mat := mat.set! i ((mat.getD i #[]).set! j (some false))
      | _, _ => pure ()
  -- V-overlay: the repaired-calculus settlement of the last open cell
  let _ : [rhoF 12] ⊬ rhoF 15 := FRJVConsequences.rho12_nle_rho15
  if (mat.getD 12 #[]).getD 15 none == none then
    IO.println "V-OVERLAY ρ12 ⊬ ρ15  (FRJVConsequences.rho12_nle_rho15)"
    mat := mat.set! 12 ((mat.getD 12 #[]).set! 15 (some false))
  let g := fun (x y : Nat) => (mat.getD x #[]).getD y none
  let opens := (List.range n).flatMap fun i =>
    (List.range n).filter fun j => i != j && g i j == none
  IO.println s!"matrix open cells: {opens.length} (must be 0 for a total table)"
  let search := fun (tag : String) (vX : Array (Array Bool)) (X : PLLFormula)
                    (vY : Array (Array Bool)) (Y : PLLFormula) => do
    match firstSep bat vX vY with
    | some _ => pure (some false)
    | none =>
        IO.println s!"  residual search: {tag}"; (← IO.getStdout).flush
        if provedAt 20000 [X] Y then pure (some true)
        else if (TwoSided.fuelLadder (min maxF 24)).any
                  (fun f => searchProves f [X] Y) then pure (some true)
        else pure none
  -- classify one composite formula against R
  let classify := fun (tag : String) (X : PLLFormula)
                      (fwdLaw bwdLaw : Nat → Status) => do
    let vX : Array (Array Bool) := bat.map fun M => vecOf M X
    let mut fwd : Array Status := #[]
    let mut bwd : Array Status := #[]
    for k in [0:n] do
      let f ← match fwdLaw k with
        | some v => pure (some v)
        | none => search s!"{tag} → ρ{k}" vX X (vecs.getD k #[]) (rhoF k)
      let b ← match bwdLaw k with
        | some v => pure (some v)
        | none => search s!"ρ{k} → {tag}" (vecs.getD k #[]) (rhoF k) vX X
      fwd := fwd.push f
      bwd := bwd.push b
    let ident := (List.range n).find? fun k =>
      fwd.getD k none == some true && bwd.getD k none == some true
    match ident with
    | some k => pure s!"ρ{k}"
    | none =>
        let allExcluded := (List.range n).all fun k =>
          fwd.getD k none == some false || bwd.getD k none == some false
        pure (if allExcluded then "∉R" else "?")
  IO.println "── ∧ table ──"
  for i in [0:n] do
    for j in [i:n] do
      let X := (rhoF i).and (rhoF j)
      -- ρk ⊢ ρi∧ρj  ⟺  ρk ⊢ ρi and ρk ⊢ ρj (EXACT); ρi∧ρj ⊢ ρk sufficient via either conjunct
      let v ← classify s!"ρ{i}∧ρ{j}" X
        (fun k => if g i k == some true || g j k == some true then some true else none)
        (fun k => andS [g k i, g k j])
      IO.println s!"RTAB and {i} {j} = {v}"
    out.flush
  IO.println "── ∨ table ──"
  for i in [0:n] do
    for j in [i:n] do
      let X := (rhoF i).or (rhoF j)
      let v ← classify s!"ρ{i}∨ρ{j}" X
        (fun k => andS [g i k, g j k])
        (fun k => if g k i == some true || g k j == some true then some true else none)
      IO.println s!"RTAB or {i} {j} = {v}"
    out.flush
  IO.println "── ⊃ table ──"
  for i in [0:n] do
    for j in [0:n] do
      let X := (rhoF i).ifThen (rhoF j)
      -- law: ρk ⊢ (ρi ⊃ ρj) is implied by ρk ⊢ ρj; ρi⊃ρj ⊢ ρk implied by... none safe.
      let v ← classify s!"ρ{i}⊃ρ{j}" X
        (fun _ => none)
        (fun k => if g k j == some true then some true else none)
      IO.println s!"RTAB imp {i} {j} = {v}"
    out.flush
  IO.println "── ◯ row ──"
  for i in [0:n] do
    let X := (rhoF i).somehow
    -- ρk ⊢ ◯ρi implied by ρk ⊢ ρi (φ ⊢ ◯φ); ◯ρi ⊢ ρk: no safe law
    let v ← classify s!"◯ρ{i}" X
      (fun _ => none)
      (fun k => if g k i == some true then some true else none)
    IO.println s!"RTAB box {i} {i} = {v}"
  out.flush
  IO.println "RTABLE-DONE"

def main (args : List String) : IO Unit := do
  if args.head? == some "emit" then return (← emitMode)
  if args.head? == some "rtable" then
    return (← rtableMode ((args.getD 1 "48").toNat?.getD 48))
  if args.head? == some "probe" then
    return (← probeMode ((args.getD 1 "48").toNat?.getD 48))
  let maxF := (args.head?.bind String.toNat?).getD 48
  IO.println s!"=== PLL cover sweep over the 22-class ρ-catalogue (LJF◯ fuel ≤ {maxF}) ==="
  let mat0 ← statusMat maxF
  -- DB OVERLAY: the database can know cells the sweep machinery cannot
  -- reach (e.g. FRJ(◯) countermodels — ρ20 ⊬ ρ10, entry rho-0167, is
  -- invisible to battery+G4c+LJF◯).  Banked kernel entries take
  -- precedence over an engine "open"; a CONFLICT (entry vs settled
  -- opposite verdict) aborts the run — it would mean a soundness bug.
  let idx : PLLFormula → Option Nat := fun φ =>
    (List.range n).find? (fun i => rhoF i == φ)
  let mut mat := mat0
  for e in RNDB.allEntries do
    if e.claim.rel == RNDB.Rel.nle then
      match idx e.claim.lhs, idx e.claim.rhs with
      | some i, some j =>
          match (mat.getD i #[]).getD j none with
          | none =>
              IO.println s!"DB-OVERLAY ρ{i} ⊬ ρ{j}  (entry {e.id})"
              mat := mat.set! i ((mat.getD i #[]).set! j (some false))
          | some true =>
              IO.println s!"CONTROL FAILED: entry {e.id} claims ρ{i} ⊬ ρ{j} but the sweep proved ρ{i} ⊢ ρ{j}"
              return
          | some false => pure ()
      | _, _ => pure ()
  -- the matrix, and its open cells
  let mut openCells : List (Nat × Nat) := []
  let mut nPos := 0; let mut nNeg := 0
  for i in [0:n] do
    for j in [0:n] do
      if i != j then
        match mat.getD i #[] |>.getD j none with
        | some true => nPos := nPos + 1
        | some false => nNeg := nNeg + 1
        | none => openCells := (i, j) :: openCells
  IO.println s!"status over {n * (n-1)} cells: {nPos} ⊢, {nNeg} ⊬, {openCells.length} open"
  for (i, j) in openCells.reverse do
    IO.println s!"  OPEN CELL ρ{i} ⊢? ρ{j}"
  IO.println ""
  -- strict pairs
  let strict := (List.range n).flatMap fun a =>
    (List.range n).filterMap fun b => if lt mat a b then some (a, b) else none
  IO.println s!"strict pairs (a < b certified): {strict.length}"
  -- classification
  let mut covers : List (Nat × Nat) := []
  let mut blocked := 0
  let mut openEdges := 0
  let mut controlOK := false
  IO.println ""
  IO.println "── candidate cover edges ──"
  for (a, b) in strict do
    let inter := (List.range n).filter fun c => c != a && c != b && lt mat a c && lt mat c b
    match inter with
    | c :: _ =>
        blocked := blocked + 1
        if a == 6 && b == 12 && inter.contains 9 then controlOK := true
        IO.println s!"  BLOCKED ρ{a} < ρ{b}  (interposer ρ{c}{if inter.length > 1 then s!", +{inter.length - 1} more" else ""})"
    | [] =>
        let undecided := (List.range n).filter fun c =>
          c != a && c != b && !excluded mat a b c
        if undecided.isEmpty then
          covers := (a, b) :: covers
          IO.println s!"  COVER   ρ{a} ⋖ ρ{b}   (every interposer excluded by settled cells)"
        else
          openEdges := openEdges + 1
          IO.println s!"  OPEN    ρ{a} <⋖? ρ{b}  undecided interposers: {undecided.map (s!"ρ{·}")}"
          for c in undecided do
            for cell in needed mat a b c do
              IO.println s!"          FRONTIER {cell}"
  IO.println ""
  IO.println s!"HASSE (scoped to the catalogue): {covers.length} cover edges, {blocked} blocked, {openEdges} open"
  for (a, b) in covers.reverse do
    IO.println s!"  HASSE ρ{a} ⋖ ρ{b}"
  if !controlOK then
    IO.println "CONTROL FAILED: ρ6/ρ12 did not come out BLOCKED by ρ9 — do not trust this run"
  else
    IO.println "control: ρ6 < ρ12 BLOCKED by ρ9, matching kernel theorem RNDB.not_covers_rho6_rho12"
  -- machine-readable class labels, for the diagram generator
  for i in List.range n do
    IO.println s!"LABEL ρ{i} {PLLND.RNC.CFX.pp (rhoF i)}"
  IO.println "RHOCOVER-DONE"

end RhoCover

def main (args : List String) : IO Unit := RhoCover.main args
