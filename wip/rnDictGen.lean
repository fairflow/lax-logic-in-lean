import LaxLogic.PLLG4Term
import LaxLogic.PLLSemUILayered
import LaxLogic.PLLG4Dec
import LaxLogic.PLLSearch

/-!
# Generator for `wip/rnDict.lean` (discover-then-pin)

Runs the fuel-free-but-budgeted G4iLL″ backward searcher
(`G4cTm.findBounded`) OFFLINE on every nontrivial cell of the
RN(◯,{}) closure tables (15 representatives; ∧/∨/⊃ tables and the ◯
column), classifies each combination against the dictionary, and
PRINTS the certified instantiation `rnDict15 : RNDict` as Lean source
— every emitted `G4cTm` proof term is then checked by the kernel when
`wip/rnDict.lean` is elaborated.  Trivial cells (units, idempotence,
commutative mirrors, syntactic coincidences) are discharged by the
generic lemmas of `wip/rnDictBase.lean` instead of emitted terms.

Run: `lake build rnDictGen && .lake/build/bin/rnDictGen > wip/rnDict.lean`
(progress goes to stderr).
-/

open PLLFormula PLLND PLLND.SemUI

namespace RNGen

/-! ## The fifteen representatives (probe order, wip/v2quant_out3.txt) -/

def Fq : PLLFormula := .falsePLL
def Nq (X : PLLFormula) : PLLFormula := X.ifThen Fq
def Bq (X : PLLFormula) : PLLFormula := X.somehow

def reps : List PLLFormula :=
  [Fq,                                                   -- 0  ⊥
   Nq Fq,                                                -- 1  ⊤
   Bq Fq,                                                -- 2  ◯⊥
   Nq (Bq Fq),                                           -- 3  ¬◯⊥
   (Bq Fq).or (Nq (Bq Fq)),                              -- 4
   Bq (Nq (Bq Fq)),                                      -- 5
   Nq (Nq (Bq Fq)),                                      -- 6
   (Nq (Bq Fq)).or (Nq (Nq (Bq Fq))),                    -- 7
   (Bq (Nq (Bq Fq))).ifThen ((Bq Fq).or (Nq (Bq Fq))),  -- 8
   (Bq (Nq (Bq Fq))).or (Nq (Nq (Bq Fq))),               -- 9
   (Nq (Nq (Bq Fq))).ifThen (Bq Fq),                     -- 10
   (Nq (Nq (Bq Fq))).or ((Nq (Nq (Bq Fq))).ifThen (Bq Fq)), -- 11
   Bq ((Nq (Bq Fq)).or (Nq (Nq (Bq Fq)))),               -- 12
   Bq ((Bq (Nq (Bq Fq))).ifThen ((Bq Fq).or (Nq (Bq Fq)))), -- 13
   ((Nq (Nq (Bq Fq))).ifThen (Bq Fq)).ifThen (Bq (Nq (Bq Fq)))] -- 14

def repIdx? (X : PLLFormula) : Option Nat := reps.findIdx? (· = X)

def budget : Nat := 400000

/-! ## Emission: Lean source for formulas, memberships, proof terms -/

/-- Print a formula, naming representatives with index < `n` as `q<i>`. -/
partial def ppFN (n : Nat) (X : PLLFormula) : String :=
  match (repIdx? X).filter (· < n) with
  | some i => s!"q{i}"
  | none =>
    match X with
    | .prop s => s!"(.prop \"{s}\")"
    | .falsePLL => ".falsePLL"
    | .and a b => s!"(.and {ppFN n a} {ppFN n b})"
    | .or a b => s!"(.or {ppFN n a} {ppFN n b})"
    | .ifThen a b => s!"(.ifThen {ppFN n a} {ppFN n b})"
    | .somehow a => s!"(.somehow {ppFN n a})"

def ppF (X : PLLFormula) : String := ppFN 15 X

def memIdx (X : PLLFormula) : List PLLFormula → Nat
  | [] => 0
  | Y :: R => if X = Y then 0 else memIdx X R + 1

def memStrN : Nat → String
  | 0 => "(.head _)"
  | n + 1 => s!"(.tail _ {memStrN n})"

def memS (X : PLLFormula) (Γ : List PLLFormula) : String :=
  memStrN (memIdx X Γ)

/-- Emit a `G4cTm` proof term as elaborable Lean source.  Left-rule
formula implicits are passed as named arguments (they are not
determined by the conclusion); membership proofs are `.head`/`.tail`
chains computed from the tracked context. -/
partial def emitTm : {Γ : List PLLFormula} → {C : PLLFormula} → G4cTm Γ C → String
  | _, _, @G4cTm.init Γ a _ => s!"(.init {memS (.prop a) Γ})"
  | _, _, @G4cTm.botL Γ _ _ => s!"(.botL {memS .falsePLL Γ})"
  | _, _, @G4cTm.andR _ _ _ t1 t2 => s!"(.andR {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.orR1 _ _ _ t => s!"(.orR1 {emitTm t})"
  | _, _, @G4cTm.orR2 _ _ _ t => s!"(.orR2 {emitTm t})"
  | _, _, @G4cTm.impR _ _ _ t => s!"(.impR {emitTm t})"
  | _, _, @G4cTm.laxR _ _ t => s!"(.laxR {emitTm t})"
  | _, _, @G4cTm.laxL Γ A _ _ t =>
      s!"(.laxL (A := {ppF A}) {memS A.somehow Γ} {emitTm t})"
  | _, _, @G4cTm.andL Γ A B _ _ t =>
      s!"(.andL (A := {ppF A}) (B := {ppF B}) {memS (A.and B) Γ} {emitTm t})"
  | _, _, @G4cTm.orL Γ A B _ _ t1 t2 =>
      s!"(.orL (A := {ppF A}) (B := {ppF B}) {memS (A.or B) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLProp Γ a B _ _ _ t =>
      s!"(.impLProp (a := \"{a}\") (B := {ppF B}) {memS ((PLLFormula.prop a).ifThen B) Γ} {memS (.prop a) Γ} {emitTm t})"
  | _, _, @G4cTm.impLAnd Γ A B D _ _ t =>
      s!"(.impLAnd (A := {ppF A}) (B := {ppF B}) (D := {ppF D}) {memS ((A.and B).ifThen D) Γ} {emitTm t})"
  | _, _, @G4cTm.impLOr Γ A B D _ _ t =>
      s!"(.impLOr (A := {ppF A}) (B := {ppF B}) (D := {ppF D}) {memS ((A.or B).ifThen D) Γ} {emitTm t})"
  | _, _, @G4cTm.impLImp Γ A B D _ _ t1 t2 =>
      s!"(.impLImp (A := {ppF A}) (B := {ppF B}) (D := {ppF D}) {memS ((A.ifThen B).ifThen D) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLLax Γ A B _ _ t1 t2 =>
      s!"(.impLLax (A := {ppF A}) (B := {ppF B}) {memS (A.somehow.ifThen B) Γ} {emitTm t1} {emitTm t2})"
  | _, _, @G4cTm.impLLaxLax Γ A B X _ _ _ t1 t2 =>
      s!"(.impLLaxLax (A := {ppF A}) (B := {ppF B}) (X := {ppF X}) {memS (A.somehow.ifThen B) Γ} {memS X.somehow Γ} {emitTm t1} {emitTm t2})"

/-! ## Classification against the dictionary -/

/-- Find the representative interderivable with `X`, returning its
index and the two emitted proof-term sources
(`[X] ⊢ rep k`, `[rep k] ⊢ X`).  A double success is self-certifying;
the classes are pairwise distinct, so at most one `k` can succeed. -/
def classifyTm (X : PLLFormula) : Option (Nat × String × String) := Id.run do
  for k in List.range 15 do
    let D := reps.getD k .falsePLL
    match (G4cTm.findBounded budget [X] D).1 with
    | none => pure ()
    | some t1 =>
      match (G4cTm.findBounded budget [D] X).1 with
      | none => pure ()
      | some t2 =>
          return some (k, s!"(ofG4 {emitTm t1})", s!"(ofG4 {emitTm t2})")
  return none

/-! ## Second oracle: the certified-complete `G4s` searcher + the
countermodel battery (v2quant's widened sweep), for diagnosing cells
the `G4cTm` searcher cannot close. -/

def provF (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C

def closeF (f : Search.Frame) : Search.Frame := Id.run do
  let mut ri := f.ri
  let mut rm := f.rm
  let mut changed := true
  while changed do
    changed := false
    for e in ri do
      for e' in ri do
        if e.2 == e'.1 && !(decide ((e.1, e'.2) ∈ ri)) && e.1 != e'.2 then
          ri := ri ++ [(e.1, e'.2)]
          changed := true
    for e in rm do
      for e' in rm do
        if e.2 == e'.1 && !(decide ((e.1, e'.2) ∈ rm)) && e.1 != e'.2 then
          rm := rm ++ [(e.1, e'.2)]
          changed := true
  return ⟨f.n, ri, rm, f.fall⟩

def chain3F : Search.Frame := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], []⟩

def residFrames : List Search.Frame :=
  [⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)], [], [4]⟩,
   ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)], [(3,4)], [4]⟩,
   ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)], [], []⟩,
   ⟨3, [(0,1),(0,2)], [], []⟩,
   ⟨3, [(0,1),(0,2)], [], [2]⟩,
   ⟨3, [(0,1),(0,2)], [(0,2)], [2]⟩,
   ⟨4, [(0,1),(0,2),(1,3),(2,3)], [], [3]⟩,
   ⟨4, [(0,1),(0,2),(1,3),(2,3)], [(1,3),(2,3)], [3]⟩,
   ⟨4, [(0,1),(0,2),(1,3),(2,3)], [], []⟩,
   ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], [3]⟩,
   ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], []⟩,
   ⟨4, [(0,1),(0,2),(0,3),(1,3),(2,3)], [(0,1)], [3]⟩]

def scanFrames : List Search.Frame :=
  (Search.defaultFrames ++ [chain3F] ++ residFrames).map closeF

def cfgD : Search.Config :=
  { frames := scanFrames, findBudget := some 1, emitClosureCap := 0 }

/-! ### Exhaustive small-frame battery (variable-free sweep)

All well-formed frames with ≤ 4 worlds: `ri` any strict poset
(irreflexive, transitively closed), `rm ⊆ ri` transitive, `fall`
up-closed.  For variable-free sequents the decoration space is a
point, so the sweep is a complete search over ≤4-world countermodels
— every hit is certified by `checkB`. -/

def offdiag (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun a => (List.range n).filterMap fun b =>
    if a ≠ b then some (a, b) else none

def transB (r : List (Nat × Nat)) : Bool :=
  r.all fun e => r.all fun e' =>
    !(e.2 == e'.1) || decide ((e.1, e'.2) ∈ r)

def upclB (n : Nat) (r : List (Nat × Nat)) (f : List Nat) : Bool :=
  f.all fun w => (List.range n).all fun v =>
    !(decide ((w, v) ∈ r)) || decide (v ∈ f)

def framesOf (n : Nat) : List Search.Frame := Id.run do
  let mut out := []
  for ri in (offdiag n).sublists do
    if transB ri then
      for rm in ri.sublists do
        if transB rm then
          for fall in (List.range n).sublists do
            if upclB n ri fall then
              out := out ++ [(⟨n, ri, rm, fall⟩ : Search.Frame)]
  return out

def bigBattery : List Search.Frame :=
  framesOf 1 ++ framesOf 2 ++ framesOf 3 ++ framesOf 4

def cfgBig : Search.Config :=
  { frames := bigBattery, findBudget := some 1, emitClosureCap := 0 }

inductive V3 | proved | refuted | unknown
deriving BEq

/-- Countermodel-first two-sided verdict: certified sweeps (standard
battery, then the exhaustive ≤4-world battery), then the G4cTm
searcher, then the certified-complete `G4s` searcher at `fuel`. -/
def v3 (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : V3 :=
  match Search.decide cfgD Γ C with
  | .refuted _ _ _ => .refuted
  | .proved _ => .proved
  | .unknown =>
    match Search.decide cfgBig Γ C with
    | .refuted _ _ _ => .refuted
    | .proved _ => .proved
    | .unknown =>
      match (G4cTm.findBounded budget Γ C).1 with
      | some _ => .proved
      | none =>
        -- `provF` (the `G4s` searcher) explodes on exhaustive-false
        -- at these sizes; only consult it at tiny fuel.
        if fuel ≤ 12 && provF fuel Γ C then .proved else .unknown

def v3tag : V3 → String
  | .proved => "proved" | .refuted => "REFUTED" | .unknown => "unknown"

/-- Strong-oracle scan of one combination against all 15 classes:
per class, ELIMINATED (a certified countermodel on one side), MATCHED
(proofs both sides), or OPEN. -/
def oracleCell (fuel : Nat) (name : String) (X : PLLFormula) : IO Unit := do
  let mut matched : List Nat := []
  let mut openK : List Nat := []
  for k in List.range 15 do
    let D := reps.getD k .falsePLL
    IO.eprintln s!"    [{name}] k={k} side A"
    (← IO.getStderr).flush
    let a := v3 fuel [X] D
    if a == .refuted then continue
    IO.eprintln s!"    [{name}] k={k} side E (A={v3tag a})"
    (← IO.getStderr).flush
    let b := v3 fuel [D] X
    if b == .refuted then continue
    if a == .proved && b == .proved then matched := matched ++ [k]
    else openK := openK ++ [k]
  match matched, openK with
  | [], [] => IO.println s!"{name}: NEW CLASS (all 15 candidates countermodel-eliminated)"
  | [], l => IO.println s!"{name}: no match, open candidates {l}"
  | m, [] => IO.println s!"{name}: matched {m}"
  | m, l => IO.println s!"{name}: matched {m}, open {l}"
  (← IO.getStdout).flush

def parseCell (c : String) : Option (String × PLLFormula) :=
  let r (i : Nat) : PLLFormula := reps.getD i .falsePLL
  match c.splitOn "_" with
  | ["cAnd", i, j] => some (c, (r i.toNat!).and (r j.toNat!))
  | ["cOr", i, j] => some (c, (r i.toNat!).or (r j.toNat!))
  | ["cImp", i, j] => some (c, (r i.toNat!).ifThen (r j.toNat!))
  | ["cBox", i] => some (c, (r i.toNat!).somehow)
  | _ => none

/-- Escalating two-sided test of a single entailment `[P] ⊢ Q`,
`P`/`Q` given as `q<i>` indices. -/
def entMain (fuel : Nat) (i j : Nat) : IO Unit := do
  let P := reps.getD i .falsePLL
  let Q := reps.getD j .falsePLL
  let t0 ← IO.monoMsNow
  let v := v3 fuel [P] Q
  let t1 ← IO.monoMsNow
  IO.println s!"[q{i}]⊢q{j} at fuel {fuel}: {v3tag v} ({t1-t0}ms)"

/-- Stage-level timing for one (cell, k) pair. -/
def stagesMain (cell : String) (k : Nat) : IO Unit := do
  match parseCell cell with
  | none => IO.eprintln "bad cell"
  | some (_, X) =>
    let D := reps.getD k .falsePLL
    for (nm, Γ, C) in [("A: [X]⊢D", [X], D), ("E: [D]⊢X", [D], X)] do
      let t0 ← IO.monoMsNow
      let r1 := match Search.decide cfgD Γ C with
        | .refuted _ _ _ => "refuted" | .proved _ => "proved" | .unknown => "unknown"
      let t1 ← IO.monoMsNow
      IO.println s!"{nm} cfgD: {r1} ({t1-t0}ms)"; (← IO.getStdout).flush
      let r2 := match Search.decide cfgBig Γ C with
        | .refuted _ _ _ => "refuted" | .proved _ => "proved" | .unknown => "unknown"
      let t2 ← IO.monoMsNow
      IO.println s!"{nm} cfgBig: {r2} ({t2-t1}ms)"; (← IO.getStdout).flush
      let r3 := match (G4cTm.findBounded budget Γ C).1 with
        | some _ => "FOUND" | none => "none"
      let t3 ← IO.monoMsNow
      IO.println s!"{nm} findBounded: {r3} ({t3-t2}ms)"; (← IO.getStdout).flush

def oracleMain (fuel : Nat) (cells : List String) : IO Unit := do
  for c in cells do
    match parseCell c with
    | some (n, X) => oracleCell fuel n X
    | none => IO.eprintln s!"bad cell name {c}"


/-- Cut-chain certificate search for one direction `[P] ⊢ Q`: a direct
G4cTm term, or a chain of direct terms through representative middles,
glued by `Deriv.cutHead` (the searcher misses some derivable sequents;
lemma-introduction recovers those reachable through the dictionary). -/
def chainD : Nat → PLLFormula → PLLFormula → Option String
  | 0, P, Q =>
    match (G4cTm.findBounded budget [P] Q).1 with
    | some t => some s!"(ofG4 {emitTm t})"
    | none => none
  | d + 1, P, Q =>
    match (G4cTm.findBounded budget [P] Q).1 with
    | some t => some s!"(ofG4 {emitTm t})"
    | none =>
      (reps.filterMap fun M =>
        if M = P || M = Q then none
        else match (G4cTm.findBounded budget [P] M).1 with
          | none => none
          | some t1 =>
            match chainD d M Q with
            | none => none
            | some e2 =>
                some s!"(Deriv.cutHead (ofG4 {emitTm t1}) {e2})").head?

/-! ## Cell resolution -/

inductive Conn | cAnd | cOr | cImp
deriving BEq

def Conn.mk : Conn → PLLFormula → PLLFormula → PLLFormula
  | .cAnd, a, b => a.and b
  | .cOr, a, b => a.or b
  | .cImp, a, b => a.ifThen b

def Conn.opStr : Conn → String
  | .cAnd => "and" | .cOr => "or" | .cImp => "ifThen"

def Conn.nm : Conn → String
  | .cAnd => "And" | .cOr => "Or" | .cImp => "Imp"

structure Cell where
  value : Nat
  expr : String
  thm : Option String := none
  searched : Bool := false
deriving Inhabited

/-- Search-backed resolution of one nontrivial cell (shared by the
binary tables and the ◯ column).  Stages: direct two-sided G4cTm
classification; on failure the strong oracle (countermodel-first,
exhaustive ≤4-world battery) categorises the cell — matched (then
cut-chain certificate recovery), NEW CLASS (all candidates
countermodel-eliminated: the 15-class closure fails there), or open —
and un-certificated cells are emitted as isolated `sorry` lemmas with
the category recorded. -/
def resolveSearched (name stmt : String) (impSpecial : Bool)
    (comb : PLLFormula) : IO Cell := do
  let t0 ← IO.monoMsNow
  match classifyTm comb with
  | some (k, e1, e2) =>
      let t1 ← IO.monoMsNow
      IO.eprintln s!"  {name} -> {k}  ({t1 - t0}ms)"
      let head := s!"theorem {name} : {stmt} q{k} :="
      if impSpecial && k == 1 then
        return { value := k, expr := name, searched := true,
                 thm := some s!"{head}\n  ⟨topD, {e2}⟩" }
      else
        return { value := k, expr := name, searched := true,
                 thm := some s!"{head}\n  ⟨{e1},\n   {e2}⟩" }
  | none =>
    let mut matched : List Nat := []
    let mut openK : List Nat := []
    for k in List.range 15 do
      let D := reps.getD k .falsePLL
      let a := v3 40 [comb] D
      if a == .refuted then continue
      let b := v3 40 [D] comb
      if b == .refuted then continue
      if a == .proved && b == .proved then matched := matched ++ [k]
      else openK := openK ++ [k]
    match matched with
    | k :: _ =>
      let D := reps.getD k .falsePLL
      let e1? := if impSpecial && k == 1 then some "topD" else chainD 3 comb D
      let e2? := chainD 3 D comb
      match e1?, e2? with
      | some e1, some e2 =>
          IO.eprintln s!"  {name} -> {k}  (cut-chain)"
          return { value := k, expr := name, searched := true,
                   thm := some s!"theorem {name} : {stmt} q{k} :=\n  ⟨{e1},\n   {e2}⟩" }
      | _, _ =>
          IO.eprintln s!"  !! {name}: SEARCHER GAP at {k} (sorried)"
          return { value := k, expr := name, searched := true,
                   thm := some s!"/-- UNCERTIFIED (searcher gap): the strong oracle proves both\ndirections against class {k}, but no G4cTm certificate was found,\ndirect or cut-chain. -/\ntheorem {name} : {stmt} q{k} := sorry" }
    | [] =>
      match openK with
      | [] =>
        IO.eprintln s!"  !! {name}: NEW CLASS (all 15 eliminated)"
        return { value := 0, expr := name, searched := true,
                 thm := some s!"/-- REFUTED CELL (new class): certified ≤4-world countermodels\neliminate EVERY candidate class — this combination is not\ninterderivable with any of the 15 representatives, so the 15-class\nclosure FAILS here.  The stated collapse (to q0, a placeholder) is\nFALSE; the `sorry` records the failure point. -/\ntheorem {name} : {stmt} q0 := sorry" }
      | l =>
        let k := l.headD 0
        IO.eprintln s!"  !! {name}: OPEN {l} (sorried at {k})"
        return { value := k, expr := name, searched := true,
                 thm := some s!"/-- OPEN CELL: candidates {l} neither proved (both searchers) nor\nrefuted (exhaustive ≤4-world battery).  Sorried at the first open\ncandidate. -/\ntheorem {name} : {stmt} q{k} := sorry" }

/-- Resolve one binary-table cell.  Priority: syntactic coincidence
with a representative; ⊥/⊤ unit laws; idempotence; commutative mirror
(referencing the transposed cell's expression); otherwise offline
search with an emitted certificate. -/
def resolveCell (c : Conn) (i j : Nat) (grid : Array (Array Cell)) :
    IO Cell := do
  let comb := c.mk (reps.getD i .falsePLL) (reps.getD j .falsePLL)
  match repIdx? comb with
  | some k => return { value := k, expr := "Interd.refl _" }
  | none =>
  match c with
  | .cAnd =>
    if i == 0 then return { value := 0, expr := "bot_and_i _" }
    else if j == 0 then
      return { value := 0, expr := "(and_comm_i _ _).trans (bot_and_i _)" }
    else if i == 1 then return { value := j, expr := "top_and_i _" }
    else if j == 1 then
      return { value := i, expr := "(and_comm_i _ _).trans (top_and_i _)" }
    else if i == j then return { value := i, expr := "and_idem_i _" }
    else if i > j then
      let t := (grid.getD j #[]).getD i default
      return { value := t.value,
               expr := s!"(and_comm_i _ _).trans ({t.expr})" }
    else searchCell c i j comb
  | .cOr =>
    if i == 0 then return { value := j, expr := "bot_or_i _" }
    else if j == 0 then
      return { value := i, expr := "(or_comm_i _ _).trans (bot_or_i _)" }
    else if i == 1 then return { value := 1, expr := "top_or_i _" }
    else if j == 1 then
      return { value := 1, expr := "(or_comm_i _ _).trans (top_or_i _)" }
    else if i == j then return { value := i, expr := "or_idem_i _" }
    else if i > j then
      let t := (grid.getD j #[]).getD i default
      return { value := t.value,
               expr := s!"(or_comm_i _ _).trans ({t.expr})" }
    else searchCell c i j comb
  | .cImp =>
    if i == 0 then return { value := 1, expr := "bot_imp_i _" }
    else if i == 1 then return { value := j, expr := "top_imp_i _" }
    else if j == 1 then return { value := 1, expr := "imp_top_i _" }
    else if i == j then return { value := 1, expr := "imp_self_i _" }
    else searchCell c i j comb
where
  searchCell (c : Conn) (i j : Nat) (comb : PLLFormula) : IO Cell :=
    resolveSearched s!"c{c.nm}_{i}_{j}" s!"Interd (q{i}.{c.opStr} q{j})"
      (c == .cImp) comb

/-- Resolve one ◯-column cell. -/
def resolveBox (i : Nat) : IO Cell := do
  let ri := reps.getD i .falsePLL
  let comb := ri.somehow
  match repIdx? comb with
  | some k => return { value := k, expr := "Interd.refl _" }
  | none =>
  match ri with
  | .somehow _ => return { value := i, expr := "box_idem_i _" }
  | _ => resolveSearched s!"cBox_{i}" s!"Interd q{i}.somehow" false comb

/-! ## Assembly -/

def header : String :=
"import wip.stabilise
import wip.rnDictBase

/-!
# The certified RN(◯,{}) dictionary: `rnDict15 : RNDict`

GENERATED FILE — do not edit by hand.  Produced by
`wip/rnDictGen.lean` (`lake build rnDictGen && .lake/build/bin/rnDictGen > wip/rnDict.lean`).

The fifteen interderivability-class representatives of the
variable-free PLL fragment (the RN(◯,{}) dictionary computed by the
v2quant probe, wip/v2quant_out3.txt), with KERNEL-CHECKED closure
tables: for every pair of representatives and each of ∧, ∨, ⊃ (and
every representative under ◯), an `Interd` certificate collapsing the
combination onto its representative.  Nontrivial cells carry G4iLL″
proof terms found by offline search (`G4cTm.findBounded`, pinned as
source per the repo's discover-then-pin discipline) and are bridged to
`LaxND` by `RND.ofG4`; trivial cells go through the generic laws of
`wip/rnDictBase.lean`.

The instantiation plugs into `wip/stabilise.lean`: `dict_collapse`,
`dict_agree_stab`, `vfB_mforthResidue` and
`restricted_amalgamation_oneVar` become unconditional in the
`RNDict` argument.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND
"

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut out : Array String := #[header]
  -- representatives
  out := out.push "/-! ## The fifteen representatives (probe order) -/\n"
  for i in List.range 15 do
    out := out.push s!"def q{i} : PLLFormula := {ppFN i (reps.getD i .falsePLL)}"
  let repList := String.intercalate ", " ((List.range 15).map (s!"q{·}"))
  out := out.push s!"\ndef repsL : List PLLFormula := [{repList}]"
  out := out.push "\ndef rep15 : Fin 15 → PLLFormula := fun i => repsL.getD i.val .falsePLL"
  -- resolve tables
  let conns : List Conn := [.cAnd, .cOr, .cImp]
  let mut grids : Array (Array (Array Cell)) := #[]
  for c in conns do
    IO.eprintln s!"resolving {c.nm} table..."
    let mut grid : Array (Array Cell) := #[]
    for i in List.range 15 do
      let mut row : Array Cell := #[]
      for j in List.range 15 do
        row := row.push (← resolveCell c i j grid)
      grid := grid.push row
    grids := grids.push grid
  IO.eprintln "resolving Box column..."
  let mut boxCol : Array Cell := #[]
  for i in List.range 15 do
    boxCol := boxCol.push (← resolveBox i)
  -- tables
  out := out.push "\n/-! ## The closure tables -/\n"
  for (c, g) in conns.zip grids.toList do
    let rows := g.toList.map fun row =>
      "[" ++ String.intercalate ", " (row.toList.map (s!"{·.value}")) ++ "]"
    out := out.push s!"def {c.nm.toLower}T : List (List Nat) :=\n  [{String.intercalate ",\n   " rows}]"
  out := out.push s!"\ndef boxT : List Nat := [{String.intercalate ", " (boxCol.toList.map (s!"{·.value}"))}]"
  for c in conns do
    out := out.push s!"\ndef {c.nm.toLower}Idx15 (i j : Fin 15) : Fin 15 :=\n  ⟨(({c.nm.toLower}T.getD i.val []).getD j.val 0) % 15, Nat.mod_lt _ (by decide)⟩"
  out := out.push "\ndef boxIdx15 (i : Fin 15) : Fin 15 :=\n  ⟨(boxT.getD i.val 0) % 15, Nat.mod_lt _ (by decide)⟩"
  -- cell certificates
  out := out.push "\n/-! ## Searched-cell certificates (offline G4iLL″ terms, kernel-checked here) -/\n"
  let mut nSearch := 0
  let mut nGeneric := 0
  for g in grids do
    for row in g do
      for cell in row do
        if cell.searched then nSearch := nSearch + 1 else nGeneric := nGeneric + 1
        if let some t := cell.thm then out := out.push (t ++ "\n")
  for cell in boxCol do
    if cell.searched then nSearch := nSearch + 1 else nGeneric := nGeneric + 1
    if let some t := cell.thm then out := out.push (t ++ "\n")
  -- closure theorems
  out := out.push "/-! ## The closure theorems -/\n"
  for (c, g) in conns.zip grids.toList do
    let mut s := s!"theorem {c.nm.toLower}_ok (i j : Fin 15) :\n    Interd ((rep15 i).{c.opStr} (rep15 j)) (rep15 ({c.nm.toLower}Idx15 i j)) :=\n  match i, j with\n"
    for i in List.range 15 do
      for j in List.range 15 do
        s := s ++ s!"  | ⟨{i}, _⟩, ⟨{j}, _⟩ => {((g.getD i #[]).getD j default).expr}\n"
    s := s ++ "  | ⟨_+15, h⟩, _ => absurd h (by omega)\n"
    s := s ++ "  | _, ⟨_+15, h⟩ => absurd h (by omega)\n"
    out := out.push s
  let mut sb := "theorem box_ok (i : Fin 15) :\n    Interd (rep15 i).somehow (rep15 (boxIdx15 i)) :=\n  match i with\n"
  for i in List.range 15 do
    sb := sb ++ s!"  | ⟨{i}, _⟩ => {(boxCol.getD i default).expr}\n"
  sb := sb ++ "  | ⟨_+15, h⟩ => absurd h (by omega)\n"
  out := out.push sb
  -- the dictionary
  let crankMax := (reps.map crank).foldl max 0
  let mut nSorry := 0
  for g in grids do
    for row in g do
      for cell in row do
        if (cell.thm.getD "").endsWith "sorry" then nSorry := nSorry + 1
  for cell in boxCol do
    if (cell.thm.getD "").endsWith "sorry" then nSorry := nSorry + 1
  out := out.push "end RND\n"
  out := out.push ("open RND in
/-- **The certified RN(◯,{}) dictionary**: 15 variable-free
representatives, crank bound " ++ toString crankMax ++ ", connective-closure tables
kernel-checked away from the sorried cells (" ++ Nat.repr nSorry ++ " of 690; when that
count is 0 this record is the full certified dictionary). -/
def rnDict15 : RNDict where
  n := 15
  rep := rep15
  rep_varFree := by decide
  crankBound := " ++ toString crankMax ++ "
  rep_crank_le := by decide
  botIdx := ⟨0, by decide⟩
  bot_interd := Interd.refl _
  andIdx := andIdx15
  orIdx := orIdx15
  impIdx := impIdx15
  boxIdx := boxIdx15
  and_interd := and_ok
  or_interd := or_ok
  imp_interd := imp_ok
  box_interd := box_ok

/-! ## Axiom audit -/
" ++ (if nSorry == 0 then "
/--
info: 'PLLND.SemUI.rnDict15' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rnDict15" else "
-- PARTIAL instantiation: " ++ Nat.repr nSorry ++ " cells are sorried (see the
-- per-cell doc comments: REFUTED/OPEN/SEARCHER-GAP).  No #guard_msgs pin.
#print axioms rnDict15") ++ "

end SemUI
end PLLND")
  -- print
  let stdout ← IO.getStdout
  for s in out do
    stdout.putStrLn s
  stdout.flush
  let t1 ← IO.monoMsNow
  IO.eprintln s!"done: {nSearch} searched cells, {nGeneric} generic cells, {nSorry} sorried, {(t1 - t0)}ms, crankMax {crankMax}"

/-! ## Refutation-witness emission (`rnDictGen refute <cell>...`)

For a NEW-CLASS cell, emit the machine-checked witness theorem: for
EVERY candidate class, one direction of the collapse is refuted by a
pinned `checkB` countermodel (`by decide`).  Printed as
`wip/rnDictRefute.lean`. -/

def fmtPairs (l : List (Nat × Nat)) : String :=
  "[" ++ String.intercalate ", " (l.map fun e => s!"({e.1}, {e.2})") ++ "]"

def fmtNats (l : List Nat) : String :=
  "[" ++ String.intercalate ", " (l.map fun e => s!"{e}") ++ "]"

def fmtCM (M : FinCM) : String :=
  s!"⟨{M.n}, {fmtPairs M.ri}, {fmtPairs M.rm}, {fmtNats M.fall}, []⟩"

/-- Find a certified refutation of `Γ ⊢ C`, returning the countermodel. -/
def findCM (Γ : List PLLFormula) (C : PLLFormula) : Option (FinCM × Nat) :=
  match Search.decide cfgD Γ C with
  | .refuted M w _ => some (M, w)
  | _ =>
    match Search.decide cfgBig Γ C with
    | .refuted M w _ => some (M, w)
    | _ => none

/-- One arm of the witness theorem: refute `Interd X (rep k)` via a
countermodel against one of its two directions. -/
def refuteArm (X : PLLFormula) (stmtX : String) (k : Nat) : Option String :=
  let D := reps.getD k .falsePLL
  match findCM [X] D with
  | some (M, w) =>
      -- `C := q<k>` pins the closed representative so the `decide` goal
      -- has no free variables; defeq with `rep15 ⟨k, _⟩` closes the arm.
      some s!"  | ⟨{k}, _⟩ => fun h => FinCM.not_provable_of_check (M := {fmtCM M}) (w := {w}) (C := q{k}) (by decide) h.1"
  | none =>
    match findCM [D] X with
    | some (M, w) =>
        some s!"  | ⟨{k}, _⟩ => fun h => FinCM.not_provable_of_check (M := {fmtCM M}) (w := {w}) (Γ := [q{k}]) (by decide) h.2"
    | none => none

def refuteHeader : String :=
"import wip.rnDict

/-!
# Machine-checked closure failure of the 15-class dictionary

GENERATED FILE (`rnDictGen refute ...`) — do not edit by hand.

For each witness cell below, the theorem eliminates EVERY candidate
class: one direction of the would-be collapse is refuted by a pinned
finite countermodel, checked by the kernel via `FinCM.checkB` +
`FinCM.not_provable_of_check` (`by decide` on closed data).  Hence the
variable-free fragment does NOT collapse onto the 15 representatives:
the RN(◯,{}) dictionary of the v2quant probe (size-capped) is not
connective-closed, and `RNDict` is NOT instantiable with these 15
representatives and ANY tables at the witnessed connectives.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND
"

def refuteCell (name : String) (X : PLLFormula) (stmtX : String) :
    IO (Option String) := do
  let mut arms : Array String := #[]
  for k in List.range 15 do
    match refuteArm X stmtX k with
    | some a => arms := arms.push a
    | none =>
        IO.eprintln s!"  !! {name}: candidate {k} not countermodel-refuted; no witness theorem"
        return none
  let body := String.intercalate "\n" arms.toList
  return some (s!"/-- `{stmtX}` matches NO dictionary class: every candidate is
countermodel-eliminated. -/
theorem refute_{name} : ∀ k : Fin 15, ¬ Interd ({stmtX}) (rep15 k) :=
  fun k => match k with
" ++ body ++ "
  | ⟨_+15, hh⟩ => absurd hh (by omega)
")

def refuteMain (cells : List String) : IO Unit := do
  let mut out : Array String := #[refuteHeader]
  let mut names : Array String := #[]
  for c in cells do
    match parseCell c with
    | none => IO.eprintln s!"bad cell name {c}"
    | some (n, X) =>
      let stmtX :=
        match c.splitOn "_" with
        | ["cAnd", i, j] => s!"q{i}.and q{j}"
        | ["cOr", i, j] => s!"q{i}.or q{j}"
        | ["cImp", i, j] => s!"q{i}.ifThen q{j}"
        | ["cBox", i] => s!"q{i}.somehow"
        | _ => "?"
      match ← refuteCell n X stmtX with
      | some t => out := out.push t; names := names.push s!"refute_{n}"
      | none => pure ()
  out := out.push "/-! ## Axiom audit -/
"
  for n in names do
    out := out.push ("/--
info: 'PLLND.SemUI.RND." ++ n ++ "' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms " ++ n ++ "
")
  out := out.push "end RND
end SemUI
end PLLND"
  let stdout ← IO.getStdout
  for x in out do
    stdout.putStrLn x
  stdout.flush

/-! ## Diagnostic mode (`rnDictGen diag <cellname>...`) -/

def tagB {Γ : List PLLFormula} {C : PLLFormula} :
    Option (G4cTm Γ C) × Nat → String
  | (some _, r) => s!"FOUND (rem {r})"
  | (none, 0) => "BUDGET-OUT"
  | (none, r) => s!"exhausted (rem {r})"

def probeCell (name : String) (X : PLLFormula) : IO Unit := do
  IO.println s!"== {name} =="
  for k in List.range 15 do
    let D := reps.getD k .falsePLL
    let t0 ← IO.monoMsNow
    let a := G4cTm.findBounded budget [X] D
    let t1 ← IO.monoMsNow
    let b := G4cTm.findBounded budget [D] X
    let t2 ← IO.monoMsNow
    IO.println s!"  k={k}: [X]⊢D {tagB a} ({t1-t0}ms)   [D]⊢X {tagB b} ({t2-t1}ms)"
    (← IO.getStdout).flush

def diagMain (cells : List String) : IO Unit := do
  let r (i : Nat) : PLLFormula := reps.getD i .falsePLL
  for c in cells do
    match c.splitOn "_" with
    | ["cAnd", i, j] => probeCell c ((r i.toNat!).and (r j.toNat!))
    | ["cOr", i, j] => probeCell c ((r i.toNat!).or (r j.toNat!))
    | ["cImp", i, j] => probeCell c ((r i.toNat!).ifThen (r j.toNat!))
    | ["cBox", i] => probeCell c (r i.toNat!).somehow
    | _ => IO.eprintln s!"bad cell name {c}"

end RNGen

def main : List String → IO Unit
  | [] => RNGen.main
  | "diag" :: cells => RNGen.diagMain cells
  | "oracle" :: fuel :: cells => RNGen.oracleMain fuel.toNat! cells
  | "refute" :: cells => RNGen.refuteMain cells
  | ["ent", fuel, i, j] => RNGen.entMain fuel.toNat! i.toNat! j.toNat!
  | ["stages", cell, k] => RNGen.stagesMain cell k.toNat!
  | _ => IO.eprintln "usage: rnDictGen [diag <cell>...|oracle <fuel> <cell>...]" 
