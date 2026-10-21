/-
# Spike S2: what settles a cell, measured on the OLD data (2026-10-21)

READ-ONLY with respect to RNDB: this walks `RNDB.allEntries` (the walk of
`tools/RNDBExport.lean`) into an in-memory store of base facts keyed by
the proposed identity key, then asks a DESIGNED test set (CLAUDE.md
rule 9) four ways, in order, and records which tier settled each cell
and how long it took:

* **K, key lookup**: the identity key `key φ = keyF (canonFix φ)`;
  equal keys, or a stored fact on the key pair;
* **U, lookup plus union-find over `interd`**: equal classes, or a stored
  `⊬` between the two classes;
* **O, order facts**: `≤` chains over stored `le` facts (none in the old
  data), `⊥` and `⊤` as least and greatest element, and the propagation
  `[φ'] ⊬ ψ', φ' ≤ φ, ψ ≤ ψ'  ⟹  [φ] ⊬ ψ`;
* **D, a public decider**: `PLLND.Search.verdictWhy` (the G4c engine and
  the FinCM battery/emitter, `LaxLogic/PLL/Search/Search.lean`) at the
  default node budget 200000 and emit cap 12 (30 s limit); on a node-budget cutoff once more at 2000000 (D2), and when only the emit cap stopped it, at emit cap 16 (D3), each with a 120 s limit.
  A `⊢` answer carries a G4c proof term, a `⊬` answer a FinCM model
  accepted by `FinCM.checkB`; neither is re-checked by the kernel here.

The test set:

* `T0`, the smoke test: six designed closed ◯-free formulas, each asked
  against `⊥` and `⊤` in both directions (24 cells).  This fragment is the
  two-element algebra, so every cell must settle without the decider.
* `T1`: the 462 directed ρ-cells `[ρi] ⊢? ρj`, `i ≠ j`.
* `T2`: ten designed formulas: q12 and q13 (the q-representatives with
  no ρ twin); six escape compounds (compounds of q-representatives that
  RNDB records as escaping the q-list; two are ρ15 and ρ13 up to `canon`,
  as controls); two Rieger–Nishimura rungs `subOb (sLad n)`.  Each is
  asked against all 22 ρ in both directions (440 cells).

`T2` is asked three times: against the old store with the decider
(`old`); against the old store with the decider's `T1` answers banked as
base facts (the "store the order" design), first without the decider
(`banked`) and then with it (`banked+D`).  Decider results are memoised
on the key pair, so a repeated pair is not re-decided (`decider_reused`).

A stage that hits its time limit is abandoned, not stopped: `IO.cancel`
is cooperative, so the abandoned computation keeps one core busy until it
ends or the process exits.  The `gtimeout` bound covers the whole run.

Run (bounded; built binary):

    lake build f0s2
    gtimeout 3000 .lake/build/bin/f0s2 _out/f0s2-cells.jsonl
-/
import RNDB.DB
import Rewrite.Canon
import LaxLogic.RN.Rho
import LaxLogic.RN.Reps
import LaxLogic.PLL.Search.Search
import LaxLogic.PLL.Semantics.LaxInfinite
import Lean.Data.Json
import Std.Data.HashMap
import Std.Data.HashSet

open Lean (Json toJson)

namespace F0S2

/-! ## Printing (as in `tools/RNDBExport.lean`) -/

def prec : PLLFormula → Nat
  | .ifThen .falsePLL .falsePLL => 3
  | .ifThen _ .falsePLL => 3
  | .ifThen _ _ => 0
  | .or _ _ => 1
  | .and _ _ => 2
  | _ => 3

def par (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

def pp : PLLFormula → String
  | .prop s => s
  | .falsePLL => "⊥"
  | .ifThen .falsePLL .falsePLL => "⊤"
  | .ifThen a .falsePLL => "¬" ++ par (prec a < 3) (pp a)
  | .ifThen a b => par (prec a == 0) (pp a) ++ " ↠ " ++ pp b
  | .or a b => par (prec a ≤ 1) (pp a) ++ " ∨ " ++ par (prec b ≤ 1) (pp b)
  | .and a b => par (prec a ≤ 2) (pp a) ++ " ∧ " ++ par (prec b ≤ 2) (pp b)
  | .somehow a => "◯" ++ par (prec a < 3) (pp a)

def js (s : String) : Json := Json.str s

/-! ## The identity key (proposal §2) -/

/-- `canon` iterated to a fixpoint, at most `n` rounds; also returns the
number of rounds that changed the formula. -/
def canonFixAux : Nat → Nat → PLLFormula → PLLFormula × Nat
  | 0, r, φ => (φ, r)
  | n + 1, r, φ =>
      let c := Rewrite.canon φ
      if c == φ then (φ, r) else canonFixAux n (r + 1) c

def canonFix (φ : PLLFormula) : PLLFormula × Nat := canonFixAux 64 0 φ

def key (φ : PLLFormula) : String := Rewrite.keyF (canonFix φ).1

def topF : PLLFormula := .ifThen .falsePLL .falsePLL

/-! ## The store of base facts -/

structure Store where
  ids : Std.HashMap String Nat := {}
  parent : Array Nat := #[]
  pos : Std.HashSet (Nat × Nat) := {}
  neg : Std.HashMap (Nat × Nat) String := {}
  leList : Array (Nat × Nat) := #[]
  negList : Array (Nat × Nat) := #[]
  facts : Nat := 0

def Store.idOf (s : Store) (k : String) : Store × Nat :=
  match s.ids.get? k with
  | some i => (s, i)
  | none =>
      let i := s.parent.size
      ({ s with ids := s.ids.insert k i, parent := s.parent.push i }, i)

partial def findRoot (p : Array Nat) (x : Nat) : Nat :=
  let y := p[x]!
  if y == x then x else findRoot p y

def Store.union (s : Store) (a b : Nat) : Store :=
  let ra := findRoot s.parent a
  let rb := findRoot s.parent b
  if ra == rb then s else { s with parent := s.parent.set! ra rb }

/-- Bank one base fact.  `interd` is stored as `≤` both ways and merges
the two classes; `le` is a `≤`; `nle` a `⊬`. -/
def Store.add (s0 : Store) (lhs rhs : PLLFormula) (rel : RNDB.Rel) (src : String) :
    Store := Id.run do
  let (s1, a) := s0.idOf (key lhs)
  let (s2, b) := s1.idOf (key rhs)
  let mut s := { s2 with facts := s2.facts + 1 }
  match rel with
  | .interd =>
      s := { s with pos := (s.pos.insert (a, b)).insert (b, a) }
      s := s.union a b
  | .le =>
      s := { s with pos := s.pos.insert (a, b), leList := s.leList.push (a, b) }
  | .nle =>
      s := { s with neg := s.neg.insert (a, b) src, negList := s.negList.push (a, b) }
  return s

/-- The class-level view: roots, `⊬` between classes, `≤` up-sets. -/
structure View where
  root : Array Nat
  negC : Std.HashSet (Nat × Nat)
  negCList : Array (Nat × Nat)
  ups : Std.HashMap Nat (Std.HashSet Nat)
  botC : Option Nat
  topC : Option Nat

def Store.view (s : Store) : View := Id.run do
  let root := (List.range s.parent.size).toArray.map (findRoot s.parent)
  let mut negC : Std.HashSet (Nat × Nat) := {}
  let mut negCList : Array (Nat × Nat) := #[]
  for (a, b) in s.negList do
    let e := (root[a]!, root[b]!)
    if !negC.contains e then
      negC := negC.insert e
      negCList := negCList.push e
  let mut adj : Std.HashMap Nat (Array Nat) := {}
  for (a, b) in s.leList do
    let ra := root[a]!
    adj := adj.insert ra ((adj.getD ra #[]).push root[b]!)
  -- up-sets by depth-first search from every source of a `≤` edge
  let mut ups : Std.HashMap Nat (Std.HashSet Nat) := {}
  for (x, _) in adj.toList do
    let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert x
    let mut stack : Array Nat := #[x]
    let mut fuel := 100000
    while stack.size > 0 && fuel > 0 do
      fuel := fuel - 1
      let y := stack.back!
      stack := stack.pop
      for z in adj.getD y #[] do
        if !seen.contains z then
          seen := seen.insert z
          stack := stack.push z
    ups := ups.insert x seen
  let cl := fun (φ : PLLFormula) => (s.ids.get? (key φ)).map (fun i => root[i]!)
  return { root, negC, negCList, ups, botC := cl .falsePLL, topC := cl topF }

def View.leq (v : View) (x y : Nat) : Bool :=
  x == y || some x == v.botC || some y == v.topC ||
    (match v.ups.get? x with
     | some u => u.contains y
     | none => false)

inductive Ans where
  | le | nle | unknown
  deriving BEq, Repr, Inhabited

def Ans.str : Ans → String
  | .le => "le" | .nle => "nle" | .unknown => "unknown"

/-- Tiers K, U, O against a store.  Returns the answer, the tier and a
detail string. -/
def query (s : Store) (v : View) (φ ψ : PLLFormula) : Ans × String × String :=
  let k1 := key φ
  let k2 := key ψ
  if k1 == k2 then (.le, "K", "equal keys") else
  let ia := s.ids.get? k1
  let ib := s.ids.get? k2
  let ca := ia.map (fun i => v.root[i]!)
  let cb := ib.map (fun i => v.root[i]!)
  let kfact : Option (Ans × String × String) :=
    match ia, ib with
    | some a, some b =>
        if s.pos.contains (a, b) then some (.le, "K", "stored ≤")
        else (s.neg.get? (a, b)).map (fun src => (.nle, "K", src))
    | _, _ => none
  match kfact with
  | some r => r
  | none =>
  match ca, cb with
  | some x, some y =>
      if x == y then (.le, "U", "one interd class") else
      if v.negC.contains (x, y) then (.nle, "U", "stored ⊬ between the classes") else
      if some x == v.botC || some y == v.topC then (.le, "O", "⊥ least / ⊤ greatest") else
      if v.leq x y then (.le, "O", "≤ chain") else
      if v.negCList.any (fun (a', b') => v.leq a' x && v.leq y b') then
        (.nle, "O", "⊬ propagated along ≤")
      else (.unknown, "none", "")
  | some x, none =>
      if some x == v.botC then (.le, "O", "⊥ least") else (.unknown, "none", "")
  | none, some y =>
      if some y == v.topC then (.le, "O", "⊤ greatest") else (.unknown, "none", "")
  | none, none => (.unknown, "none", "")

/-! ## The decider (public: G4c + FinCM) -/


/-- One decider call: answer, detail, certificate size (G4c term source
length in characters, or FinCM worlds), whether the NODE BUDGET ran out,
and the closure size when the emit stage was skipped for its cap. -/
structure Dec where
  ans : Ans
  detail : String
  size : Nat
  budgetHit : Bool
  closure : Option Nat

def decideCell (φ ψ : PLLFormula) (budget cap : Nat) : Dec :=
  match PLLND.Search.verdictWhy [φ] ψ
      { PLLND.Search.budgetedConfig with findBudget := some budget, emitClosureCap := cap } with
  | .proved t => ⟨.le, "G4c proof term", t.src.length, false, none⟩
  | .refuted M w _ => ⟨.nle, s!"FinCM model, {M.n} worlds, world {w}", M.n, false, none⟩
  | .unknown r =>
      ⟨.unknown, r.describe, 0,
       (match r with | .budgetExhausted _ => true | _ => false),
       (match r with | .closureTooBig s _ => some s | _ => none)⟩

/-- Run a decider call on its own thread with a wall-clock limit.  On a
timeout the call is abandoned (`none`); the answer it might have given is
not waited for. -/
def timed (ms : Nat) (f : Unit → Dec) : IO (Option Dec × Nat) := do
  let t0 ← IO.monoMsNow
  let task ← IO.asTask (prio := .dedicated) (IO.lazyPure f)
  repeat
    if ← IO.hasFinished task then break
    if (← IO.monoMsNow) - t0 > ms then break
    IO.sleep 10
  let el := (← IO.monoMsNow) - t0
  if ← IO.hasFinished task then
    match task.get with
    | .ok d => return (some d, el)
    | .error _ => return (none, el)
  else
    IO.cancel task
    return (none, el)

/-! ## Test sets -/

def rho (i : Nat) : PLLFormula := RhoOrder.rhoF i

def T1 : List (String × PLLFormula × PLLFormula) :=
  (List.range RhoOrder.n).flatMap fun i =>
    (List.range RhoOrder.n).filterMap fun j =>
      if i == j then none else some (s!"ρ{i} ⊢? ρ{j}", rho i, rho j)

open RNReps in
def designed : List (String × PLLFormula) :=
  [ ("q12", q12), ("q13", q13),
    ("q5 ∨ q8 [esc; canon = ρ15]", q5.or q8),
    ("q10 ↠ q4 [esc; = ρ13]", q10.ifThen q4),
    ("q10 ∧ q13 [esc]", q10.and q13),
    ("◯q11 [esc]", q11.somehow),
    ("q10 ↠ q7 [esc]", q10.ifThen q7),
    ("q8 ↠ q4 [esc]", q8.ifThen q4),
    ("rung 2 = subOb (sLad 2)", PLLND.LaxInfinite.subOb (PLLND.LaxInfinite.sLad 2)),
    ("rung 3 = subOb (sLad 3)", PLLND.LaxInfinite.subOb (PLLND.LaxInfinite.sLad 3)) ]

def T2 : List (String × String × PLLFormula × PLLFormula) :=
  designed.flatMap fun (nm, x) =>
    (List.range RhoOrder.n).flatMap fun j =>
      [ (nm, s!"X ⊢? ρ{j}", x, rho j), (nm, s!"ρ{j} ⊢? X", rho j, x) ]

/-- The ◯-free smoke set: closed formulas of the two-element algebra. -/
def smoke : List (String × PLLFormula) :=
  let b : PLLFormula := .falsePLL
  let t := topF
  [ ("⊥", b), ("⊤", t), ("¬⊤", .ifThen t b), ("¬¬⊤", .ifThen (.ifThen t b) b),
    ("(⊥ ∨ ⊤) ∧ (⊤ ↠ ⊤)", .and (.or b t) (.ifThen t t)),
    ("(⊤ ∧ ⊥) ∨ (¬⊤ ∧ ⊤)", .or (.and t b) (.and (.ifThen t b) t)) ]

def boolEval : PLLFormula → Option Bool
  | .falsePLL => some false
  | .and a b => do pure ((← boolEval a) && (← boolEval b))
  | .or a b => do pure ((← boolEval a) || (← boolEval b))
  | .ifThen a b => do pure (!(← boolEval a) || (← boolEval b))
  | _ => none

/-! ## Main -/

structure Cell where
  run : String
  set : String
  group : String
  name : String
  lhs : PLLFormula
  rhs : PLLFormula
  ans : Ans
  tier : String
  detail : String
  storeNs : Nat
  decMs : Nat
  certSize : Nat
  reused : Bool := false

def Cell.json (c : Cell) : String :=
  (Json.mkObj
    [("run", js c.run), ("set", js c.set), ("group", js c.group), ("name", js c.name),
     ("lhs", js (pp c.lhs)), ("rhs", js (pp c.rhs)), ("ans", js c.ans.str),
     ("tier", js c.tier), ("detail", js c.detail), ("store_ns", toJson c.storeNs),
     ("decider_ms", toJson c.decMs), ("cert_size", toJson c.certSize),
     ("decider_reused", toJson c.reused)]).compress

/-- Decider results by key pair, shared by the runs, so a cell is decided
once: (answer, tier, detail, size, ms). -/
abbrev Memo := IO.Ref (Std.HashMap (String × String) (Ans × String × String × Nat × Nat))

/-- The decider ladder, each call under a wall-clock limit:

* `D`:  node budget 200000, emit closure cap 12 (the defaults), 30 s;
* `D2`: on a NODE-BUDGET cutoff only, node budget 2000000, 120 s;
* `D3`: when only the emit stage's closure cap (12) stopped it and the
  closure has at most 16 formulas, emit cap 16, 120 s.

Every other `unknown` (all stages ran and missed) is left unknown: a
larger budget repeats the same search. -/
def decideLadder (φ ψ : PLLFormula) : IO (Ans × String × String × Nat × Nat) := do
  let (r1, e1) ← timed 30000 (fun _ => decideCell φ ψ 200000 12)
  match r1 with
  | none => return (.unknown, "none", s!"timeout after {e1} ms at node budget 200000", 0, e1)
  | some d =>
    if d.ans != .unknown then return (d.ans, "D", d.detail, d.size, e1)
    if d.budgetHit then
      let (r2, e2) ← timed 120000 (fun _ => decideCell φ ψ 2000000 12)
      match r2 with
      | some d2 =>
          if d2.ans != .unknown then return (d2.ans, "D2", d2.detail, d2.size, e1 + e2)
          return (.unknown, "none", s!"D2: {d2.detail}", 0, e1 + e2)
      | none => return (.unknown, "none", s!"D2: timeout after {e2} ms at node budget 2000000", 0, e1 + e2)
    match d.closure with
    | some s =>
        if s ≤ 16 then
          let (r3, e3) ← timed 120000 (fun _ => decideCell φ ψ 200000 16)
          match r3 with
          | some d3 =>
              if d3.ans != .unknown then return (d3.ans, "D3", d3.detail, d3.size, e1 + e3)
              return (.unknown, "none", s!"D3: {d3.detail}", 0, e1 + e3)
          | none => return (.unknown, "none", s!"D3: timeout after {e3} ms at emit cap 16", 0, e1 + e3)
        else return (.unknown, "none", d.detail, 0, e1)
    | none => return (.unknown, "none", d.detail, 0, e1)

/-- Ask one cell: the store tiers, then (if `useDecider`) the decider
ladder. -/
def ask (memo : Memo) (s : Store) (v : View) (run set group name : String)
    (φ ψ : PLLFormula) (useDecider : Bool) : IO Cell := do
  let t0 ← IO.monoNanosNow
  let (a, tier, det) ← IO.lazyPure (fun _ => query s v φ ψ)
  let t1 ← IO.monoNanosNow
  let base : Cell := { run, set, group, name, lhs := φ, rhs := ψ, ans := a, tier,
                       detail := det, storeNs := t1 - t0, decMs := 0, certSize := 0 }
  if a != .unknown || !useDecider then return base
  let k := (key φ, key ψ)
  let cached := (← memo.get).get? k
  if let some (a', t', det', sz, ms) := cached then
    return { base with ans := a', tier := t', detail := det', decMs := ms,
                       certSize := sz, reused := true }
  let r ← decideLadder φ ψ
  memo.modify (·.insert k r)
  let (a2, t2, det2, sz2, ms) := r
  return { base with ans := a2, tier := t2, detail := det2, decMs := ms, certSize := sz2 }

def summarise (label : String) (cs : Array Cell) : IO Unit := do
  let tiers := ["K", "U", "O", "D", "D2", "D3", "none"]
  let n := cs.size
  let line := tiers.map fun t => s!"{t} {(cs.filter (·.tier == t)).size}"
  let le := (cs.filter (·.ans == .le)).size
  let nle := (cs.filter (·.ans == .nle)).size
  let sns := cs.foldl (fun acc c => acc + c.storeNs) 0
  let dms := cs.foldl (fun acc c => if c.reused then acc else acc + c.decMs) 0
  let dmax := cs.foldl (fun acc c => max acc c.decMs) 0
  IO.println s!"{label}: {n} cells; {String.intercalate ", " line}; ⊢ {le}, ⊬ {nle}; store time {sns / 1000} µs total; decider {dms} ms total (fresh runs), max {dmax} ms"
  (← IO.getStdout).flush

def emit (h : IO.FS.Handle) (c : Cell) : IO Unit := do
  h.putStrLn c.json
  h.flush

def main (args : List String) : IO UInt32 := do
  let path := args.headD "_out/f0s2-cells.jsonl"
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  let memo : Memo ← IO.mkRef {}
  -- the old store
  let b0 ← IO.monoNanosNow
  let mut s0 : Store := {}
  for e in RNDB.allEntries do
    s0 := s0.add e.claim.lhs e.claim.rhs e.claim.rel e.id
  let v0 := s0.view
  let b1 ← IO.monoNanosNow
  let maxRounds := RNDB.allEntries.foldl
    (fun acc e => max acc (max (canonFix e.claim.lhs).2 (canonFix e.claim.rhs).2)) 0
  IO.println s!"old store: {s0.facts} facts, {s0.parent.size} keys, {v0.negCList.size} class-level ⊬, {s0.leList.size} ≤ (le) facts; built in {(b1 - b0) / 1000000} ms; canonFix needs at most {maxRounds} changing rounds"
  -- T0: the ◯-free smoke test
  let mut c0 : Array Cell := #[]
  for (nm, x) in smoke do
    IO.println s!"  smoke key: {nm} ↦ {pp (canonFix x).1} (Boolean value {repr (boolEval x)})"
    for (cn, φ, ψ) in [("X ⊢? ⊥", x, PLLFormula.falsePLL), ("⊥ ⊢? X", PLLFormula.falsePLL, x),
                       ("X ⊢? ⊤", x, topF), ("⊤ ⊢? X", topF, x)] do
      let c ← ask memo s0 v0 "old" "T0" nm cn φ ψ true
      emit h c
      c0 := c0.push c
  summarise "T0 smoke (old store)" c0
  -- T1: the 462 ρ-cells
  let mut c1 : Array Cell := #[]
  for (nm, φ, ψ) in T1 do
    let c ← ask memo s0 v0 "old" "T1" "rho" nm φ ψ true
    emit h c
    c1 := c1.push c
  summarise "T1 ρ-cells (old store)" c1
  -- bank the decider's T1 answers as base facts
  let mut s1 := s0
  let mut banked := 0
  for c in c1 do
    if c.tier.startsWith "D" then
      let rel := if c.ans == .le then RNDB.Rel.le else RNDB.Rel.nle
      s1 := s1.add c.lhs c.rhs rel s!"decided:{c.name}"
      banked := banked + 1
  let v1 := s1.view
  IO.println s!"banked {banked} decided T1 cells as base facts"
  -- T2 against the banked store, store tiers only
  let mut c3 : Array Cell := #[]
  for (g, nm, φ, ψ) in T2 do
    let c ← ask memo s1 v1 "banked" "T2" g nm φ ψ false
    emit h c
    c3 := c3.push c
  summarise "T2 designed (old store + banked T1 order, no decider)" c3
  -- T2 against the old store, with the decider
  let mut c2 : Array Cell := #[]
  for (g, nm, φ, ψ) in T2 do
    let c ← ask memo s0 v0 "old" "T2" g nm φ ψ true
    emit h c
    c2 := c2.push c
  summarise "T2 designed (old store, then decider)" c2
  -- T2 against the banked store, then the decider (results reused by key pair)
  let mut c4 : Array Cell := #[]
  for (g, nm, φ, ψ) in T2 do
    let c ← ask memo s1 v1 "banked+D" "T2" g nm φ ψ true
    emit h c
    c4 := c4.push c
  summarise "T2 designed (old store + banked T1 order, then decider)" c4
  -- no cell may get both verdicts across runs
  let mut clash := 0
  for (a, b) in (c2.toList.zip c4.toList) do
    if a.ans != .unknown && b.ans != .unknown && a.ans != b.ans then clash := clash + 1
  for (a, b) in (c3.toList.zip c4.toList) do
    if a.ans != .unknown && b.ans != .unknown && a.ans != b.ans then clash := clash + 1
  IO.println s!"verdict clashes between runs: {clash}"
  (← IO.getStdout).flush
  -- abandoned decider threads (timeouts) must not hold the process open
  IO.Process.exit (if clash == 0 then 0 else 2)

end F0S2

def main (args : List String) : IO UInt32 := F0S2.main args
