/-
# The `TagLeafV` census probe — is the lift's residual interface reachable,
and where is it already dischargeable?

`wip/minmodv_liftmain.lean` reduces `hloc` to ONE named interface:

    TagLeafV K G : ∀ w C, C ∈ Sf^R(G) → w ⊮ C → (C prime ∨ C = C₁∨C₂) →
                   circPart (Λ*_w) ≠ [] → (∃ c, Rm w c ∧ c ≠ w ∧ c ⊩ C) →
                   RegWitV K G w C

`wip/frjv_probe.lean` probes the STATEMENT (LIFT); this file probes the
INTERFACE.  Two questions, in order:

1. **Census.**  How many `(M, G, w, C)` configurations meeting the
   `TagLeafV` precondition occur at all?  (A detector that never fires
   proves nothing, so the census runs against a watched positive control
   — `M2q`, `G = ◯p ⊃ q`, `w = 0`, `C = q` — which MUST be flagged.)

2. **Discharge classification.**  `Kripke.circPart_lamStar_nil_of_coneTrivial`
   (`FRJ/Complete.lean`) says a cone-trivial world is `Λ*`-circ-free.  So
   whenever some `v` with `w ≤ v`, `ConeTrivial v`, `v ⊮ C` exists, the
   demand can be re-anchored at `v`, where the BARREN joins of round 1
   fire and the wit floats back down (`ht` drops strictly, since `w` is
   circ-carrying and `v` is not, so `v ≠ w`).  Call such a `v` a
   **CT-refuter**.  Configurations WITH a CT-refuter are dischargeable
   by that move; configurations WITHOUT one are the genuine residue.

3. For the residue only: run the typed V-engine and look for a row that
   inhabits `RegWitV` outright — `rhs = C`, tag barren or `chain W` with
   `Covers ctx W C`, and `Λ*_v ⊆ ctx` for some `v ≥ w` (literal, as the
   structure demands; the `Clo`-relaxed test is reported alongside,
   since that is all the CONSUMER — `circNotIn` — actually needs).

Verdict vocabulary: an engine MISS is not-found-within-bound, never a
verdict; all binding caps are printed.

The `PM` battery scaffolding is duplicated from `wip/frjv_probe.lean`
on purpose: that file is an executable root (it defines `main`), so it
cannot be imported here, and a probe is a disposable instrument.  The
two `circ`-carrying detectors are cross-checked against each other by
the `wf`-gate below.
-/
import FRJ.Search.Core
import FRJ.Search.OpsV

open FRJ FRJ.Search Form

namespace TagLeafProbe

/-! ## Mini-models (duplicated scaffolding — see the header) -/

structure PM where
  name : String
  n : Nat
  le : Nat → Nat → Bool
  rm : Nat → Nat → Bool
  val : String → Nat → Bool

def worlds (M : PM) : List Nat := List.range M.n

def wf (M : PM) : Bool :=
  let ws := worlds M
  ws.all (fun a => M.le a a) &&
  ws.all (fun a => ws.all (fun b => ws.all (fun c =>
    !(M.le a b && M.le b c) || M.le a c))) &&
  ws.all (fun a => M.rm a a) &&
  ws.all (fun a => ws.all (fun b => ws.all (fun c =>
    !(M.rm a b && M.rm b c) || M.rm a c))) &&
  ws.all (fun a => ws.all (fun b => !(M.rm a b) || M.le a b)) &&
  ["p", "q"].all (fun s => ws.all (fun a => ws.all (fun b =>
    !(M.le a b && M.val s a) || M.val s b)))

def force (M : PM) : Form → Nat → Bool
  | .atom s, w => M.val s w
  | .bot, _ => false
  | .and a b, w => force M a w && force M b w
  | .or a b, w => force M a w || force M b w
  | .imp a b, w => (worlds M).all (fun v =>
      !(M.le w v) || !(force M a v) || force M b v)
  | .circ a, w => (worlds M).all (fun v =>
      !(M.le w v) || (worlds M).any (fun c => M.rm v c && force M a c))

def M2 : PM :=
  { name := "M2", n := 2
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 0 && b = 1)
    val := fun s w => s = "p" && w = 1 }

def M2q : PM :=
  { name := "M2q", n := 2
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 0 && b = 1)
    val := fun s w => (s = "p" || s = "q") && w = 1 }

def M3 : PM :=
  { name := "M3", n := 3
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 0 && b = 1)
    val := fun s w => (s = "p" && w ≥ 1) || (s = "q" && w = 2) }

def M3m : PM :=
  { name := "M3m", n := 3
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 1 && b = 2)
    val := fun s w => (s = "p" && w = 2) || (s = "q" && w ≥ 1) }

def M3f : PM :=
  { name := "M3f", n := 3
    le := fun a b => a = b || a = 0
    rm := fun a b => a = b || (a = 0 && b = 1)
    val := fun s w => (s = "p" && w ≥ 1) || (s = "q" && w = 2) }

def M4 : PM :=
  { name := "M4", n := 4
    le := fun a b => a = b || a = 0 || b = 3
    rm := fun a b => a = b || (a = 0 && b = 1) || (a = 2 && b = 3)
    val := fun s w => (s = "p" && (w = 1 || w = 3)) || (s = "q" && (w = 2 || w = 3)) }

def M4c : PM :=
  { name := "M4c", n := 4
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 0 && b = 2) || (a = 1 && b = 2)
    val := fun s w => (s = "p" && w ≥ 2) || (s = "q" && w = 3) }

def M4r : PM :=
  { name := "M4r", n := 4
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 0 && b = 1) || (a = 2 && b = 3)
    val := fun s w => (s = "p" && w ≥ 1) || (s = "q" && w = 3) }

def M3d : PM :=
  { name := "M3d", n := 3
    le := fun a b => a ≤ b
    rm := fun a b => a = b || a < b
    val := fun s w => (s = "p" && w ≥ 1) || (s = "q" && w = 2) }

/-- Negative control for the wellformedness gate: `rm ⊄ le`. -/
def Mbad : PM :=
  { name := "Mbad", n := 2
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 1 && b = 0)
    val := fun _ _ => false }

def battery : List PM := [M2, M2q, M3, M3m, M3f, M4, M4c, M4r, M3d]

/-! ## `Λ*`, cone-triviality, and the interface predicate -/

/-- `⊩*`, transcribed from `Kripke.forceStar` (`FRJ/Complete.lean`). -/
def forceStarPM (M : PM) : Form → Nat → Bool
  | .atom p, w => M.val p w
  | .imp A B, w => force M (.imp A B) w && !(force M A w)
  | .circ A, w => force M (.circ A) w && !(force M A w)
  | _, _ => false

/-- `Λ*_w`, transcribed from `lamStar`. -/
def lamStarPM (M : PM) (G : Form) (w : Nat) : List Form :=
  (sfL G).filter (fun H => forceStarPM M H w)

/-- `w` is circ-carrying for `G`: `circPart (Λ*_w) ≠ []`. -/
def circCarryingW (M : PM) (G : Form) (w : Nat) : Bool :=
  !(circPart (lamStarPM M G w)).isEmpty

/-- The independent detector of `wip/frjv_probe.lean`, kept as a
cross-check on `lamStarPM`. -/
def circCarryingAlt (M : PM) (G : Form) (w : Nat) : Bool :=
  (sfL G).any (fun X => match X with
    | .circ Y => force M (.circ Y) w && !(force M Y w)
    | _ => false)

/-- `ConeTrivial w`: the modal cone of `w` is `{w}`. -/
def coneTrivial (M : PM) (w : Nat) : Bool :=
  (worlds M).all (fun c => !(M.rm w c) || c == w)

/-- A CT-refuter for `(w, C)`: `w ≤ v`, `ConeTrivial v`, `v ⊮ C`.  A
special case of the strict-refuter walk (a circ-carrying `w` is never
cone-trivial, so `v ≠ w`), kept as a separate statistic. -/
def ctRefuter (M : PM) (w : Nat) (C : Form) : Option Nat :=
  (worlds M).find? (fun v => M.le w v && coneTrivial M v && !(force M C v))

/-- **Move 1, the coverage re-anchor** (`axAnchor`, mechanised in
`wip/minmodv_liftmain.lean`): some `v ≥ w` whose `Λ*` fits inside the
`Ax^R` context `Ĝ_at \ {C}`.  Prime goals only — `Ax^R` needs primality. -/
def axAnchor (M : PM) (G : Form) (w : Nat) (C : Form) : Option Nat :=
  if C.isPrime then
    (worlds M).find? (fun v => M.le w v &&
      (lamStarPM M G v).all (fun X => (rm (gAt G) C).contains X))
  else none

/-- **Move 2, the strict-refuter walk** (`strictRef`): some `v > w` still
refuting `C`.  `ht` drops there, so the recursion re-anchors. -/
def strictRef (M : PM) (w : Nat) (C : Form) : Option Nat :=
  (worlds M).find? (fun v => M.le w v && !(v == w) && !(force M C v))

/-- The `TagLeafV` goal shapes: prime or a disjunction. -/
def tlShape (C : Form) : Bool :=
  C.isPrime || (match C with | .or _ _ => true | _ => false)

/-- The `TagLeafV` precondition at `(w, C)`. -/
def tlConfig (M : PM) (G : Form) (w : Nat) (C : Form) : Bool :=
  tlShape C && !(force M C w) && circCarryingW M G w &&
  (worlds M).any (fun c => M.rm w c && !(c == w) && force M C c)

def tlConfigs (M : PM) (G : Form) : List (Nat × Form) :=
  (worlds M).flatMap (fun w =>
    (sfR G).filterMap (fun C => if tlConfig M G w C then some (w, C) else none))

/-! ## The `RegWitV` test against an engine row -/

def tOKB (t : Tag) (ctx : List Form) (C : Form) : Bool :=
  match t with
  | .barren => true
  | .chain W => coversB ctx W C
  | .blocked => false

/-- `∃ v ≥ w` with `Λ*_v ⊆ ctx` — the `RegWitV.cov` field, literally. -/
def covLit (M : PM) (G : Form) (w : Nat) (ctx : List Form) : Option Nat :=
  (worlds M).find? (fun v => M.le w v && (lamStarPM M G v).all (fun X => ctx.contains X))

/-- The `Clo`-relaxed variant — what `circNotIn` actually consumes. -/
def covClo (M : PM) (G : Form) (w : Nat) (ctx : List Form) : Option Nat :=
  (worlds M).find? (fun v => M.le w v && (lamStarPM M G v).all (fun X => cloB ctx X))

/-! ## Pretty-printing -/

def ppF : Form → String
  | .atom p => p
  | .bot => "⊥"
  | .and a b => s!"({ppF a}∧{ppF b})"
  | .or a b => s!"({ppF a}∨{ppF b})"
  | .imp a b => s!"({ppF a}⊃{ppF b})"
  | .circ a => s!"◯{ppF a}"

def ppTag : Tag → String
  | .barren => "barren" | .chain D => s!"chain {ppF D}" | .blocked => "blocked"

def ppL (l : List Form) : String := String.intercalate "," (l.map ppF)

/-! ## Goal enumeration (duplicated scaffolding) -/

def leaves : List Form := [.atom "p", .atom "q", .bot]

def genTable (n : Nat) : Array (Array Form) := Id.run do
  let mut t : Array (Array Form) := #[#[], leaves.toArray]
  for s in [2:n+1] do
    let mut cur : Array Form := (t.getD (s-1) #[]).map Form.circ
    for sa in [1:s-1] do
      for a in t.getD sa #[] do
        for b in t.getD (s-1-sa) #[] do
          cur := cur.push (.and a b)
          cur := cur.push (.or a b)
          cur := cur.push (.imp a b)
    t := t.push cur
  return t

def genUpTo (n : Nat) : List Form :=
  ((genTable n).foldl (· ++ ·) #[]).toList

def caps (st : Stats) : String :=
  s!"lamCapped={st.lamCapped} dbCapped={st.dbCapped} jmaxB={st.jmaxBinding} pmaxB={st.pmaxBinding} rounds={st.roundsUsed}"

/-! ## The census -/

/-- The watched positive control: `M2q`, `G = ◯p ⊃ q`, `w = 0`, `C = q`.
`0 ⊩ ◯p` (the `Rm`-edge reaches `p` at 1) and `0 ⊮ p`, so `◯p ∈ Λ*_0`;
`0 ⊮ q` while `1 ⊩ q` and `Rm 0 1`.  The detector MUST flag it, and it
must have NO CT-refuter (world 1 is the only cone-trivial world `≥ 0`,
and it forces `q`) — i.e. the control is a genuine residue cell. -/
def ctrlG : Form := .imp (.circ (.atom "p")) (.atom "q")

def gate : IO Bool := do
  for M in battery do
    if !wf M then
      IO.println s!"WF-FAIL {M.name} — battery model malformed, ABORT"
      return false
  if wf Mbad then
    IO.println "GATE-FAIL: Mbad passed wf — the gate is broken, ABORT"
    return false
  -- the two circ-carrying detectors must agree everywhere on the battery
  for M in battery do
    for G in genUpTo 4 do
      for w in worlds M do
        if circCarryingW M G w != circCarryingAlt M G w then
          IO.println s!"DETECTOR-DISAGREE {M.name}@{w} {ppF G} — ABORT"
          return false
  -- the watched positive control
  if !tlConfig M2q ctrlG 0 (.atom "q") then
    IO.println "CONTROL-FAIL: the tl-detector missed the watched control — ABORT"
    return false
  if (ctRefuter M2q 0 (.atom "q")).isSome then
    IO.println "CONTROL-FAIL: the control acquired a CT-refuter — ABORT"
    return false
  if (strictRef M2q 0 (.atom "q")).isSome then
    IO.println "CONTROL-FAIL: the control acquired a strict refuter — ABORT"
    return false
  -- and the control MUST be closed by move 1 (Λ*_1 = {p} ⊆ Ĝ_at \ {q}):
  -- a watched POSITIVE for the coverage re-anchor
  if (axAnchor M2q ctrlG 0 (.atom "q")).isNone then
    IO.println "CONTROL-FAIL: move 1 missed the control cell — ABORT"
    return false
  IO.println s!"== gates: {battery.length} models wf, Mbad rejected, detectors agree, control flagged =="
  return true

structure Cell where
  mname : String
  G : Form
  w : Nat
  C : Form

def censusMain (sizeCap : Nat) (rounds lam : Nat) : IO Unit := do
  if !(← gate) then return
  let cfg : Config := { rounds := rounds, lamCap := lam, maxRS := 4000, maxIS := 4000 }
  let all := genUpTo sizeCap
  IO.println s!"== goals: {all.length} formulas of size ≤ {sizeCap} over p,q,⊥ =="
  let mut nCfg := 0
  let mut nAx := 0
  let mut nWalk := 0
  let mut nCT := 0
  let mut residue : List Cell := []
  for G in all do
    for M in battery do
      for (w, C) in tlConfigs M G do
        nCfg := nCfg + 1
        if (ctRefuter M w C).isSome then nCT := nCT + 1
        if (axAnchor M G w C).isSome then
          nAx := nAx + 1
        else if (strictRef M w C).isSome then
          nWalk := nWalk + 1
        else
          residue := { mname := M.name, G := G, w := w, C := C } :: residue
  IO.println s!"== tl-configurations (round-2 interface): {nCfg} =="
  IO.println s!"==   closed by move 1, the coverage re-anchor Ax^R: {nAx}"
  IO.println s!"==   closed by move 2, the strict-refuter walk:     {nWalk}  (of which cone-trivial: {nCT})"
  IO.println s!"==   RESIDUE (round-3 interface, both moves fail):  {residue.length} =="
  -- the residue, run against the engine
  let mut solved := 0
  let mut solvedClo := 0
  let mut open' : List Cell := []
  for cell in residue.reverse do
    let M := (battery.find? (fun m => m.name == cell.mname)).getD M2
    let (db, st) := saturateO (V.vOps cell.G) cfg
    let rows := db.rs.filterMap (fun r =>
      if r.rhs = cell.C && tOKB r.t r.ctx cell.C then some (r.t, r.ctx) else none)
    let lit := rows.filterMap (fun (t, ctx) =>
      (covLit M cell.G cell.w ctx).map (fun v => (t, ctx, v)))
    let clo := rows.filterMap (fun (t, ctx) =>
      (covClo M cell.G cell.w ctx).map (fun v => (t, ctx, v)))
    let tag := s!"[{cell.mname} @ {cell.w}] {ppF cell.G} :: {ppF cell.C}"
    match lit, clo with
    | (t, ctx, v) :: _, _ =>
        solved := solved + 1
        IO.println s!"RESIDUE-SOLVED {tag} — row[{ppTag t}] wld={v} ctx={ppL ctx}"
    | [], (t, ctx, v) :: _ =>
        solvedClo := solvedClo + 1
        IO.println s!"RESIDUE-CLO-ONLY {tag} — row[{ppTag t}] wld={v} ctx={ppL ctx}"
    | [], [] =>
        open' := cell :: open'
        IO.println s!"RESIDUE-OPEN {tag}  Lam*={ppL (lamStarPM M cell.G cell.w)}  tOK-rows={rows.length}  {caps st}"
    (← IO.getStdout).flush
  IO.println s!"== residue verdicts: RegWitV rows found (literal cov) {solved}; Clo-only {solvedClo}; none-within-bound {open'.length} =="
  if open'.isEmpty then
    IO.println "TAGLEAF-PROBE: every residue cell carries a RegWitV row — the interface is unrefuted at this stratum"
  else
    IO.println s!"TAGLEAF-PROBE: {open'.length} residue cells with no RegWitV row within bound — candidate separating cells"

/-- Dump one cell in full: `Λ*` at every world, the cone data, and every
engine row with the goal on the right. -/
def inspectMain (mname : String) (G : Form) (w : Nat) (C : Form)
    (rounds lam : Nat) : IO Unit := do
  let M := (battery.find? (fun m => m.name == mname)).getD M2
  let cfg : Config := { rounds := rounds, lamCap := lam, maxRS := 4000, maxIS := 4000 }
  IO.println s!"== {mname} @ {w}: G = {ppF G}, C = {ppF C}"
  for v in worlds M do
    IO.println s!"  world {v}: Λ*={ppL (lamStarPM M G v)} coneTrivial={coneTrivial M v} forceC={force M C v} le({w},{v})={M.le w v}"
  IO.println s!"  tlConfig={tlConfig M G w C}  ctRefuter={ctRefuter M w C}"
  let (db, st) := saturateO (V.vOps G) cfg
  IO.println s!"  engine: RS={db.rs.length} IS={db.is.length} {caps st}"
  IO.println "  -- rows deriving the GOAL G:"
  for r in db.rs do
    if r.rhs = G then
      IO.println s!"   G[{ppTag r.t}] ctx={ppL r.ctx}"
  IO.println "  -- rows deriving C:"
  for r in db.rs do
    if r.rhs = C then
      IO.println s!"   R[{ppTag r.t}] tOK={tOKB r.t r.ctx C} covLit={covLit M G w r.ctx} covClo={covClo M G w r.ctx} ctx={ppL r.ctx}"

def main (args : List String) : IO Unit := do
  match args.head? with
  | some "control" =>
      inspectMain "M2q" ctrlG 0 (.atom "q")
        (((args.getD 1 "10").toNat?).getD 10) (((args.getD 2 "16").toNat?).getD 16)
  | some "counit" =>
      inspectMain "M2" (.imp (.circ (.atom "p")) (.atom "p")) 0 (.atom "p")
        (((args.getD 1 "10").toNat?).getD 10) (((args.getD 2 "16").toNat?).getD 16)
  | _ =>
      let sz := ((args.getD 0 "5").toNat?).getD 5
      let rounds := ((args.getD 1 "10").toNat?).getD 10
      let lam := ((args.getD 2 "16").toNat?).getD 16
      censusMain sz rounds lam

end TagLeafProbe

def main (args : List String) : IO Unit := TagLeafProbe.main args
