/-
# The hloc-lift refute-first probe

Target statement (the lift of `completenessV`'s `hloc`):

    (LIFT)  K.Infallible → ¬ K.valid G → ProvableV G      [no hloc]

Closed formulas are constant across infallible models (`◯⊥ ≡ ⊥` there),
so the ρ-matrix cannot test (LIFT): the genuine test space is
VARIABLE-CARRYING goals refuted on infallible models with a
CIRC-CARRYING world (some `◯Y ∈ Sf^L(G)` with `b ⊩ ◯Y`, `b ⊮ Y` — the
worlds where `hloc` fails and the promise joins must carry the load).

The probe: a battery of small infallible models (hand-built, wellformed-
checked with a WATCHED-FAIL negative control), an exhaustive goal
enumeration over {p, q, ⊥} up to a size cap, a forcing screen, and the
typed V-engine (`vOps` — promise + fallible joins included, a HIT is an
`FRJVr` derivation) on every survivor.  Verdict vocabulary per the
repo discipline: a MISS is not-found-within-bound, never a verdict —
all binding caps are printed.  TARGET survivors (refuted at a
circ-carrying configuration, engine-missed at raised budget) are the
candidate separating cells for (LIFT); if none survive, the statement
has passed this stratum and the port build can be scoped.

Controls: the Peirce cell `(◯p⊃q)⊃q` and the flight cell `(◯w⊃q)⊃◯w`
(both ProvableV, both refuted on fallible models only — they must HIT);
plus every hloc-satisfying refuted survivor (completenessV proves these
ProvableV, so a MISS there is an engine-budget signal, not a lift
signal).
-/
import FRJ.Search.Core
import FRJ.Search.OpsV

open FRJ FRJ.Search Form

namespace FRJVProbe

/-! ## Mini-models: worlds are `Nat`s below `n` -/

structure PM where
  name : String
  n : Nat
  le : Nat → Nat → Bool
  rm : Nat → Nat → Bool
  val : String → Nat → Bool

def worlds (M : PM) : List Nat := List.range M.n

/-- Wellformedness: `le` preorder, `rm` reflexive-transitive
sub-relation of `le`, valuation monotone. -/
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

/-- Forcing, structurally on the formula. -/
def force (M : PM) : Form → Nat → Bool
  | .atom s, w => M.val s w
  | .bot, _ => false
  | .and a b, w => force M a w && force M b w
  | .or a b, w => force M a w || force M b w
  | .imp a b, w => (worlds M).all (fun v =>
      !(M.le w v) || !(force M a v) || force M b v)
  | .circ a, w => (worlds M).all (fun v =>
      !(M.le w v) || (worlds M).any (fun c => M.rm v c && force M a c))

/-- A circ-carrying world for `G`: some `◯Y ∈ Sf^L(G)` forced with `Y`
refuted — exactly a `forceStar` `◯`-member, i.e. a world where `hloc`
fails. -/
def circCarrying (M : PM) (G : Form) (w : Nat) : Bool :=
  (sfL G).any (fun X => match X with
    | .circ Y => force M (.circ Y) w && !(force M Y w)
    | _ => false)

/-! ## The battery -/

/-- 2-chain, `Rm`-edge to the top: root forces `◯p`, refutes `p`. -/
def M2 : PM :=
  { name := "M2", n := 2
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 0 && b = 1)
    val := fun s w => s = "p" && w = 1 }

/-- 2-chain with `q` at the top as well. -/
def M2q : PM :=
  { name := "M2q", n := 2
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 0 && b = 1)
    val := fun s w => (s = "p" || s = "q") && w = 1 }

/-- 3-chain 0<1<2, `Rm` = refl + (0,1): `0 ⊩ ◯p`, `0 ⊮ p`; `q` only at
the top separates. -/
def M3 : PM :=
  { name := "M3", n := 3
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 0 && b = 1)
    val := fun s w => (s = "p" && w ≥ 1) || (s = "q" && w = 2) }

/-- 3-chain, circ-carrying at the MIDDLE world: `Rm` = refl + (1,2),
`p` at the top only.  The root refutes `◯p` (its only `Rm`-successor is
itself), realising `(0,◯Z)`-demands below a circ-carrying world. -/
def M3m : PM :=
  { name := "M3m", n := 3
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 1 && b = 2)
    val := fun s w => (s = "p" && w = 2) || (s = "q" && w ≥ 1) }

/-- 3-fork: 0 < 1, 0 < 2 (1,2 incomparable), `Rm` = refl + (0,1); `p`
at both tips (so `0 ⊩ ◯p`), `q` at tip 2 only. -/
def M3f : PM :=
  { name := "M3f", n := 3
    le := fun a b => a = b || a = 0
    rm := fun a b => a = b || (a = 0 && b = 1)
    val := fun s w => (s = "p" && w ≥ 1) || (s = "q" && w = 2) }

/-- 4-diamond 0 < 1,2 < 3, `Rm` = refl + (0,1) + (2,3): two
circ-carrying worlds at different `◯`-depths; `p` at 1 and 3, `q` at 2
and 3. -/
def M4 : PM :=
  { name := "M4", n := 4
    le := fun a b => a = b || a = 0 || b = 3
    rm := fun a b => a = b || (a = 0 && b = 1) || (a = 2 && b = 3)
    val := fun s w => (s = "p" && (w = 1 || w = 3)) || (s = "q" && (w = 2 || w = 3)) }

/-- 4-chain, `Rm` = refl + (0,2) + (1,2): circ-carrying at 0 AND 1. -/
def M4c : PM :=
  { name := "M4c", n := 4
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 0 && b = 2) || (a = 1 && b = 2)
    val := fun s w => (s = "p" && w ≥ 2) || (s = "q" && w = 3) }

/-- 4-chain, `Rm` = refl + (0,1) + (2,3): circ-carriers at two levels
with DISJOINT pledge cones. -/
def M4r : PM :=
  { name := "M4r", n := 4
    le := fun a b => a ≤ b
    rm := fun a b => a = b || (a = 0 && b = 1) || (a = 2 && b = 3)
    val := fun s w => (s = "p" && w ≥ 1) || (s = "q" && w = 3) }

/-- 3-chain with DENSE `Rm` (refl + (0,1) + (0,2) + (1,2)). -/
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

/-! ## Goal enumeration over {p, q, ⊥} -/

def leaves : List Form := [.atom "p", .atom "q", .bot]

/-- Formulas by EXACT size (leaves size 1, `◯` adds 1, binary adds 1),
memoised: `(genTable n)[s]` holds every formula of size `s ≤ n`. -/
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

/-! ## Pretty-printing -/

def ppF : Form → String
  | .atom p => p
  | .bot => "⊥"
  | .and a b => s!"({ppF a}∧{ppF b})"
  | .or a b => s!"({ppF a}∨{ppF b})"
  | .imp a b => s!"({ppF a}⊃{ppF b})"
  | .circ a => s!"◯{ppF a}"

/-! ## The probe -/

/-- Screen: the least model in the battery refuting `G` somewhere, with
the classification of whether some world of that model is circ-carrying
for `G`. -/
def screen (G : Form) : Option (PM × Nat × Bool) :=
  battery.firstM (fun M =>
    match (worlds M).find? (fun w => !(force M G w)) with
    | some w => some (M, w, (worlds M).any (circCarrying M G))
    | none => none)

def runEngine (G : Form) (cfg : Config) : Bool × Stats :=
  let (db, st) := saturateO (V.vOps G) cfg
  (db.rs.any (fun r => decide (r.rhs = G)), st)

def caps (st : Stats) : String :=
  s!"lamCapped={st.lamCapped} dbCapped={st.dbCapped} jmaxB={st.jmaxBinding} pmaxB={st.pmaxBinding} rounds={st.roundsUsed}"

def probeMain (sizeCap : Nat) (rounds lam : Nat) : IO Unit := do
  -- wellformedness gate, with the watched negative control
  for M in battery do
    if !wf M then
      IO.println s!"WF-FAIL {M.name} — battery model malformed, ABORT"
      return
  if wf Mbad then
    IO.println "GATE-FAIL: Mbad passed wf — the gate is broken, ABORT"
    return
  IO.println s!"== wf gate: {battery.length} models pass, negative control fails =="
  let cfg : Config := { rounds := rounds, lamCap := lam, maxRS := 2000, maxIS := 2000 }
  let all := genUpTo sizeCap
  IO.println s!"== goals: {all.length} formulas of size ≤ {sizeCap} over p,q,⊥ =="
  let mut nRef := 0
  let mut nTarget := 0
  let mut nCtrl := 0
  let mut missT : List (Form × PM × Nat) := []
  let mut missC : List Form := []
  for G in all do
    match screen G with
    | none => pure ()
    | some (M, w, cc) =>
        nRef := nRef + 1
        if cc then
          nTarget := nTarget + 1
          let (hit, st) := runEngine G cfg
          if !hit then
            missT := (G, M, w) :: missT
            IO.println s!"TARGET-MISS {ppF G}  [{M.name} @ {w}]  {caps st}"
        else
          nCtrl := nCtrl + 1
          let (hit, _) := runEngine G cfg
          if !hit then
            missC := G :: missC
    (← IO.getStdout).flush
  IO.println s!"== screened: {nRef} refuted on the battery; {nTarget} at circ-carrying configurations (TARGETS), {nCtrl} hloc-controls =="
  IO.println s!"== TARGET misses: {missT.length}; control misses (engine-budget signals, completenessV covers them): {missC.length} =="
  for G in missC do
    IO.println s!"CTRL-MISS {ppF G}"
  if missT.isEmpty then
    IO.println "LIFT-PROBE: no target survivor at this stratum — (LIFT) unrefuted"
  else
    IO.println s!"LIFT-PROBE: {missT.length} candidate separating cells (escalate budget, then hand analysis)"

/-! ## Corpus replay: the repo's own hard shapes, variable-carried -/

def p : Form := .atom "p"
def q : Form := .atom "q"

/-- The classically-valid antecedent device of the residue cell. -/
def Acv : Form := .or p (.imp p q)

/-- Hard shapes: residue/flight/witness skeletons with variables, plus
nested-promise inventions.  Every member is screened against the whole
battery (not just the first refuting model). -/
def corpus : List (String × Form) :=
  [ ("residue-var", .imp (.imp Acv q) (.circ q)),
    ("flight-var", .imp (.imp (.circ p) q) (.circ p)),
    ("w80-var", .circ (.imp (.imp (.circ p) q) (.circ p))),
    ("peirce", .imp (.imp (.circ p) q) q),
    ("resid-deep", .imp (.imp Acv (.circ q)) (.circ q)),
    ("resid-conj", .imp (.imp Acv q) (.circ (.and q (.or p q)))),
    ("promise2", .imp (.imp (.circ p) (.circ q)) (.imp (.imp p q) (.circ q))),
    ("stack", .imp (.imp (.circ p) q) (.imp (.imp (.circ q) p) (.circ (.and p q)))),
    ("nest", .imp (.imp (.circ (.circ p)) q) (.circ (.or q (.circ p)))),
    ("antefloat", .imp (.imp (.imp p q) (.circ q)) (.circ (.imp p q))),
    ("bodyimp", .imp (.imp (.circ (.imp p q)) q) (.circ (.imp p q))),
    ("twocarry", .imp (.and (.imp (.circ p) q) (.imp (.circ q) p)) (.circ (.and p q))),
    ("orpush", .imp (.imp (.circ p) q) (.or (.circ q) (.circ (.and p q)))),
    ("mixed", .imp (.imp Acv (.circ q)) (.or q (.circ (.and q p)))) ]

def replayMain (rounds lam : Nat) : IO Unit := do
  let cfg : Config := { rounds := rounds, lamCap := lam, maxRS := 4000, maxIS := 4000 }
  IO.println s!"== corpus replay: {corpus.length} hard shapes × {battery.length} models (rounds={rounds} lamCap={lam}) =="
  for (nm, G) in corpus do
    let refs := battery.filterMap (fun M =>
      match (worlds M).find? (fun w => !(force M G w)) with
      | some w => some (M.name, w, (worlds M).any (circCarrying M G))
      | none => none)
    if refs.isEmpty then
      IO.println s!"{nm}: {ppF G} — VALID on the whole battery (no refutation; outside the statement here)"
    else
      let (hit, st) := runEngine G cfg
      let tgt := refs.any (fun (_, _, cc) => cc)
      let refStr := String.intercalate " " (refs.map (fun (n, w, cc) =>
        s!"{n}@{w}{if cc then "*" else ""}"))
      IO.println s!"{nm}: {ppF G} — refuted [{refStr}] {if tgt then "TARGET" else "control"} → {if hit then "HIT" else s!"MISS {caps st}"}"
    (← IO.getStdout).flush
  IO.println "(* = circ-carrying configuration)"

/-- Dump the V-engine's regular rows for one corpus goal — the
derivation shapes that will guide the port. -/
def inspectMain (nm : String) (rounds lam : Nat) : IO Unit := do
  match corpus.find? (fun (n, _) => n = nm) with
  | none => IO.println s!"unknown corpus goal {nm}"
  | some (_, G) =>
      let cfg : Config := { rounds := rounds, lamCap := lam, maxRS := 4000, maxIS := 4000 }
      let (db, st) := saturateO (V.vOps G) cfg
      IO.println s!"== {nm}: {ppF G}  {caps st} RS={db.rs.length} IS={db.is.length}"
      let ppTag : Tag → String
        | .barren => "barren" | .chain D => s!"chain {ppF D}" | .blocked => "blocked"
      for r in db.rs do
        IO.println s!"  R[{ppTag r.t}] {String.intercalate ", " (r.ctx.map ppF)} ⇒ {ppF r.rhs}"
      for i in db.is do
        IO.println s!"  I⟨{String.intercalate ", " (i.stab.map ppF)} ; {String.intercalate ", " (i.th.map ppF)}⟩ ⇒ {ppF i.rhs}"

def main (args : List String) : IO Unit := do
  match args.head? with
  | some "replay" =>
      replayMain (((args.getD 1 "10").toNat?).getD 10) (((args.getD 2 "16").toNat?).getD 16)
  | some "inspect" =>
      inspectMain (args.getD 1 "peirce") (((args.getD 2 "10").toNat?).getD 10)
        (((args.getD 3 "16").toNat?).getD 16)
  | _ =>
      let sz := ((args.getD 0 "6").toNat?).getD 6
      let rounds := ((args.getD 1 "10").toNat?).getD 10
      let lam := ((args.getD 2 "16").toNat?).getD 16
      probeMain sz rounds lam

end FRJVProbe

def main (args : List String) : IO Unit := FRJVProbe.main args
