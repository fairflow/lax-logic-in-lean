/-
THE JOIN SCREEN — the extensional attack on the multi-premise root
constructor, run BEFORE the Lean proofs of `Reject/Join.lean` were
scoped (repo CLAUDE.md, § Testing for counterexamples).

The candidate construction: a fresh root below the DISJOINT UNION of
premise models `M₀ … Mₙ₋₁`, with a `cone` declaring which component
worlds are `Rm`-successors of the new root.  Six statements are put
under attack, each with a CONTROL that must fail in the same run:

  A  constructor laws   — `wellB (join …)` for every cell
     control A′: an `Rm`-cone that is NOT `Rm`-upward closed must be
     REJECTED by `wellB` (otherwise the law is decorative)
  B  preservation       — forcing inside a component is unchanged
     control B′: a cross-linked join (Ri joining two components) must
     BREAK preservation (otherwise the check has no teeth)
  C  ◯ at the root      — the exact iff for `join ⊩ ◯A`
     control C′: the version WITHOUT the reflexive disjunct (the
     `boxHolds` incompleteness the audit found) must be REFUTED here
  D  confluence         — `confl (join …)` ⟺ components confluent AND
     the cone dominates; and the branching corollary
  E  boundary cells     — 0 components, 1 component (must degenerate
     to `addRoot`), one-world component, empty cone, fallible
     component
  F  soundness (adversarial) — no join model may witness a DERIVABLE
     sequent as refuted.  Corpus replay: the G4iLL blocker
     `◯((◯p⊃r)⊃◯p), ◯p⊃r ⇒ r` and six more, each certified derivable
     by the searcher in this same run
     control F′: the joins must REFUTE the intended target
     `¬◯⊥ ∨ ◯⊥` (a null result with nothing refuted is a broken pipe)

Verdicts are three-valued: `pass` / `fail` (certificate printed) /
`flag`.  One appended line per cell block; nothing is silently capped.
-/
import LaxLogic.PLLCountermodelEmit
import LaxLogic.PLLSearchConf
import Rewrite.Catalogue

open PLLND PLLND.FinCM

namespace JoinScreen

abbrev F := PLLFormula

/-- Three-valued verdict rendering (no nested string literals inside
`s!` interpolation). -/
def vd (b : Bool) : String := if b then "pass" else "FAIL"

/-- CONTROL-verdict rendering. -/
def cv (b : Bool) : String := if b then "pass (rejected)" else "FAIL (accepted!)"

/-- Derivability-verdict rendering. -/
def dv (b : Bool) : String := if b then "derivable" else "NOT SETTLED (flag)"

/-! ## The corpus (catalogue representatives + p-carrying cells) -/

def bot : F := .falsePLL
def top : F := .ifThen bot bot
def oBot : F := .somehow bot
def nOBot : F := .ifThen oBot bot
def nnOBot : F := .ifThen nOBot bot
def q4 : F := .or nOBot oBot
def q5 : F := .somehow nOBot
def q7 : F := .or nnOBot nOBot
def q9 : F := .or nnOBot q5
def q10 : F := .ifThen nnOBot oBot
def q11 : F := .or q10 nnOBot
def q8 : F := .ifThen q5 q4
def q14 : F := .ifThen q10 q5
def w16 : F := .ifThen q9 q4
def pv : F := .prop "p"
def qv : F := .prop "q"
def rv : F := .prop "r"

def corpus : List (String × F) :=
  [("⊥", bot), ("⊤", top), ("◯⊥", oBot), ("¬◯⊥", nOBot),
   ("¬◯⊥∨◯⊥", q4), ("¬¬◯⊥", nnOBot), ("¬¬◯⊥∨¬◯⊥", q7),
   ("◯¬◯⊥", q5), ("¬¬◯⊥⊃◯⊥", q10), ("¬¬◯⊥∨◯¬◯⊥", q9),
   ("(¬¬◯⊥⊃◯⊥)∨¬¬◯⊥", q11), ("g1", q8), ("r1", q14), ("w1", w16),
   ("p", pv), ("◯p", .somehow pv), ("p∨q", .or pv qv),
   ("◯(p∨q)", .somehow (.or pv qv)),
   ("◯p∨◯q", .or (.somehow pv) (.somehow qv)),
   ("p⊃q", .ifThen pv qv), ("(p⊃q)∨(q⊃p)", .or (.ifThen pv qv) (.ifThen qv pv)),
   ("◯◯p", .somehow (.somehow pv)), ("¬p", .ifThen pv bot),
   ("◯(p∧◯q)", .somehow (.and pv (.somehow qv)))]

/-! ## The FinCM-level join -/

def offAt (Ms : List FinCM) (i : Nat) : Nat :=
  1 + ((Ms.take i).map (·.n)).sum

def totW (Ms : List FinCM) : Nat := 1 + (Ms.map (·.n)).sum

/-- The candidate constructor, as computable data. -/
def finJoin (Ms : List FinCM) (cone : List (Nat × Nat))
    (atoms : List String) : FinCM :=
  { n := totW Ms
    ri := ((List.range (totW Ms)).filter (fun w => w != 0)).map (fun w => (0, w))
          ++ Ms.zipIdx.flatMap (fun p =>
               p.1.ri.map fun e => (offAt Ms p.2 + e.1, offAt Ms p.2 + e.2))
    rm := cone.map (fun c => (0, offAt Ms c.1 + c.2))
          ++ Ms.zipIdx.flatMap (fun p =>
               p.1.rm.map fun e => (offAt Ms p.2 + e.1, offAt Ms p.2 + e.2))
    fall := Ms.zipIdx.flatMap (fun p => p.1.fall.map (offAt Ms p.2 + ·))
    val := atoms.map (fun a => (0, a))
           ++ Ms.zipIdx.flatMap (fun p =>
                p.1.val.map fun e => (offAt Ms p.2 + e.1, e.2)) }

/-- CONTROL B′: the same join with an extra `Ri` link from every world
of component 0 to every world of component 1.  Still a well-formed
frame on the cells we run it on, but it destroys preservation. -/
def finJoinCross (Ms : List FinCM) (cone : List (Nat × Nat))
    (atoms : List String) : FinCM :=
  let J := finJoin Ms cone atoms
  match Ms with
  | M0 :: M1 :: _ =>
      { J with ri := J.ri ++
          (List.range M0.n).flatMap fun a =>
            (List.range M1.n).map fun b => (offAt Ms 0 + a, offAt Ms 1 + b) }
  | _ => J

def wf (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all (fun x => M.riB x x && M.rmB x x) &&
  ws.all (fun x => ws.all fun y => ws.all fun z =>
    (!(M.riB x y && M.riB y z) || M.riB x z) &&
    (!(M.rmB x y && M.rmB y z) || M.rmB x z)) &&
  ws.all (fun x => ws.all fun y =>
    (!(M.rmB x y) || M.riB x y) &&
    (!(M.fallB x && M.riB x y) || M.fallB y)) &&
  M.val.all (fun p => ws.all fun v => !(M.riB p.1 v) || M.valB v p.2)

def confl (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all fun x => ws.all fun w => ws.all fun v =>
    !(M.rmB x w && M.riB x v) || ws.any fun u => M.riB w u && M.rmB v u

/-! ## The cells -/

/-- one world, infallible, no atoms -/
def sIn : FinCM := ⟨1, [], [], [], []⟩
/-- one world, fallible -/
def sFal : FinCM := ⟨1, [], [], [0], []⟩
/-- one world where `p` holds -/
def sP : FinCM := ⟨1, [], [], [], [(0, "p")]⟩
/-- one world where `q` holds -/
def sQ : FinCM := ⟨1, [], [], [], [(0, "q")]⟩
/-- two worlds `0 <ᵢ 1`, `0 <ₘ 1`, `1` fallible: forces `◯⊥` at `0`
without `0` being fallible.  (This is `Reject.M₁` of `Demo.lean`.) -/
def chFal : FinCM := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩
/-- three worlds, a fork above a root; nothing fallible -/
def fork3 : FinCM := ⟨3, [(0, 1), (0, 2)], [], [], [(1, "p"), (2, "q")]⟩
/-- two worlds `0 <ᵢ 1` with `p` at the top only -/
def chP : FinCM := ⟨2, [(0, 1)], [], [], [(1, "p")]⟩

structure Cell where
  name : String
  comps : List FinCM
  cone : List (Nat × Nat)
  atoms : List String

def cells : List Cell :=
  [ -- boundary: no components at all
    ⟨"E0 empty component list", [], [], []⟩,
    -- boundary: a single component (must degenerate to addRoot)
    ⟨"E1 single component, full cone", [chFal], [(0, 0), (0, 1)], []⟩,
    ⟨"E1b single component, empty cone", [chFal], [], []⟩,
    -- boundary: one-world components
    ⟨"E2 one-world component", [sIn], [(0, 0)], []⟩,
    ⟨"E3 fallible component", [sFal], [(0, 0)], []⟩,
    ⟨"E3b fallible component, empty cone", [sFal], [], []⟩,
    -- the intended target: branching, empty modal cone
    ⟨"J2 two components, empty cone", [chFal, sIn], [], []⟩,
    ⟨"J2p p | q, empty cone", [sP, sQ], [], []⟩,
    ⟨"J2x sIn | chFal, empty cone", [sIn, chFal], [], []⟩,
    ⟨"J2c two components, cone in comp 0", [chFal, sIn], [(0, 0), (0, 1)], []⟩,
    ⟨"J2c' two components, cone in comp 1", [chFal, sIn], [(1, 0)], []⟩,
    -- frontier: three components
    ⟨"J3 three components, empty cone", [chFal, sIn, sP], [], []⟩,
    ⟨"J3c three components, cone in comp 2", [chFal, sIn, sP], [(2, 0)], []⟩,
    -- frontier: deeper components
    ⟨"J4 fork + chain", [fork3, chP], [], []⟩,
    ⟨"J4c fork + chain, cone in comp 1", [fork3, chP], [(1, 0), (1, 1)], []⟩,
    -- root atoms (hereditary only if every component world has them)
    ⟨"A1 root atom p, components force p", [sP, sP], [], ["p"]⟩ ]

/-- CONTROL A′: cones that are NOT `Rm`-upward closed.  `wellB` must
reject the resulting frame. -/
def badCells : List Cell :=
  [ ⟨"A′ cone {0} but 0 <ₘ 1", [chFal], [(0, 0)], []⟩,
    ⟨"A′ root atom p, component lacks p", [sIn], [], ["p"]⟩ ]

/-! ## Section A — constructor laws -/

def sectionA : IO Bool := do
  let mut ok := true
  for c in cells do
    let J := finJoin c.comps c.cone c.atoms
    let good := wf J && J.wellB
    IO.println s!"A {vd good}  {c.name}  (n={J.n})"
    if !good then ok := false
  IO.println ""
  IO.println "A′ CONTROL — unlawful cells must be REJECTED:"
  for c in badCells do
    let J := finJoin c.comps c.cone c.atoms
    let rejected := !(wf J)
    IO.println s!"A′ {cv rejected}  {c.name}"
    if !rejected then ok := false
  return ok

/-! ## Section B — preservation inside a component -/

def preservationHits (J : FinCM) (c : Cell) : List String :=
  c.comps.zipIdx.flatMap fun p =>
    (List.range p.1.n).flatMap fun u =>
      corpus.filterMap fun nf =>
        if J.forceB (offAt c.comps p.2 + u) nf.2 == p.1.forceB u nf.2 then none
        else some s!"comp {p.2} world {u} formula {nf.1}"

def sectionB : IO Bool := do
  let mut ok := true
  let mut checked := 0
  for c in cells do
    let J := finJoin c.comps c.cone c.atoms
    let hits := preservationHits J c
    checked := checked + (c.comps.map (·.n)).sum * corpus.length
    if hits.isEmpty then
      IO.println s!"B pass  {c.name}"
    else
      ok := false
      IO.println s!"B FAIL  {c.name}: {hits.length} mismatches"
      for h in hits.take 3 do IO.println s!"     certificate: {h}"
  IO.println s!"B cells checked: {checked} (component-world × formula)"
  IO.println ""
  IO.println "B′ CONTROL — a cross-linked join must BREAK preservation:"
  let mut breaks := 0
  let mut live := 0
  for c in cells do
    if c.comps.length ≥ 2 then
      let X := finJoinCross c.comps c.cone c.atoms
      if wf X then
        live := live + 1
        let hits := preservationHits X c
        if hits.isEmpty then
          IO.println s!"B′ no break  {c.name} (cross-link changes nothing here)"
        else
          breaks := breaks + 1
          IO.println s!"B′ pass (broken, {hits.length} mismatches)  {c.name}: {hits.head!}"
      else
        IO.println s!"B′ skip (cross-link not a well-formed frame)  {c.name}"
  IO.println s!"B′ well-formed cross-links: {live}; of these, breaking preservation: {breaks}"
  if breaks == 0 then
    IO.println "B′ FAIL — no cross-link broke preservation; the check has no teeth"
    ok := false
  return ok

/-! ## Section C — the exact ◯ rule at the root -/

/-- The right-hand side of the candidate iff for `root ⊩ ◯A`. -/
def boxRootRHS (J : FinCM) (c : Cell) (A : F) : Bool :=
  let rootPart :=
    J.forceB 0 A ||
      c.cone.any fun e =>
        match c.comps[e.1]? with
        | some M => M.forceB e.2 A
        | none => false
  let conePart :=
    c.comps.all fun M =>
      (List.range M.n).all fun a =>
        (List.range M.n).any fun u => M.rmB a u && M.forceB u A
  rootPart && conePart

/-- CONTROL C′: the INCOMPLETE version — the `boxHolds` defect the
audit found (root can witness `◯A` only through a proper successor). -/
def boxRootRHSbad (J : FinCM) (c : Cell) (A : F) : Bool :=
  let rootPart :=
    c.cone.any fun e =>
      match c.comps[e.1]? with
      | some M => M.forceB e.2 A
      | none => false
  let conePart :=
    c.comps.all fun M =>
      (List.range M.n).all fun a =>
        (List.range M.n).any fun u => M.rmB a u && M.forceB u A
  rootPart && conePart

def sectionC : IO Bool := do
  let mut ok := true
  let mut cellsRun := 0
  for c in cells do
    let J := finJoin c.comps c.cone c.atoms
    let hits := corpus.filterMap fun nf =>
      if J.forceB 0 (.somehow nf.2) == boxRootRHS J c nf.2 then none
      else some nf.1
    cellsRun := cellsRun + corpus.length
    if hits.isEmpty then IO.println s!"C pass  {c.name}"
    else
      ok := false
      IO.println s!"C FAIL  {c.name}: {hits.length} mismatches, e.g. ◯{hits.head!}"
  IO.println s!"C cells checked: {cellsRun}"
  IO.println ""
  IO.println "C′ CONTROL — the INCOMPLETE rule must be refuted here:"
  let mut wit := 0
  for c in cells do
    let J := finJoin c.comps c.cone c.atoms
    let hits := corpus.filterMap fun nf =>
      if J.forceB 0 (.somehow nf.2) == boxRootRHSbad J c nf.2 then none
      else some nf.1
    if !hits.isEmpty then
      wit := wit + 1
      IO.println s!"C′ pass (defect exposed)  {c.name}: ◯{hits.head!}"
  if wit == 0 then
    IO.println "C′ FAIL — the incomplete rule was never exposed; the test has no teeth"
    ok := false
  else IO.println s!"C′ cells exposing the defect: {wit}/{cells.length}"
  return ok

/-! ## Section D — confluence -/

/-- The candidate side condition: every proper `Rm`-successor of the
root DOMINATES every world — `∀ s ∈ cone, ∀ t, ∃ u. s Rᵢ u ∧ t Rₘ u`. -/
def dominates (J : FinCM) : Bool :=
  let ws := List.range J.n
  ws.all fun s =>
    !(J.rmB 0 s && s != 0) ||
      ws.all fun t => ws.any fun u => J.riB s u && J.rmB t u

def sectionD : IO Bool := do
  let mut ok := true
  for c in cells do
    let J := finJoin c.comps c.cone c.atoms
    let lhs := confl J
    let rhs := c.comps.all confl && dominates J
    let agree := lhs == rhs
    if !agree then ok := false
    IO.println s!"D {vd agree}  {c.name}: confl={lhs} (components={c.comps.all confl}, dominates={dominates J})"
  IO.println ""
  IO.println "D corollary — BRANCHING (≥2 inhabited components) with a NON-EMPTY cone:"
  let mut br := 0
  for c in cells do
    if c.comps.length ≥ 2 && c.comps.all (·.n > 0) && !c.cone.isEmpty then
      let J := finJoin c.comps c.cone c.atoms
      br := br + 1
      if confl J then
        IO.println s!"D FAIL  {c.name}: confluent with a non-empty cone (corollary false)"
        ok := false
      else IO.println s!"D pass  {c.name}: NOT confluent, as the corollary predicts"
  IO.println s!"D branching cells tested: {br}"
  return ok

/-! ## Section E — degeneracy to `addRoot` on one component -/

/-- `addRoot` as FinCM data: exactly `finJoin [M]`, written out
independently so the degeneracy claim is not true by definition. -/
def finAddRoot (M : FinCM) (cone : List Nat) (atoms : List String) : FinCM :=
  { n := M.n + 1
    ri := ((List.range M.n).map fun w => (0, w + 1)) ++ M.ri.map fun e => (e.1 + 1, e.2 + 1)
    rm := (cone.map fun u => (0, u + 1)) ++ M.rm.map fun e => (e.1 + 1, e.2 + 1)
    fall := M.fall.map (· + 1)
    val := atoms.map (fun a => (0, a)) ++ M.val.map fun e => (e.1 + 1, e.2) }

def sectionE : IO Bool := do
  let mut ok := true
  for c in cells do
    if h : c.comps.length = 1 then
      let M := c.comps[0]'(by omega)
      let J := finJoin c.comps c.cone c.atoms
      let R := finAddRoot M (c.cone.map (·.2)) c.atoms
      let hits := (List.range J.n).flatMap fun w =>
        corpus.filterMap fun nf =>
          if J.forceB w nf.2 == R.forceB w nf.2 then none else some s!"w{w} {nf.1}"
      if hits.isEmpty then IO.println s!"E pass (degenerates to addRoot)  {c.name}"
      else
        ok := false
        IO.println s!"E FAIL  {c.name}: {hits.length} mismatches, e.g. {hits.head!}"
  return ok

/-! ## Section F — soundness, adversarially -/

def derivableCorpus : List (String × List F × F) :=
  [ ("G4iLL blocker",
     [.somehow (.ifThen (.ifThen (.somehow pv) rv) (.somehow pv)), .ifThen (.somehow pv) rv], rv),
    ("laxIntro", [pv], .somehow pv),
    ("◯◯p ⊢ ◯p", [.somehow (.somehow pv)], .somehow pv),
    ("◯p, p⊃q ⊢ ◯q", [.somehow pv, .ifThen pv qv], .somehow qv),
    ("⊢ ◯(p∧q) ⊃ (◯p∧◯q)", [],
      .ifThen (.somehow (.and pv qv)) (.and (.somehow pv) (.somehow qv))),
    ("⊢ ¬◯⊥ ⊃ ¬◯⊥", [], .ifThen nOBot nOBot),
    ("◯⊥ ⊢ ◯⊥ ", [oBot], oBot) ]

def provedPLL (b : Nat) (Γ : List F) (φ : F) : Bool :=
  match Search.decide { findBudget := some b, emitClosureCap := 0 } Γ φ with
  | .proved _ => true
  | _ => false

def sectionF : IO Bool := do
  let mut ok := true
  IO.println "F derivability of the adversarial corpus (certified in this run):"
  let mut live : List (String × List F × F) := []
  for d in derivableCorpus do
    let p := provedPLL 20000 d.2.1 d.2.2
    IO.println s!"F   {dv p}  {d.1}"
    if p then live := live ++ [d]
  IO.println s!"F live adversarial cells: {live.length}/{derivableCorpus.length}"
  for c in cells do
    let J := finJoin c.comps c.cone c.atoms
    let bad := live.filterMap fun d =>
      if (d.2.1.all fun γ => J.forceB 0 γ) && !(J.forceB 0 d.2.2) then some d.1 else none
    if bad.isEmpty then IO.println s!"F pass  {c.name}"
    else
      ok := false
      IO.println s!"F FAIL (UNSOUND)  {c.name}: {bad}"
  IO.println ""
  IO.println "F′ CONTROL — the joins must actually REFUTE the branching targets:"
  let targets : List (String × F) :=
    [("¬◯⊥∨◯⊥ (catalogue ρ4)", q4),
     ("(p⊃q)∨(q⊃p)", .or (.ifThen pv qv) (.ifThen qv pv))]
  for t in targets do
    let mut refuters := 0
    for c in cells do
      let J := finJoin c.comps c.cone c.atoms
      if !(J.forceB 0 t.2) then
        refuters := refuters + 1
        IO.println s!"F′ pass  {c.name} refutes {t.1} at the root; confluent={confl J}"
    if refuters == 0 then
      IO.println s!"F′ FAIL — no cell refutes {t.1}; the pipeline is not firing"
      ok := false
    else IO.println s!"F′ {t.1}: refuting cells {refuters}/{cells.length}"
  return ok

/-! ## Section G — which targets GENUINELY need branching

A refutation "needs branching" when no LINEAR frame refutes the
formula anywhere.  The chain battery is exhaustive on `Rm`-subsets,
fallible up-sets and (for the p-carrying controls) atom up-sets, so a
formula refuted on no chain up to the size run is a needs-branching
candidate at that size — evidence, not proof, and reported as such.
Positive control: `(p⊃q)∨(q⊃p)` must come out NEEDS-BRANCHING.
Negative control: `◯p` and `¬◯⊥∨◯⊥` must come out CHAIN-REFUTABLE. -/

def upSets (n : Nat) : List (List Nat) :=
  (List.range (n + 1)).map fun k => (List.range n).filter (fun w => w ≥ n - k)

def subsetsOfPairs (l : List (Nat × Nat)) : List (List (Nat × Nat)) :=
  (List.range (2 ^ l.length)).map fun code =>
    (l.zipIdx.filter fun p => (code / 2 ^ p.2) % 2 = 1).map (·.1)

/-- Every chain on `n` worlds: `Ri` is `≤`, `Rm` any well-formed
subrelation, `fall` any up-set, `val` any pair of up-sets for p,q. -/
def chains (n : Nat) (withAtoms : Bool) : List FinCM :=
  let riPairs := (List.range n).flatMap fun i =>
    (List.range n).filter (fun j => j > i) |>.map fun j => (i, j)
  let vals : List (List (Nat × String)) :=
    if withAtoms then
      (upSets n).flatMap fun up =>
        (upSets n).map fun uq =>
          up.map (fun w => (w, "p")) ++ uq.map (fun w => (w, "q"))
    else [[]]
  (subsetsOfPairs riPairs).flatMap fun rm =>
    (upSets n).flatMap fun fal =>
      vals.map fun v => (⟨n, riPairs, rm, fal, v⟩ : FinCM)

def chainBattery (maxN : Nat) (withAtoms : Bool) : List FinCM :=
  ((List.range maxN).flatMap fun k => chains (k + 1) withAtoms).filter wf

def refutedOnChain (bat : List FinCM) (φ : F) : Option (Nat × Nat) :=
  let rec go (i : Nat) : List FinCM → Option (Nat × Nat)
    | [] => none
    | M :: ms =>
        match (List.range M.n).find? (fun w => !(M.forceB w φ)) with
        | some w => some (i, w)
        | none => go (i + 1) ms
  go 0 bat

/-- Refuted at the root of one of the BRANCHING cells (≥2 inhabited
components — a root with incomparable `Ri`-successors)? -/
def refutedByBranchingJoin (φ : F) : Option String :=
  (cells.filter fun c => c.comps.length ≥ 2 && c.comps.all (·.n > 0)).findSome? fun c =>
    let J := finJoin c.comps c.cone c.atoms
    if !(J.forceB 0 φ) then some c.name else none

def sectionG : IO Bool := do
  let mut ok := true
  let closedBat := chainBattery 5 false
  let atomBat := chainBattery 4 true
  IO.println s!"G chain battery: {closedBat.length} closed chains (≤5 worlds), {atomBat.length} p,q-chains (≤4 worlds)"
  let mut needs : List String := []
  for nf in corpus do
    let bat := if nf.1 == "p" || nf.1.length > 0 then atomBat else atomBat
    let chainHit := refutedOnChain (closedBat ++ bat) nf.2
    let brHit := refutedByBranchingJoin nf.2
    match chainHit, brHit with
    | none, some cn =>
        needs := needs ++ [nf.1]
        IO.println s!"G NEEDS-BRANCHING  {nf.1}: no chain refutes it; refuted at the root of {cn}"
    | none, none => IO.println s!"G unrefuted     {nf.1}: no chain and no branching join refutes it"
    | some _, _ => pure ()
  IO.println s!"G chain-refutable (silent): {corpus.length - needs.length} of {corpus.length}"
  IO.println "G CONTROLS:"
  let gd : F := .or (.ifThen pv qv) (.ifThen qv pv)
  let gdOk := (refutedOnChain (closedBat ++ atomBat) gd).isNone && (refutedByBranchingJoin gd).isSome
  IO.println s!"G   positive control (p⊃q)∨(q⊃p) NEEDS-BRANCHING: {vd gdOk}"
  if !gdOk then ok := false
  let negOk := (refutedOnChain (closedBat ++ atomBat) (.somehow pv)).isSome
                && (refutedOnChain (closedBat ++ atomBat) q4).isSome
  IO.println s!"G   negative control ◯p and ¬◯⊥∨◯⊥ CHAIN-refutable: {vd negOk}"
  if !negOk then ok := false
  return ok

/-! ## Section H — the normalisation pipeline -/

def sectionH : IO Unit := do
  let fuel := 12
  let raw := corpus.map (·.2)
  let nrm := raw.map (Rewrite.simplifyWith Rewrite.fullSetC fuel)
  let distinct (l : List F) : Nat := (l.foldl (fun acc φ =>
    if acc.contains φ then acc else φ :: acc) []).length
  let crankSum (l : List F) : Nat := (l.map PLLND.SemUI.crank).sum
  let changed := (raw.zip nrm).filter (fun p => p.1 != p.2)
  IO.println s!"H corpus cells: {raw.length}"
  IO.println s!"H rewritten: {changed.length}/{raw.length} ({(100 * changed.length) / raw.length}%)"
  IO.println s!"H distinct forms: {distinct raw} → {distinct nrm}"
  let cut := if crankSum raw == 0 then 0 else (100 * (crankSum raw - crankSum nrm)) / crankSum raw
  IO.println s!"H crank total: {crankSum raw} → {crankSum nrm} (cut {cut}%)"
  -- CONTROL on the low shrink rate: the pipeline must fire on cells it
  -- provably should.  The catalogue representatives are already the
  -- dictionary's canonical forms, so a low rate here is the corpus,
  -- not a broken normaliser.
  let scrambled : List F :=
    corpus.map (fun nf => .and top (.or nf.2 nf.2)) ++ corpus.map (fun nf => .somehow (.somehow nf.2))
  let sn := scrambled.map (Rewrite.simplifyWith Rewrite.fullSetC fuel)
  let sch := (scrambled.zip sn).filter (fun p => p.1 != p.2)
  IO.println s!"H CONTROL (scrambled corpus ⊤∧(φ∨φ), ◯◯φ): rewritten {sch.length}/{scrambled.length} ({(100 * sch.length) / scrambled.length}%)"
  IO.println s!"H CONTROL distinct forms: {distinct scrambled} → {distinct sn}"
  let scut := if crankSum scrambled == 0 then 0 else (100 * (crankSum scrambled - crankSum sn)) / crankSum scrambled
  IO.println s!"H CONTROL crank: {crankSum scrambled} → {crankSum sn} (cut {scut}%)"
  if sch.length * 2 < scrambled.length then
    IO.println "H CONTROL FAIL — the normaliser is not firing even on scrambled cells"

/-! ## Driver -/

def main : IO Unit := do
  IO.println "JOIN SCREEN — the multi-premise root constructor"
  IO.println s!"cells: {cells.length}   corpus: {corpus.length} formulas"
  IO.println ""
  IO.println "== A  constructor laws =="
  let a ← sectionA
  (← IO.getStdout).flush
  IO.println ""
  IO.println "== B  preservation inside a component =="
  let b ← sectionB
  (← IO.getStdout).flush
  IO.println ""
  IO.println "== C  the exact ◯ rule at the root =="
  let c ← sectionC
  (← IO.getStdout).flush
  IO.println ""
  IO.println "== D  confluence =="
  let d ← sectionD
  (← IO.getStdout).flush
  IO.println ""
  IO.println "== E  degeneracy to addRoot =="
  let e ← sectionE
  (← IO.getStdout).flush
  IO.println ""
  IO.println "== F  soundness, adversarially =="
  let f ← sectionF
  (← IO.getStdout).flush
  IO.println ""
  IO.println "== G  which targets need branching =="
  let g ← sectionG
  (← IO.getStdout).flush
  IO.println ""
  IO.println "== H  normalisation =="
  sectionH
  IO.println ""
  IO.println s!"VERDICT A={a} B={b} C={c} D={d} E={e} F={f} G={g}"
  IO.println "JOIN-SCREEN-DONE"

end JoinScreen

def main : IO Unit := JoinScreen.main
