/-
THE T2 SCREEN — the height measure, and an extensional test of
COMPLETENESS itself, run before the proofs of `Reject/Height.lean`
and `Reject/Complete.lean` were scoped.

T2's claim: every underivability has a construction.  The constructions
are `solo` and `join`, which generate exactly the finite `Rᵢ`-TREES
(fallible worlds only at leaves).  So the claim is testable directly:

    is every formula refutable on SOME finite model
    also refutable AT THE ROOT of some finite TREE?

Sections:

  A  the height measure decreases along a strict `Rᵢ`-ascent, on
     REDUCED models
     control A′: on a NON-reduced model the decrease must FAIL —
     otherwise the reducedness hypothesis is decorative
  B  the same along `Rₘ` (via `Rm ⊆ Ri`)
  C  reduced-class completeness: does the REDUCED battery refute
     everything the full battery refutes?
  D  tree-class completeness — T2 ITSELF, extensionally: does the
     TREE battery refute, AT ITS ROOT, everything the full battery
     refutes anywhere?
     control D′: the tree battery must be strictly weaker than "all
     models at any world" for at least one shape, or the test is
     vacuous
  E  the bisimulation obstruction: a certified 3-world model whose
     two `Rᵢ`-equivalent worlds have different `Rₘ`-cones, and two
     worlds that force different formulas — the certificate that
     BISIMILARITY to a tree can fail while force-equivalence need not
-/
import LaxLogic.PLLCountermodelEmit
import LaxLogic.PLLSearchConf

open PLLND PLLND.FinCM

namespace T2Screen

abbrev F := PLLFormula

def vd (b : Bool) : String := if b then "pass" else "FAIL"

/-! ## Frames -/

def wf (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all (fun x => ws.all fun y => ws.all fun z =>
    (!(M.riB x y && M.riB y z) || M.riB x z) &&
    (!(M.rmB x y && M.rmB y z) || M.rmB x z)) &&
  ws.all (fun x => ws.all fun y =>
    (!(M.rmB x y) || M.riB x y) &&
    (!(M.fallB x && M.riB x y) || M.fallB y)) &&
  M.val.all (fun p => ws.all fun v => !(M.riB p.1 v) || M.valB v p.2)

/-- REDUCED: `Rᵢ` antisymmetric. -/
def reduced (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all fun x => ws.all fun y => !(M.riB x y && M.riB y x) || decide (x = y)

/-- ROOTED at 0: world 0 is `Rᵢ`-below everything. -/
def rooted (M : FinCM) : Bool := (List.range M.n).all fun w => M.riB 0 w

/-- TREE: reduced, rooted, and every world's set of `Rᵢ`-predecessors
is a chain.  This is exactly the class `solo`/`join` generate. -/
def isTree (M : FinCM) : Bool :=
  reduced M && rooted M &&
  (List.range M.n).all fun w =>
    (List.range M.n).all fun x => (List.range M.n).all fun y =>
      !(M.riB x w && M.riB y w) || M.riB x y || M.riB y x

/-- FALLIBLE ONLY AT LEAVES: `join` can never create a fallible world,
so a `Built` model's fallible worlds have no strict `Rᵢ`-successors. -/
def falLeaves (M : FinCM) : Bool :=
  (List.range M.n).all fun w =>
    !(M.fallB w) ||
      (List.range M.n).all fun v => !(M.riB w v) || decide (v = w)

def pairsOf (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun x => (List.range n).map fun y => (x, y)

def subsetOf (l : List (Nat × Nat)) (code : Nat) : List (Nat × Nat) :=
  (l.zipIdx.filter fun p => (code / 2 ^ p.2) % 2 = 1).map (·.1)

/-- All frames on `n` worlds with atom `p` given an up-set valuation. -/
def framesN (n : Nat) (atoms : List String) : List FinCM :=
  let ps := (pairsOf n).filter (fun e => e.1 != e.2)
  let cap := 2 ^ ps.length
  let valsFor (a : String) : List (List (Nat × String)) :=
    (List.range (2 ^ n)).map fun c =>
      ((List.range n).filter fun w => (c / 2 ^ w) % 2 = 1).map fun w => (w, a)
  let vals : List (List (Nat × String)) :=
    atoms.foldl (fun acc a =>
      acc.flatMap fun v => (valsFor a).map fun v' => v ++ v') [[]]
  (List.range cap).flatMap fun ci =>
    (List.range cap).flatMap fun cm =>
      (List.range (2 ^ n)).flatMap fun cf =>
        vals.map fun v =>
          (⟨n, subsetOf ps ci, subsetOf ps cm,
            (List.range n).filter fun x => (cf / 2 ^ x) % 2 = 1, v⟩ : FinCM)

def battery (maxN : Nat) (atoms : List String) : List FinCM :=
  ((List.range maxN).flatMap fun k => framesN (k + 1) atoms).filter wf

/-! ## The corpus -/

def bot : F := .falsePLL
def top : F := .ifThen bot bot
def oBot : F := .somehow bot
def nOBot : F := .ifThen oBot bot
def nnOBot : F := .ifThen nOBot bot
def pv : F := .prop "p"
def qv : F := .prop "q"

def corpus : List (String × F) :=
  [("⊥", bot), ("⊤", top), ("◯⊥", oBot), ("¬◯⊥", nOBot),
   ("¬◯⊥∨◯⊥", .or nOBot oBot), ("¬¬◯⊥", nnOBot),
   ("¬¬◯⊥∨¬◯⊥", .or nnOBot nOBot), ("◯¬◯⊥", .somehow nOBot),
   ("¬¬◯⊥⊃◯⊥", .ifThen nnOBot oBot),
   ("p", pv), ("◯p", .somehow pv), ("p∨¬p", .or pv (.ifThen pv bot)),
   ("¬¬p⊃p", .ifThen (.ifThen (.ifThen pv bot) bot) pv),
   ("◯p⊃p", .ifThen (.somehow pv) pv),
   ("p⊃◯p", .ifThen pv (.somehow pv)),
   ("◯◯p⊃◯p", .ifThen (.somehow (.somehow pv)) (.somehow pv)),
   ("p∨q", .or pv qv), ("(p⊃q)∨(q⊃p)", .or (.ifThen pv qv) (.ifThen qv pv)),
   ("◯(p∨q)⊃(◯p∨◯q)", .ifThen (.somehow (.or pv qv))
      (.or (.somehow pv) (.somehow qv))),
   ("◯(p∧q)⊃(◯p∧◯q)", .ifThen (.somehow (.and pv qv))
      (.and (.somehow pv) (.somehow qv))),
   ("¬◯⊥∨¬¬◯⊥", .or nOBot nnOBot),
   ("◯p∨¬◯p", .or (.somehow pv) (.ifThen (.somehow pv) bot))]

/-! ## A/B — the height measure -/

/-- The measure: the number of worlds STRICTLY above `w`. -/
def heightF (M : FinCM) (w : Nat) : Nat :=
  ((List.range M.n).filter fun z => M.riB w z && !(decide (z = w))).length

/-- Does the measure strictly decrease along every strict `Rᵢ`-step? -/
def decreasesRi (M : FinCM) : Bool :=
  (List.range M.n).all fun x => (List.range M.n).all fun y =>
    !(M.riB x y && !(decide (x = y))) || decide (heightF M y < heightF M x)

def decreasesRm (M : FinCM) : Bool :=
  (List.range M.n).all fun x => (List.range M.n).all fun y =>
    !(M.rmB x y && !(decide (x = y))) || decide (heightF M y < heightF M x)

def sectionAB (bat : List FinCM) : IO Bool := do
  let red := bat.filter reduced
  let nonred := bat.filter (fun M => !(reduced M))
  let badRi := red.filter (fun M => !(decreasesRi M))
  let badRm := red.filter (fun M => !(decreasesRm M))
  IO.println s!"A reduced models: {red.length}; strict-Ri decrease fails on {badRi.length}"
  IO.println s!"B reduced models: {red.length}; strict-Rm decrease fails on {badRm.length}"
  let ok := badRi.isEmpty && badRm.isEmpty
  IO.println s!"A/B {vd ok}"
  -- control: reducedness must be doing work
  let breaks := nonred.filter (fun M => !(decreasesRi M))
  IO.println s!"A′ CONTROL non-reduced models: {nonred.length}; decrease FAILS on {breaks.length}"
  match breaks.head? with
  | some M => IO.println s!"A′ certificate: {repr M}"
  | none => pure ()
  let ctrl := !breaks.isEmpty
  IO.println s!"A′ {vd ctrl} (reducedness is load-bearing, not decorative)"
  return ok && ctrl

/-! ## C/D — completeness of the reduced and tree classes -/

def refutedSomewhere (bat : List FinCM) (φ : F) : Bool :=
  bat.any fun M => (List.range M.n).any fun w => !(M.forceB w φ)

def refutedAtRoot (bat : List FinCM) (φ : F) : Bool :=
  bat.any fun M => !(M.forceB 0 φ)

def sectionCD (bat : List FinCM) : IO Bool := do
  let red := bat.filter reduced
  let trees := bat.filter (fun M => isTree M && falLeaves M)
  IO.println s!"C/D battery {bat.length} | reduced {red.length} | trees(fal-leaves) {trees.length}"
  let mut ok := true
  let mut gapC := 0
  let mut gapD := 0
  for nf in corpus do
    let full := refutedSomewhere bat nf.2
    let redR := refutedSomewhere red nf.2
    let treeR := refutedAtRoot trees nf.2
    if full && !redR then
      gapC := gapC + 1
      IO.println s!"C GAP  {nf.1}: refuted in the full battery, NOT in the reduced one"
    if full && !treeR then
      gapD := gapD + 1
      IO.println s!"D GAP  {nf.1}: refuted somewhere, NOT at the root of any tree"
  IO.println s!"C reduced-class completeness: {gapC} gaps in {corpus.length} cells — {vd (gapC == 0)}"
  IO.println s!"D TREE-class completeness (T2 itself): {gapD} gaps in {corpus.length} cells — {vd (gapD == 0)}"
  if gapC != 0 || gapD != 0 then ok := false
  -- D′ non-vacuity: the tree battery must not refute everything
  let unref := corpus.filter fun nf => !(refutedAtRoot trees nf.2)
  IO.println s!"D′ CONTROL formulas NOT refuted at any tree root: {unref.length} \
(must be > 0, else the test is vacuous): {unref.map (·.1)}"
  if unref.isEmpty then ok := false
  return ok

/-! ## F — the PCLL question: are CONFLUENT trees enough?

Matthew's objection, screened.  Decision (a) keeps the constructed
models CONFLUENT, which buys a PCLL conclusion
(`Reject.not_derivU_of_root`).  But `join_cone_empty_of_confluent_branching`
says a confluent BRANCHING join has an EMPTY modal cone — so in a
confluent tree, `◯A ⊃ A` holds at every branching node, while in a
general confluent model a branching world can force `◯A` without `A`
(its `Rₘ`-witness needs common upper bounds with both branches, which
a tree cannot provide).  So the confluent trees may be a strictly
weaker refuting class than the confluent models.  This section
measures the gap. -/

def confl (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all fun x => ws.all fun w => ws.all fun v =>
    !(M.rmB x w && M.riB x v) || ws.any fun u => M.riB w u && M.rmB v u

/-- A branching world forcing `◯A` without `A` — impossible in a
confluent tree, possible in a confluent model. -/
def branchingBoxWitness (M : FinCM) (A : F) : Option Nat :=
  (List.range M.n).find? fun w =>
    M.forceB w (.somehow A) && !(M.forceB w A) &&
    ((List.range M.n).any fun v1 => (List.range M.n).any fun v2 =>
      M.riB w v1 && M.riB w v2 && !(M.riB v1 v2) && !(M.riB v2 v1))

def sectionF (bat : List FinCM) : IO Bool := do
  let cbat := bat.filter confl
  let ctrees := bat.filter (fun M => confl M && isTree M && falLeaves M)
  IO.println s!"F confluent models {cbat.length} | confluent trees {ctrees.length}"
  let mut gaps : List String := []
  for nf in corpus do
    let full := refutedSomewhere cbat nf.2
    let treeR := refutedAtRoot ctrees nf.2
    if full && !treeR then
      gaps := gaps ++ [nf.1]
      IO.println s!"F GAP  {nf.1}: refuted in a confluent model, NOT at any confluent tree root"
  IO.println s!"F confluent-tree completeness (PCLL): {gaps.length} gaps in {corpus.length} cells"
  -- the structural fact behind any gap, exhibited directly
  let mut wits := 0
  for M in cbat do
    if (branchingBoxWitness M pv).isSome && isTree M then wits := wits + 1
  IO.println s!"F confluent TREES with a branching world forcing ◯p but not p: {wits} (theory says 0)"
  let mut wits2 : List String := []
  for M in cbat do
    if !(isTree M) then
      match branchingBoxWitness M pv with
      | some w => if wits2.length < 3 then
                    wits2 := wits2 ++ [s!"world {w} of {repr M}"]
      | none => pure ()
  IO.println s!"F confluent NON-trees with such a world: {wits2.length} shown"
  for x in wits2 do IO.println s!"F   witness: {x}"
  -- The ≤3-world battery is too small for the decisive shape.  Here it
  -- is by hand: a 4-world confluent TREE whose ROOT has a NON-EMPTY
  -- modal cone and two incomparable Rᵢ-successors higher up.  So the
  -- side condition bites only at IMMEDIATE branching — which is what
  -- confluence itself forbids — not at branching in general.
  let deepCone : FinCM :=
    ⟨4, [(0,1),(1,2),(1,3),(0,2),(0,3)], [(0,1)], [], [(1,"p"),(2,"p"),(3,"p")]⟩
  let dOk := wf deepCone && confl deepCone && isTree deepCone
  let dBox := deepCone.forceB 0 (.somehow pv) && !(deepCone.forceB 0 pv)
  let dBranch := !(deepCone.riB 2 3) && !(deepCone.riB 3 2)
  let dCone := (List.range 4).filter (fun u => deepCone.rmB 0 u && u != 0)
  IO.println s!"F CERTIFICATE deepCone: wf&confluent&tree = {dOk}"
  IO.println s!"F   root cone (proper Rₘ-successors) = {dCone} (NON-empty)"
  IO.println s!"F   root ⊩ ◯p ∧ root ⊮ p = {dBox};  worlds 2,3 incomparable above the root = {dBranch}"
  IO.println s!"F   ⇒ a confluent tree CAN have a non-trivial modal cone at a branching root;"
  IO.println s!"F     the empty-cone theorem constrains IMMEDIATE branching only."
  return gaps.isEmpty && dOk && dBox && dBranch

/-! ## E — the bisimulation obstruction, as data -/

/-- Two `Rᵢ`-equivalent worlds (0,1) with DIFFERENT `Rₘ`-cones, and a
third world 2 above both.  `p` holds only at 2. -/
def obstruction : FinCM := ⟨3, [(0,1),(1,0),(0,2),(1,2)], [(0,2)], [], [(2,"p")]⟩

def sectionE : IO Bool := do
  let M := obstruction
  let wfM := wf M
  let redM := reduced M
  let a0 := M.forceB 0 (.somehow pv)
  let a2 := M.forceB 2 (.somehow pv)
  IO.println s!"E model well-formed: {wfM}; reduced: {redM} (must be false)"
  IO.println s!"E worlds 0,1 are Rᵢ-equivalent: {M.riB 0 1 && M.riB 1 0}"
  IO.println s!"E Rₘ-cones differ: cone(0)={(List.range 3).filter (M.rmB 0 ·)}, cone(1)={(List.range 3).filter (M.rmB 1 ·)}"
  IO.println s!"E 0 ⊩ ◯p = {a0};  2 ⊩ ◯p = {a2}  (differ ⇒ 0 and 2 are NOT bisimilar)"
  IO.println s!"E 0 and 1 force the same corpus formulas: {corpus.all fun nf => M.forceB 0 nf.2 == M.forceB 1 nf.2}"
  let ok := wfM && !redM && (a0 != a2)
  IO.println s!"E {vd ok}"
  return ok

/-! ## G — EXTRACTION COST: what the completeness proof actually builds

`genJoin` indexes the components at `w` by EVERY strictly greater
world.  So the extracted model satisfies

    |T(w)| = 1 + Σ_{v > w} |T(v)|

which on a CHAIN of `n` worlds is `2^(n-1)`: the procedure re-expands
every world once per path that reaches it.  The obvious repair is to
index by the IMMEDIATE successors (covers) instead — every world above
`w` is still reached, inside the component of some cover — giving

    |T'(w)| = 1 + Σ_{v ⋖ w} |T'(v)|

which is exactly `n` on a chain.  This section measures both. -/

/-- Cost of the extracted model, as the proof builds it. -/
def treeSizeAll (M : FinCM) (fuel : Nat) (w : Nat) : Nat :=
  match fuel with
  | 0 => 1
  | fuel + 1 =>
      if M.fallB w then 1
      else 1 + (((List.range M.n).filter fun v => M.riB w v && v != w).map
                  (treeSizeAll M fuel)).sum

/-- `v` covers `w`: strictly above, with nothing strictly between. -/
def covers (M : FinCM) (w v : Nat) : Bool :=
  M.riB w v && v != w &&
    !((List.range M.n).any fun z => M.riB w z && z != w && M.riB z v && z != v)

/-- Cost of the repaired extraction, indexing by covers. -/
def treeSizeCov (M : FinCM) (fuel : Nat) (w : Nat) : Nat :=
  match fuel with
  | 0 => 1
  | fuel + 1 =>
      if M.fallB w then 1
      else 1 + (((List.range M.n).filter (covers M w)).map
                  (treeSizeCov M fuel)).sum

def chainOf (n : Nat) : FinCM :=
  ⟨n, (List.range n).flatMap fun i => (List.range n).filter (fun j => j > i) |>.map fun j => (i, j),
   [], [], []⟩

def sectionG (bat : List FinCM) : IO Unit := do
  IO.println "G extraction cost on CHAINS (the worst case for the proof as written):"
  for n in [1, 2, 3, 4, 5, 6, 8, 10] do
    let C := chainOf n
    IO.println s!"G   chain n={n}: proof-as-written {treeSizeAll C (n+1) 0}, by covers {treeSizeCov C (n+1) 0}"
  let red := bat.filter reduced
  let costs := red.map fun M => (treeSizeAll M (M.n + 1) 0, treeSizeCov M (M.n + 1) 0, M.n)
  let worstAll := costs.foldl (fun a c => max a c.1) 0
  let worstCov := costs.foldl (fun a c => max a c.2.1) 0
  let sumAll := (costs.map (·.1)).sum
  let sumCov := (costs.map (·.2.1)).sum
  IO.println s!"G battery ({red.length} reduced models, ≤3 worlds): worst |T| = {worstAll} (proof), {worstCov} (covers); total {sumAll} vs {sumCov}"
  IO.println s!"G ⇒ the extracted MODEL is exponential; the extracted DERIVATION need not be."

/-! ## Driver -/

def main : IO Unit := do
  IO.println "T2 SCREEN — height measure, and completeness of the tree class"
  let bat1 := battery 3 ["p"]
  IO.println s!"battery (≤3 worlds, atom p): {bat1.length} well-formed frames"
  IO.println ""
  IO.println "== A/B  the height measure =="
  let ab ← sectionAB bat1
  (← IO.getStdout).flush
  IO.println ""
  IO.println "== C/D  reduced- and tree-class completeness =="
  let cd ← sectionCD (battery 3 ["p", "q"])
  (← IO.getStdout).flush
  IO.println ""
  IO.println "== F  are CONFLUENT trees enough (the PCLL question)? =="
  let f ← sectionF (battery 3 ["p", "q"])
  (← IO.getStdout).flush
  IO.println ""
  IO.println "== E  the bisimulation obstruction =="
  let e ← sectionE
  IO.println ""
  IO.println "== G  extraction cost =="
  sectionG bat1
  IO.println ""
  IO.println s!"VERDICT AB={ab} CD={cd} F={f} E={e}"
  IO.println "T2-SCREEN-DONE"

end T2Screen

def main : IO Unit := T2Screen.main
