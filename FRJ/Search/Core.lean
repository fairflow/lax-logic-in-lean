/-
# The saturation engine, with the calculus as an INPUT

`FRJ/Search/Engine.lean` hard-wires the paper calculus: its steps apply
`FRJr`/`FRJi` constructors directly, so a change of calculus meant a new
engine.  This module factors the engine into

* `Ops G` — the calculus operations: the row types (sequents carrying
  their derivations), their zone projections, the seed rows, and one
  step function per rule group; and
* the generic loop — subsumption, insertion, family enumeration and the
  round/saturation drivers — written once over an arbitrary `Ops`.

Two instances exist: the paper calculus (`paperOps`, this file — its
fields are literally the functions of `FRJ/Search/Engine.lean`) and the
repaired RefAt calculus (`vOps`, `FRJ/Search/OpsV.lean`).  The loop is a
transcription of `Engine.lean`'s `roundStep`/`saturate`, so the paper
instance must agree with the legacy engine row for row — checked by the
differential runner, not assumed.
-/
import FRJ.Search.Engine

namespace FRJ.Search

open FRJ Form

/-- The calculus, as the engine consumes it: row types with their zone
projections, seeds, and the rule steps.  A row is a sequent CARRYING its
derivation, so faithfulness lives in the instance, not the loop. -/
structure Ops (G : Form) where
  RS : Type
  IS : Type
  rsTag : RS → Tag
  rsCtx : RS → List Form
  rsRhs : RS → Form
  isStab : IS → List Form
  isTh : IS → List Form
  isRhs : IS → Form
  seedsR : List RS
  seedsI : List IS
  /-- `∧`, `⊃∈`, `◯∈` on one regular row. -/
  stepR1 : RS → List RS
  /-- `∧` (irregular). -/
  stepI1 : IS → List IS
  /-- `∨` (irregular) on an ordered pair. -/
  stepOrI : IS → IS → List IS
  /-- `⊃∈` (irregular); the `Nat` is the `Λ`-width cap, the `Bool`
  reports its truncation. -/
  stepImpInI : Nat → IS → List IS × Bool
  /-- `⊃∉` and `◯∉` from one regular row. -/
  stepNotIn : RS → List IS
  /-- The barren joins on one premise family. -/
  mkJoinBarren : IS → List IS → List RS
  /-- The fallible joins. -/
  mkJoinF : IS → List IS → List RS
  /-- The promise joins, against one promise family. -/
  mkJoinP : IS → List IS → RS → List RS → List RS

variable {G : Form} (O : Ops G)

/-! ## The generic loop (transcribed from `Engine.lean`) -/

def rsLeO (r r' : O.RS) : Bool :=
  decide (O.rsRhs r = O.rsRhs r') && tagLeB (O.rsTag r) (O.rsTag r')
    && subB (O.rsCtx r) (O.rsCtx r')

def isLeO (i i' : O.IS) : Bool :=
  decide (O.isRhs i = O.isRhs i') && subB (O.isStab i) (O.isStab i')
    && subB (O.isStab i') (O.isStab i) && subB (O.isTh i) (O.isTh i')

structure DBO (O : Ops G) where
  rs : List O.RS
  is : List O.IS

def insertRO (db : DBO O) (r : O.RS) : DBO O × Bool :=
  if db.rs.any (fun e => rsLeO O r e) then (db, false)
  else ({ db with rs := r :: db.rs.filter (fun e => !(rsLeO O e r)) }, true)

def insertIO (db : DBO O) (i : O.IS) : DBO O × Bool :=
  if db.is.any (fun e => isLeO O i e) then (db, false)
  else ({ db with is := i :: db.is.filter (fun e => !(isLeO O e i)) }, true)

def insertAllRO (db : DBO O) (l : List O.RS) : DBO O × Nat :=
  l.foldl (fun (acc : DBO O × Nat) r =>
    let (db', new) := insertRO O acc.1 r
    (db', acc.2 + (if new then 1 else 0))) (db, 0)

def insertAllIO (db : DBO O) (l : List O.IS) : DBO O × Nat :=
  l.foldl (fun (acc : DBO O × Nat) i =>
    let (db', new) := insertIO O acc.1 i
    (db', acc.2 + (if new then 1 else 0))) (db, 0)

/-- Does a premise family carry modal content for a `P`/`F` join?  The
same test as `Engine.lean`'s `modalContent`, through the projections. -/
def modalContentO (a : O.IS) (rest : List O.IS) : Bool :=
  !((a :: rest).flatMap (fun i => circPart (O.isStab i))).isEmpty ||
    !((circPart (O.isTh a)).filter (fun x =>
        rest.all (fun i => decide (x ∈ circPart (O.isTh i))))).isEmpty

def roundStepO (cfg : Config) (db : DBO O) : DBO O × Nat × Bool :=
  let newR1 := db.rs.flatMap O.stepR1
  let newI1 := db.rs.flatMap O.stepNotIn
  let newI2 := db.is.flatMap O.stepI1
  let newI3 := db.is.flatMap (fun i1 => db.is.flatMap (fun i2 => O.stepOrI i1 i2))
  let impRes := db.is.map (O.stepImpInI cfg.lamCap)
  let newI4 := impRes.flatMap (·.1)
  let lamCapped := impRes.any (·.2)
  let fams := famsUpTo db.is cfg.jmax
  let newJB := fams.flatMap (fun (a, rest) => O.mkJoinBarren a rest)
  let newJF := fams.flatMap (fun (a, rest) =>
    if modalContentO O a rest then O.mkJoinF a rest else [])
  let pfams := famsUpTo db.rs cfg.pmax
  let newJP := fams.flatMap (fun (a, rest) =>
    if modalContentO O a rest then
      pfams.flatMap (fun (p, prest) => O.mkJoinP a rest p prest)
    else [])
  let (db1, n1) := insertAllRO O db (newR1 ++ newJB ++ newJF ++ newJP)
  let (db2, n2) := insertAllIO O db1 (newI1 ++ newI2 ++ newI3 ++ newI4)
  (db2, n1 + n2, lamCapped)

def saturateO (cfg : Config) : DBO O × Stats :=
  let db0 : DBO O := { rs := O.seedsR, is := O.seedsI }
  let rec go : Nat → DBO O → Stats → DBO O × Stats
    | 0, db, st => (db, st)
    | fuel + 1, db, st =>
        if db.rs.length > cfg.maxRS || db.is.length > cfg.maxIS then
          (db, { st with dbCapped := true })
        else
          let (db', fresh, lc) := roundStepO O cfg db
          let st' := { st with
            roundsUsed := st.roundsUsed + 1,
            lamCapped := st.lamCapped || lc,
            jmaxBinding := st.jmaxBinding || decide (db.is.length > cfg.jmax),
            pmaxBinding := st.pmaxBinding || decide (db.rs.length > cfg.pmax) }
          if fresh == 0 then (db', st') else go fuel db' st'
  let (db, st) := go cfg.rounds db0 {}
  (db, { st with rsSize := db.rs.length, isSize := db.is.length })

def derivableO (db : DBO O) : Bool :=
  db.rs.any (fun r => decide (O.rsRhs r = G))

/-! ## The paper calculus as an instance

The fields are literally `Engine.lean`'s functions.  `modalContentO`
recomputes `Engine.modalContent` through the projections (same zones),
and the loop is a transcription — the differential runner checks the two
engines agree row for row rather than trusting the transcription. -/

def paperOps (G : Form) : Ops G where
  RS := RS G
  IS := IS G
  rsTag := (·.t)
  rsCtx := (·.ctx)
  rsRhs := (·.rhs)
  isStab := (·.stab)
  isTh := (·.th)
  isRhs := (·.rhs)
  seedsR := seedsR G
  seedsI := seedsI G ++ seedsIC G
  stepR1 := stepR1 G
  stepI1 := stepI1 G
  stepOrI := stepOrI G
  stepImpInI := fun cap i => stepImpInI G cap i
  stepNotIn := stepNotIn G
  mkJoinBarren := fun a rest => mkJoinBarren a rest
  mkJoinF := fun a rest => mkJoinF a rest
  mkJoinP := fun a rest p prest => mkJoinP a rest p prest

end FRJ.Search
