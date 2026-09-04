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

def saturateNaiveO (cfg : Config) : DBO O × Stats :=
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

/-! ## Semi-naive (differential) evaluation  (`Config.semiNaive`)

`roundStepO` recomputes every rule instance every round: on
`(◯◯p ∧ ◯q) ⊃ ◯(◯p ∧ q)` at `jmax=3 pmax=2` it fires 129 premise
families × 703 promise families = 33 744 join pairs in each of the five
rounds, while rows added per round run 13, 13, 9, 2, 0
(`docs/engine-profile.md`).  An instance all of whose premises were
already in the store LAST round was fired then, and — insertion keeping
the `rsLeO`/`isLeO`-maximal rows, both preorders — its conclusion is
still subsumed now.  So only instances touching a row NEW since the
previous round can add anything.

**Why the fixpoint is the same.**  Write `S k` for the store at the
start of round `k`, `D k` for its delta and `O k` for the rest, and note
`O (k+1) ⊆ S k` (the old half of round `k+1` is round `k`'s whole store,
minus rows filtered out).  Then

    every rule instance over `S k` was fired in some round `≤ k`

by induction: at `k = 1` the store IS the delta (the seeds), so every
instance touches it; and an instance over `S (k+1)` either touches
`D (k+1)`, and is fired in round `k+1`, or lies inside
`O (k+1) ⊆ S k` and was fired by round `k` already.  A conclusion `c`
fired in an earlier round is now rejected either way: `rsLeO`/`isLeO`
are reflexive and TRANSITIVE (list inclusion, `tagLeB`, equality of the
right-hand side), and `insertRO` keeps the ≤-maximal rows, so once
`c ≤ e` holds for some stored `e` it holds forever — if that `e` is
later filtered it is because `e ≤ e'` for an inserted `e'`.  Skipping
the old-only instances therefore loses no row.

**Identifying the new rows.**  `O.RS`/`O.IS` carry no `DecidableEq`, and
`insertRO` prepends the new row while FILTERING subsumed old ones, so a
row's position is not a stable name for it.  The generation is therefore
carried STRUCTURALLY, by splitting the store in two — `DBG` below —
rather than recovered after the fact.  `viewG` is `rsN ++ rsO`, and
`insertRG` is `insertRO` with the same test and the same filter applied
to both halves, so the view of a `DBG` is exactly the `DBO` the naive
loop would hold: the split costs nothing in row order.
-/

/-- The store with its generation split: `rsN`/`isN` are the rows
inserted in the round just finished (the delta), `rsO`/`isO` everything
older.  `viewG` is the `DBO` the naive loop holds at the same point. -/
structure DBG (O : Ops G) where
  rsN : List O.RS
  rsO : List O.RS
  isN : List O.IS
  isO : List O.IS

def viewG (d : DBG O) : DBO O := { rs := d.rsN ++ d.rsO, is := d.isN ++ d.isO }

/-- `insertRO` on `viewG d`: same subsumption test, same filter, the new
row prepended in front of the delta.  `viewG` commutes with it because
`(l ++ m).any p = l.any p || m.any p` and
`(l ++ m).filter p = l.filter p ++ m.filter p`. -/
def insertRG (d : DBG O) (r : O.RS) : DBG O × Bool :=
  if d.rsN.any (fun e => rsLeO O r e) || d.rsO.any (fun e => rsLeO O r e) then (d, false)
  else ({ d with rsN := r :: d.rsN.filter (fun e => !(rsLeO O e r)),
                 rsO := d.rsO.filter (fun e => !(rsLeO O e r)) }, true)

def insertIG (d : DBG O) (i : O.IS) : DBG O × Bool :=
  if d.isN.any (fun e => isLeO O i e) || d.isO.any (fun e => isLeO O i e) then (d, false)
  else ({ d with isN := i :: d.isN.filter (fun e => !(isLeO O e i)),
                 isO := d.isO.filter (fun e => !(isLeO O e i)) }, true)

def insertAllRG (d : DBG O) (l : List O.RS) : DBG O × Nat :=
  l.foldl (fun (acc : DBG O × Nat) r =>
    let (d', new) := insertRG O acc.1 r
    (d', acc.2 + (if new then 1 else 0))) (d, 0)

def insertAllIG (d : DBG O) (l : List O.IS) : DBG O × Nat :=
  l.foldl (fun (acc : DBG O × Nat) i =>
    let (d', new) := insertIG O acc.1 i
    (d', acc.2 + (if new then 1 else 0))) (d, 0)

/-- One differential round.  Every rule instance of `roundStepO` whose
premises all lie in the old generation is skipped; everything else is
fired, in the same shape:

* single-premise rules (`stepR1`, `stepNotIn`, `stepI1`, `stepImpInI`)
  over the delta only;
* the ordered `∨` pair over `new × all` and `old × new`;
* barren and fallible joins over the families meeting the delta
  (`famsDeltaUpTo`);
* the promise cross product over
  `(new-meeting families × all promise families)` together with
  `(old-only families × new-meeting promise families)` — the two
  disjoint halves of "the pair contains a new row".

`lamCapped` is unaffected: `stepImpInI` depends only on the row and the
cap, every stored row is in the delta of exactly one round, and the flag
is accumulated disjunctively across rounds. -/
def roundStepG (cfg : Config) (d : DBG O) : DBG O × Nat × Bool :=
  let rsAll := d.rsN ++ d.rsO
  let isAll := d.isN ++ d.isO
  let newR1 := d.rsN.flatMap O.stepR1
  let newI1 := d.rsN.flatMap O.stepNotIn
  let newI2 := d.isN.flatMap O.stepI1
  let newI3 := d.isN.flatMap (fun i1 => isAll.flatMap (fun i2 => O.stepOrI i1 i2))
    ++ d.isO.flatMap (fun i1 => d.isN.flatMap (fun i2 => O.stepOrI i1 i2))
  let impRes := d.isN.map (O.stepImpInI cfg.lamCap)
  let newI4 := impRes.flatMap (·.1)
  let lamCapped := impRes.any (·.2)
  -- `max · 1`: `famsUpTo` truncates `k - 1`, so it treats `k = 0` as
  -- `k = 1` (all singletons) while `famsDeltaUpTo _ _ 0` is empty.  See
  -- the `#guard`s at `famsDeltaUpTo`.
  let famsD := famsDeltaUpTo d.isN d.isO (max cfg.jmax 1)
  let newJB := famsD.flatMap (fun (a, rest) => O.mkJoinBarren a rest)
  let newJF := famsD.flatMap (fun (a, rest) =>
    if modalContentO O a rest then O.mkJoinF a rest else [])
  let pfamsD := famsDeltaUpTo d.rsN d.rsO (max cfg.pmax 1)
  let newJP :=
    (if famsD.isEmpty then [] else
      let pfamsAll := famsUpTo rsAll cfg.pmax
      famsD.flatMap (fun (a, rest) =>
        if modalContentO O a rest then
          pfamsAll.flatMap (fun (p, prest) => O.mkJoinP a rest p prest)
        else []))
    ++ (if pfamsD.isEmpty then [] else
      (famsUpTo d.isO cfg.jmax).flatMap (fun (a, rest) =>
        if modalContentO O a rest then
          pfamsD.flatMap (fun (p, prest) => O.mkJoinP a rest p prest)
        else []))
  -- the generation rolls over: everything present is now old, and the
  -- rows inserted below are the next round's delta
  let d0 : DBG O := { rsN := [], rsO := rsAll, isN := [], isO := isAll }
  let (d1, n1) := insertAllRG O d0 (newR1 ++ newJB ++ newJF ++ newJP)
  let (d2, n2) := insertAllIG O d1 (newI1 ++ newI2 ++ newI3 ++ newI4)
  (d2, n1 + n2, lamCapped)

/-- `saturateNaiveO` with `roundStepG` in place of `roundStepO`: the
seeds are the first delta, so round 1 fires everything. -/
def saturateSemiO (cfg : Config) : DBO O × Stats :=
  let d0 : DBG O := { rsN := O.seedsR, rsO := [], isN := O.seedsI, isO := [] }
  let rec go : Nat → DBG O → Stats → DBG O × Stats
    | 0, d, st => (d, st)
    | fuel + 1, d, st =>
        let rsLen := d.rsN.length + d.rsO.length
        let isLen := d.isN.length + d.isO.length
        if rsLen > cfg.maxRS || isLen > cfg.maxIS then
          (d, { st with dbCapped := true })
        else
          let (d', fresh, lc) := roundStepG O cfg d
          let st' := { st with
            roundsUsed := st.roundsUsed + 1,
            lamCapped := st.lamCapped || lc,
            jmaxBinding := st.jmaxBinding || decide (isLen > cfg.jmax),
            pmaxBinding := st.pmaxBinding || decide (rsLen > cfg.pmax) }
          if fresh == 0 then (d', st') else go fuel d' st'
  let (d, st) := go cfg.rounds d0 {}
  let db := viewG O d
  (db, { st with rsSize := db.rs.length, isSize := db.is.length })

/-- The saturation the callers use.  `cfg.semiNaive` defaults to `false`,
and on that branch this IS `saturateNaiveO` — the previous definition,
unchanged. -/
def saturateO (cfg : Config) : DBO O × Stats :=
  if cfg.semiNaive then saturateSemiO O cfg else saturateNaiveO O cfg

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
