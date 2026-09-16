/-
# The PROFILE-INDEXED family search

A third saturation engine, alongside `FRJ/Search/Engine.lean` (reference)
and `FRJ/Search/Fast.lean` (clique-based).  Nothing here replaces either:
the frozen oracle `wip/frj_sat.lean` and `Fast` both stay exactly as they
are, so the three can be run against each other.

## What it changes, and what licenses it

`Fast` enumerates every J1-clique of arity `≤ jmax` into a strict list.
Measured 2026-08-21 on bank cell `cAnd_8_11`: 14748 cliques in one round
from a 61-row database, with arity capped at 3, and the cap bound 119 of
119 negative results.

`FRJ/Profile.lean` proves (sorry-free, choice-free) that a join rule's
conclusion and side conditions are a function of four aggregates

    Σ = ⋃ⱼ stab j    Θ = ⋂ⱼ th j    M = ⋂ⱼ (stab j ++ th j)    Υ = { rhs j }

and — `Profile.J1_cons` — that whether a row may JOIN is a function of
`(Σ, M)` alone:

    J1 (b ∷ 𝔉)  ⟺  J1 𝔉  ∧  b.stab ⊆ M(𝔉)  ∧  Σ(𝔉) ⊆ b.stab ++ b.th

So families sharing a profile produce the same row AND admit the same
extensions.  This engine keeps ONE witness family per profile and walks
the profile lattice with a worklist, which is why it needs no arity cap:
each layer adds one member, so `l.length` layers suffice, and the loop
stops early when a layer produces no new profile.

## SCOPE — read this before believing any speedup

The proved lemma covers the IRREGULAR family (`stab`, `th`, `rhs`), so
this eliminates `jmax` and nothing else.  **`pmax` is untouched**: promise
families are `RS G` rows and their side conditions (`hJ5` is an
existential over the family, `htag` forces a common `Ds`) factor through
a DIFFERENT profile — the pair `⋃ᵢ Cl(Δs i)` / `⋂ᵢ Cl(Δs i)` — for which
no lemma is proved yet.  `pfams` is therefore computed exactly as `Fast`
computes it.

Consequently `closed-no-cap-bound` will still not fire on dictionary
cells: `pmax` will still bind.  What this buys is the `fams` factor of the
`fams × pfams` product, which is the larger one (14748 against 406).

## What is NOT claimed

That this engine is correct.  The lemma licenses the METHOD; the
implementation must still agree row-for-row with the frozen oracle on the
corpus before it is used for anything.
-/
import FRJ.Search.Fast
import FRJ.Profile

namespace FRJ.Search

open FRJ.Profile

variable {G : Form}

/-! ## The profile key

Four sets, compared up to set equality.  Deliberately independent of `G`
and of the derivation terms, so the comparison is cheap. -/

structure PKey where
  sig : List Form   -- Σ, grows
  the : List Form   -- Θ, shrinks
  mid : List Form   -- M, shrinks
  ups : List Form   -- Υ, grows

def sameSet (a b : List Form) : Bool := subB a b && subB b a

def PKey.same (p q : PKey) : Bool :=
  sameSet p.sig q.sig && sameSet p.the q.the
    && sameSet p.mid q.mid && sameSet p.ups q.ups

/-- The step of `Profile.mem_unionAll_cons` / `mem_interAll_cons` /
`mem_mAll_cons` / `mem_upsilon_cons`, as computation: Σ and Υ grow, Θ and
M shrink. -/
def PKey.push (p : PKey) (b : IS G) : PKey :=
  { sig := p.sig ++ b.stab,
    the := p.the.filter (fun x => decide (x ∈ b.th)),
    mid := p.mid.filter (fun x => decide (x ∈ b.stab ++ b.th)),
    ups := b.rhs :: p.ups }

/-- `Profile.J1_cons` as a Bool: may `b` join a family with this profile? -/
def PKey.admits (p : PKey) (b : IS G) : Bool :=
  subB b.stab p.mid && subB p.sig (b.stab ++ b.th)

def keyOf (a : IS G) : PKey :=
  { sig := a.stab, the := a.th, mid := a.stab ++ a.th, ups := [a.rhs] }

/-! ## The worklist -/

/-- Each element paired with the suffix that follows it.  Walking suffixes
is what stops one family being built in several orders. -/
def withTails {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: as => (a, as) :: withTails as

/-- A node of the profile DAG: the profile, ONE witness family for it, and
the candidates still available to extend it. -/
structure PNode (G : Form) where
  head : IS G
  rest : List (IS G)
  tail : List (IS G)
  key : PKey

def seedNodes (l : List (IS G)) : List (PNode G) :=
  (withTails l).map (fun p => ⟨p.1, [], p.2, keyOf p.1⟩)

/-- One layer: extend a node by every admissible candidate.  Admissibility
is `PKey.admits`, i.e. `Profile.J1_cons`, checked against the AGGREGATE
rather than against every committed member. -/
def extendNode (n : PNode G) : List (PNode G) :=
  (withTails n.tail).filterMap (fun p =>
    if n.key.admits p.1 then
      some ⟨n.head, n.rest ++ [p.1], p.2, n.key.push p.1⟩
    else none)

/-- Statistics, so a run can never silently look exhaustive. -/
structure PStats where
  profiles : Nat := 0
  families : Nat := 0
  merged : Nat := 0
  layers : Nat := 0
  layerCapped : Bool := false

/-- **The replacement for `famsUpToC compatI l jmax`.**

Returns the same type, so it drops into `roundStepFast` unchanged.  No
arity cap: `maxLayers` defaults to `l.length`, which is the most members
any family can have, and the loop stops as soon as a layer yields no new
profile.  `layerCapped` records whether the layer budget ran out, so a
truncated run is never read as a complete one. -/
def profFamsStats (l : List (IS G)) (maxLayers : Nat) :
    List (IS G × List (IS G)) × PStats :=
  Id.run do
    let s := seedNodes l
    let mut seen : List PKey := s.map (·.key)
    let mut out : List (IS G × List (IS G)) := s.map (fun n => (n.head, n.rest))
    let mut frontier := s
    let mut merged := 0
    let mut used := 0
    let mut capped := true
    for _ in [0:maxLayers] do
      if frontier.isEmpty then
        capped := false
        break
      used := used + 1
      let mut nxt : List (PNode G) := []
      for n in frontier do
        for m in extendNode n do
          if seen.any (fun k => k.same m.key) then
            merged := merged + 1
          else
            seen := m.key :: seen
            nxt := m :: nxt
            out := (m.head, m.rest) :: out
      frontier := nxt
    if frontier.isEmpty then capped := false
    return (out, { profiles := seen.length, families := out.length,
                   merged := merged, layers := used, layerCapped := capped })

def profFams (l : List (IS G)) : List (IS G × List (IS G)) :=
  (profFamsStats l l.length).1

/-- The layer-BUDGETED form, for the differential test.  `famsUpTo l k`
admits families of total size `≤ k`, i.e. a head plus `k-1` more, so
`profFamsN l (k-1)` explores exactly the same arity as `famsUpToC … k`
and any difference in verdict is down to the merging alone. -/
def profFamsN (l : List (IS G)) (k : Nat) : List (IS G × List (IS G)) :=
  (profFamsStats l k).1

/-! ## The PROMISE side — `FRJ/Profile.lean` §8

`Profile.restrictC_congr` / `restrictP_congr` say a promise family enters
the calculus only through two predicates on formulas,

    E(Y) := any i, cloB (Δs i) Y        A(X) := all i, cloB (Δs i) X

and `cupCl_cons` / `capCl_cons` say adding a row grows `E` and shrinks
`A`.  So promise families merge exactly as irregular ones do.

`E` and `A` are PREDICATES, and a key must be finite.  They are only ever
consulted on formulas the conclusion could contain, so materialise them on
two universes computed from the irregular family ALONE (never from `Δ⃗`,
which would be circular):

    U_A := Σ ++ Θ            everything `restrictP` is applied to
    U_E := bodies of circPart U_A      everything `restrictC` and (J5) ask about

Using SUPERSETS here is sound in the safe direction: a larger universe
makes the key FINER, so it can only merge less, never more.

`mkJoinPFam` also builds a `.chain` tag when `hch` holds — all promise
rhs's equal and each tag covering.  That is not a function of `(E, A)`, so
the key carries it, maintained incrementally with `coversB`. -/

/-- The promise profile.  `eSet` and `aSet` are kept as sublists of their
universes in the universe's own order, so equality is list equality. -/
structure QKey where
  eSet : List Form
  aSet : List Form
  headRhs : Form
  chainOk : Bool

def QKey.same (x y : QKey) : Bool :=
  decide (x.eSet = y.eSet) && decide (x.aSet = y.aSet)
    && decide (x.headRhs = y.headRhs) && (x.chainOk == y.chainOk)

/-- The `hch` disjunct of `htag`, for one promise row against the head's
rhs.  `.blocked` cannot participate in a chain. -/
def tagCond (headRhs : Form) (r : RS G) : Bool :=
  decide (r.rhs = headRhs) &&
    (match r.t with
     | .barren => true
     | .chain W => coversB r.ctx W headRhs
     | .blocked => false)

def qKeyOf (uE uA : List Form) (r : RS G) : QKey :=
  { eSet := uE.filter (fun Y => cloB r.ctx Y),
    aSet := uA.filter (fun X => cloB r.ctx X),
    headRhs := r.rhs,
    chainOk := tagCond r.rhs r }

/-- `cupCl_cons` and `capCl_cons` as computation: `E` grows, `A` shrinks. -/
def QKey.push (k : QKey) (uE : List Form) (b : RS G) : QKey :=
  { eSet := uE.filter (fun Y => decide (Y ∈ k.eSet) || cloB b.ctx Y),
    aSet := k.aSet.filter (fun X => cloB b.ctx X),
    headRhs := k.headRhs,
    chainOk := k.chainOk && tagCond k.headRhs b }

structure QNode (G : Form) where
  head : RS G
  rest : List (RS G)
  tail : List (RS G)
  key : QKey

/-- **The replacement for `famsUpTo l pmax` on the promise side.**  Same
type, so `mkJoinPFam` consumes it unchanged.  Unlike the irregular side
there is no admissibility test — (J7) is discharged by pre-filtering
`db.rs` and (J5) is checked in `mkJoinPFam` — so merging is the only
pruning, which is exactly what Lemma 2 licenses. -/
def profPFams (uE uA : List Form) (l : List (RS G)) (maxLayers : Nat) :
    List (RS G × List (RS G)) :=
  Id.run do
    let s : List (QNode G) :=
      (withTails l).map (fun p => ⟨p.1, [], p.2, qKeyOf uE uA p.1⟩)
    let mut seen : List QKey := s.map (·.key)
    let mut out : List (RS G × List (RS G)) := s.map (fun n => (n.head, n.rest))
    let mut frontier := s
    for _ in [0:maxLayers] do
      if frontier.isEmpty then break
      let mut nxt : List (QNode G) := []
      for n in frontier do
        for pb in withTails n.tail do
          let k := n.key.push uE pb.1
          if !(seen.any (fun z => z.same k)) then
            seen := k :: seen
            nxt := ⟨n.head, n.rest ++ [pb.1], pb.2, k⟩ :: nxt
            out := (n.head, n.rest ++ [pb.1]) :: out
      frontier := nxt
    return out

/-! ## The round, and the saturation loop

A copy of `roundStepFast` with ONE line changed: `famsUpToC compatI db.is
cfg.jmax` becomes `profFams db.is`.  Everything else — the new/old split,
the promise families, the insertion — is `Fast`'s, unchanged, so a
difference between the two engines can only come from the family
enumeration. -/

/-- `layers = none` means unbounded arity (bounded only by `db.is.length`,
which is the most members any family can have).  `layers = some k` caps
the arity at `k+1`, which is what the differential test against `Fast`
uses. -/
def roundStepProf (G : Form) (cfg : Config) (layers pLayers : Option Nat)
    (db : DB G) (prev : DB G) : DB G × Nat × Bool × Nat × Nat :=
  let isNewI : IS G → Bool := fun i => !prev.is.any (fun e => sameIS e i)
  let isNewR : RS G → Bool := fun r => !prev.rs.any (fun e => sameRS e r)
  let newIs := db.is.filter isNewI
  let newRs := db.rs.filter isNewR
  let newR1 := newRs.flatMap (fun r => stepR1 G r)
  let newI1 := newRs.flatMap (fun r => stepNotIn G r)
  let newI2 := newIs.flatMap (fun i => stepI1 G i)
  let newI3 := newIs.flatMap (fun i1 =>
    db.is.flatMap (fun i2 => stepOrI G i1 i2 ++ stepOrI G i2 i1))
  let impRes := newIs.map (fun i => stepImpInI G cfg.lamCap i)
  let newI4 := impRes.flatMap (·.1)
  let lamCapped := impRes.any (·.2)
  -- THE ONE CHANGED LINE: profile-indexed, no arity cap
  let famsAll := match layers with
    | none => profFams db.is
    | some k => profFamsN db.is k
  let famsNew := famsAll.filter (fun (a, rest) => isNewI a || rest.any isNewI)
  let famsOld := famsAll.filter (fun (a, rest) => !(isNewI a || rest.any isNewI))
  let newJB := famsNew.flatMap (fun (a, rest) => mkJoinBarrenH a rest)
  let newJF := famsNew.flatMap (fun (a, rest) =>
    if modalContent a rest then mkJoinFH a rest else [])
  -- PROMISE SIDE, profile-indexed (FRJ/Profile.lean §8).  The (J7) filter
  -- is `Fast`'s, unchanged; only the enumeration over the survivors moves.
  let pfamsOf : IS G → List (IS G) → List (RS G × List (RS G)) :=
    fun a rest =>
      let stabAll := unionAll (fun j => stabF a rest j)
      let survivors := db.rs.filter (fun r => stabAll.all (fun X => cloB r.ctx X))
      let uA := stabAll ++ interAll (fun j => thF a rest j)
      let uE := (circPart uA).filterMap (fun f =>
        match f with | Form.circ Y => some Y | _ => none)
      match pLayers with
      | none => profPFams uE uA survivors survivors.length
      | some k => profPFams uE uA survivors k
  let newJP :=
    famsNew.flatMap (fun (a, rest) =>
      if modalContent a rest then mkJoinPFam a rest (pfamsOf a rest) else []) ++
    famsOld.flatMap (fun (a, rest) =>
      if modalContent a rest then
        mkJoinPFam a rest
          ((pfamsOf a rest).filter (fun (p, prest) => isNewR p || prest.any isNewR))
      else [])
  let (db1, n1) := insertAllR db (newR1 ++ newJB ++ newJF ++ newJP)
  let (db2, n2) := insertAllI db1 (newI1 ++ newI2 ++ newI3 ++ newI4)
  (db2, n1 + n2, lamCapped, famsAll.length, (famsUpTo db.rs cfg.pmax).length)

/-- `saturateFast`, with `roundStepProf`.  `jmaxBinding` is recorded as
`false` throughout: the arity cap is not consulted by this engine, so it
cannot bind.  `pmaxBinding` is recorded exactly as before, because the
promise side is unchanged and DOES still cap. -/
def saturateProfL (G : Form) (cfg : Config) (layers pLayers : Option Nat) :
    DB G × FastStats :=
  let db0 : DB G := { rs := seedsR G, is := seedsI G ++ seedsIC G }
  let empty : DB G := { rs := [], is := [] }
  let rec go : Nat → DB G → DB G → FastStats → DB G × FastStats
    | 0, db, _, st => (db, st)
    | fuel + 1, db, prev, st =>
        if db.rs.length > cfg.maxRS || db.is.length > cfg.maxIS then
          (db, { st with dbCapped := true })
        else
          let (db', fresh, lc, nf, np) := roundStepProf G cfg layers pLayers db prev
          let st' := { st with
            roundsUsed := st.roundsUsed + 1,
            lamCapped := st.lamCapped || lc,
            pmaxBinding := match pLayers with
              | none => st.pmaxBinding
              | some _ => st.pmaxBinding || decide (db.rs.length > cfg.pmax),
            fams := max st.fams nf,
            pfams := max st.pfams np }
          if fresh == 0 then (db', st') else go fuel db' db st'
  let (db, st) := go cfg.rounds db0 empty {}
  (db, { st with rsSize := db.rs.length, isSize := db.is.length })

/-- The engine proper: unbounded arity. -/
def saturateProf (G : Form) (cfg : Config) : DB G × FastStats :=
  saturateProfL G cfg none none

/-- Arity matched to `Fast`'s `jmax`, so a verdict difference isolates the
MERGING rather than the extra reach.  `famsUpTo`'s `k` counts the whole
family; layers count the additions after the head. -/
def saturateProfMatched (G : Form) (cfg : Config) : DB G × FastStats :=
  saturateProfL G cfg (some (cfg.jmax - 1)) (some (cfg.pmax - 1))

end FRJ.Search
