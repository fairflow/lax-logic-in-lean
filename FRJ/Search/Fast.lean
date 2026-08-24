/-
# The fast FRJ(◯) search: same closure, three exact cuts

`FRJ/Search/Engine.lean` recomputes, every round, every family of premises
up to arity `jmax` against every family of promises up to arity `pmax`, and
re-checks `J1`/`J2` inside each promise pairing.  Measured on the RN(◯,{})
bank that is `≈ 10⁶–10⁸` rule instances per round against a database of at
most a few dozen rows.  This module keeps the rule set, the row types and
the derivations exactly as they are, and removes three sources of waste.
None of the three changes the set of derivable rows: the fixpoint reached
is the same one, which is what the differential test against the frozen
engine checks.

**(1) `J1` is pairwise, so admissible families are cliques.**  The side
condition of every join is

    J1 :  ∀ i j, i ≠ j → Σᵢ ⊆ Σⱼ ∪ Θⱼ

a conjunction over ORDERED PAIRS of family members.  A family therefore
satisfies `J1` if and only if each of its two-element subfamilies does, so
the admissible families are exactly the cliques of the digraph

    x → y   iff   Σₓ ⊆ Σ_y ∪ Θ_y   and   Σ_y ⊆ Σₓ ∪ Θₓ

on the irregular rows.  `famsUpToC` enumerates cliques directly instead of
enumerating all `C(|Σ|, ≤ jmax)` subsets and rejecting most of them after
the fact.

**(2) `J1`/`J2` do not depend on the promise family.**  `mkJoinP` re-runs
`j1j2Check` for every promise family paired with the same premise family:
with `≈ 10³` promise families that is a factor of `10³` of repeated work on
the dominant term.  `mkJoinPFam` runs the check once and then loops.

**(3) A family with no new member was already tried.**  Standard
given-clause incrementality: an inference all of whose premises were
present at the start of the previous round fired then, and its conclusion
was inserted (or subsumed, and subsumption is transitive, so it stays
subsumed).  Only families containing at least one row new this round can
contribute.

Caps are unchanged and still reported.  The clique enumeration is exact,
not a heuristic: nothing admissible is skipped.
-/
import FRJ.Search.Engine

namespace FRJ.Search

open Form

variable {G : Form}

/-! ## Row identity, up to the data a rule can see

Rows carry derivations, which have no `DecidableEq`; two rows with the same
sequent are interchangeable for every rule, so "same row" means "same
sequent". -/

def sameIS (x y : IS G) : Bool :=
  decide (x.rhs = y.rhs) && decide (x.stab = y.stab) && decide (x.th = y.th)

def sameRS (x y : RS G) : Bool :=
  decide (x.rhs = y.rhs) && decide (x.ctx = y.ctx) && decide (x.t = y.t)

/-! ## (1) Cliques -/

/-- The pairwise form of `J1`, one direction. -/
def compatI (x y : IS G) : Bool := subB x.stab (y.stab ++ y.th)

/-- `J1`-cliques of size `≤ k` inside `l`, each as an ordered sublist, each
once.  `cur` carries the members already committed to, so extension is
checked against the whole clique rather than the previous element. -/
def cliquesLe {α : Type} (compat : α → α → Bool) (cur : List α) :
    Nat → List α → List (List α)
  | 0, _ => [[]]
  | _, [] => [[]]
  | k + 1, a :: as =>
      cliquesLe compat cur (k + 1) as ++
      (if cur.all (fun y => compat y a && compat a y) then
        (cliquesLe compat (a :: cur) k as).map (a :: ·)
      else [])

/-- `famsUpTo`, restricted to the families that can pass `J1`. -/
def famsUpToC {α : Type} (compat : α → α → Bool) (l : List α) (k : Nat) :
    List (α × List α) :=
  match l with
  | [] => []
  | a :: as =>
      ((cliquesLe compat [a] (k - 1) as).map (fun rest => (a, rest))) ++
        famsUpToC compat as k

/-! ## (2) The barren, fallible and promise joins, with the family-level
sets hoisted out of the `Sf^R(G)` loops -/

/-- `mkJoinBarren` with `⋃ atPart Σ` and `Υ` computed once. -/
def mkJoinBarrenH (a : IS G) (rest : List (IS G)) : List (RS G) :=
  match j1j2Check a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    if hcirc : unionAll (fun j => circPart (stabF a rest j)) = [] then
      let atU := unionAll (fun j => atPart (stabF a rest j))
      let ups := upsilon (rhsF a rest)
      let targets := sfR G
      (targets.filterMap (fun F =>
        if hF : F.isPrime then
          if hFnot : F ∉ atU then
            if hg : F ∈ targets then
              some ⟨.barren, joinCtxAt (stabF a rest) (thF a rest) (rhsF a rest) F, F,
                .joinAt (premF a rest) h1 (hJ2_of_check h2) hcirc hF hFnot hg (CtxEq.refl _)⟩
            else none
          else none
        else none)) ++
      (targets.filterMap (fun T =>
        if hg : T ∈ targets then
          match T, hg with
          | .or C₁ C₂, hg =>
              if hC : C₁ ∈ ups ∧ C₂ ∈ ups then
                some ⟨.barren, joinCtxOr (stabF a rest) (thF a rest) (rhsF a rest),
                  .or C₁ C₂,
                  .joinOr (premF a rest) h1 (hJ2_of_check h2) hcirc hC hg (CtxEq.refl _)⟩
              else none
          | .circ Z, hg =>
              if hZ : Z ∈ ups then
                some ⟨.barren, joinCtxOr (stabF a rest) (thF a rest) (rhsF a rest),
                  .circ Z,
                  .joinCirc (premF a rest) h1 (hJ2_of_check h2) hcirc hZ hg (CtxEq.refl _)⟩
              else none
          | _, _ => none
        else none))
    else []

/-- `mkJoinF` with the same sets hoisted. -/
def mkJoinFH (a : IS G) (rest : List (IS G)) : List (RS G) :=
  match j1j2Check a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    let atU := unionAll (fun j => atPart (stabF a rest j))
    let ups := upsilon (rhsF a rest)
    let targets := sfR G
    (targets.filterMap (fun F =>
      if hF : F.isPrime then
        if hFnot : F ∉ atU then
          if hg : F ∈ targets then
            some ⟨.blocked, joinCtxAtF (stabF a rest) (thF a rest) (rhsF a rest) F, F,
              .joinAtF (premF a rest) h1 (hJ2_of_check h2) hF hFnot hg (CtxEq.refl _)⟩
          else none
        else none
      else none)) ++
    (targets.filterMap (fun T =>
      if hg : T ∈ targets then
        match T, hg with
        | .or C₁ C₂, hg =>
            if hC : C₁ ∈ ups ∧ C₂ ∈ ups then
              some ⟨.blocked, joinCtxOrF (stabF a rest) (thF a rest) (rhsF a rest),
                .or C₁ C₂,
                .joinOrF (premF a rest) h1 (hJ2_of_check h2) hC hg (CtxEq.refl _)⟩
            else none
        | _, _ => none
      else none))

/-- `mkJoinP` over a whole list of promise families, running `j1j2Check`
once for the premise family instead of once per promise family. -/
def mkJoinPFam (a : IS G) (rest : List (IS G))
    (pfams : List (RS G × List (RS G))) : List (RS G) :=
  match j1j2Check a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    -- family-level sets, computed once instead of once per promise family
    -- and once per right-formula (the `let`s are shared at run time; the
    -- dependent checks below see them up to zeta, so the rule's own side
    -- conditions are the ones discharged).
    let atU := unionAll (fun j => atPart (stabF a rest j))
    let ups := upsilon (rhsF a rest)
    let targets := sfR G
    pfams.flatMap (fun (p, prest) =>
      if h5 : ∀ X ∈ unionAll (fun j => circPart (stabF a rest j)),
          CircBodyOk (dctxF p prest) X then
        let hJ5 : ∀ Y : Form,
            Form.circ Y ∈ unionAll (fun j => circPart (stabF a rest j)) →
            ∃ i, Clo (dctxF p prest i) Y := fun _ hm => h5 _ hm
        if h7 : ∀ i j, ∀ X ∈ stabF a rest j, Clo (dctxF p prest i) X then
        let tags : List ((t' : Tag) ×'
            (t' = .blocked ∨ (t' = .chain (drhsF p prest 0) ∧ ∀ i,
              drhsF p prest i = drhsF p prest 0 ∧
              (dtagF p prest i = .barren ∨ ∃ W, dtagF p prest i = .chain W ∧
                Covers (dctxF p prest i) W (drhsF p prest 0))))) :=
          ⟨.blocked, Or.inl rfl⟩ ::
          (if hch : ∀ i, drhsF p prest i = drhsF p prest 0 ∧
              (dtagF p prest i = .barren ∨ ∃ W, dtagF p prest i = .chain W ∧
                Covers (dctxF p prest i) W (drhsF p prest 0)) then
            [⟨.chain (drhsF p prest 0), Or.inr ⟨rfl, hch⟩⟩]
          else [])
        (tags.flatMap (fun tg =>
          (targets.filterMap (fun F =>
            if hF : F.isPrime then
              if hFnot : F ∉ atU then
                if hg : F ∈ targets then
                  some ⟨tg.1,
                    joinCtxAtP (stabF a rest) (thF a rest) (rhsF a rest) F (dctxF p prest), F,
                    .joinAtP (premF a rest) (dpsF p prest) h1 (hJ2_of_check h2)
                      hJ5 h7 tg.2 hF hFnot hg (CtxEq.refl _)⟩
                else none
              else none
            else none)) ++
          (targets.filterMap (fun T =>
            if hg : T ∈ targets then
              match T, hg with
              | .or C₁ C₂, hg =>
                  if hC : C₁ ∈ ups ∧ C₂ ∈ ups then
                    some ⟨tg.1,
                      joinCtxOrP (stabF a rest) (thF a rest) (rhsF a rest) (dctxF p prest),
                      .or C₁ C₂,
                      .joinOrP (premF a rest) (dpsF p prest) h1 (hJ2_of_check h2)
                        hJ5 h7 tg.2 hC hg (CtxEq.refl _)⟩
                  else none
              | _, _ => none
            else none)))) ++
        (targets.filterMap (fun T =>
          if hg : T ∈ targets then
            match T, hg with
            | .circ Z, hg =>
                if hZ : Z ∈ ups then
                  if hDs : ∀ i, drhsF p prest i = Z ∧
                      (dtagF p prest i = .barren ∨ ∃ W, dtagF p prest i = .chain W ∧
                        Covers (dctxF p prest i) W Z) then
                    some ⟨.chain Z,
                      joinCtxOrP (stabF a rest) (thF a rest) (rhsF a rest) (dctxF p prest),
                      .circ Z,
                      .joinCircP (premF a rest) (dpsF p prest) h1 (hJ2_of_check h2)
                        hJ5 h7 hDs hZ hg (CtxEq.refl _)⟩
                  else none
                else none
            | _, _ => none
          else none))
        else []
      else [])

/-! ## (3) The incremental round -/

structure FastStats extends Stats where
  fams : Nat := 0
  pfams : Nat := 0

/-- One round.  `prev` is the database as it stood at the START of the
previous round: rows outside it are the ones that can license something
new. -/
def roundStepFast (G : Form) (cfg : Config) (db : DB G) (prev : DB G) :
    DB G × Nat × Bool × Nat × Nat :=
  let isNewI : IS G → Bool := fun i => !prev.is.any (fun e => sameIS e i)
  let isNewR : RS G → Bool := fun r => !prev.rs.any (fun e => sameRS e r)
  let newIs := db.is.filter isNewI
  let newRs := db.rs.filter isNewR
  -- single-premise rules, on new rows only
  let newR1 := newRs.flatMap (fun r => stepR1 G r)
  let newI1 := newRs.flatMap (fun r => stepNotIn G r)
  let newI2 := newIs.flatMap (fun i => stepI1 G i)
  -- ∨∉ needs a pair; at least one member must be new
  let newI3 := newIs.flatMap (fun i1 =>
    db.is.flatMap (fun i2 => stepOrI G i1 i2 ++ stepOrI G i2 i1))
  let impRes := newIs.map (fun i => stepImpInI G cfg.lamCap i)
  let newI4 := impRes.flatMap (·.1)
  let lamCapped := impRes.any (·.2)
  -- joins over J1-cliques
  let famsAll := famsUpToC compatI db.is cfg.jmax
  let famsNew := famsAll.filter (fun (a, rest) => isNewI a || rest.any isNewI)
  let famsOld := famsAll.filter (fun (a, rest) => !(isNewI a || rest.any isNewI))
  let newJB := famsNew.flatMap (fun (a, rest) => mkJoinBarrenH a rest)
  let newJF := famsNew.flatMap (fun (a, rest) =>
    if modalContent a rest then mkJoinFH a rest else [])
  -- `J7` (`∀ i j, ∀ X ∈ Σⱼ, Clo Δᵢ X`) is a condition on ONE promise row at
  -- a time, so filter the rows first and enumerate promise families only
  -- over the survivors, instead of enumerating all of them and rejecting
  -- each after `|family| · |Σ|` closure tests.
  let pfamsOf : IS G → List (IS G) → List (RS G × List (RS G)) :=
    fun a rest =>
      let stabAll := unionAll (fun j => stabF a rest j)
      famsUpTo (db.rs.filter (fun r => stabAll.all (fun X => cloB r.ctx X))) cfg.pmax
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

def saturateFast (G : Form) (cfg : Config) : DB G × FastStats :=
  let db0 : DB G := { rs := seedsR G, is := seedsI G ++ seedsIC G }
  let empty : DB G := { rs := [], is := [] }
  let rec go : Nat → DB G → DB G → FastStats → DB G × FastStats
    | 0, db, _, st => (db, st)
    | fuel + 1, db, prev, st =>
        if db.rs.length > cfg.maxRS || db.is.length > cfg.maxIS then
          (db, { st with dbCapped := true })
        else
          let (db', fresh, lc, nf, np) := roundStepFast G cfg db prev
          let st' := { st with
            roundsUsed := st.roundsUsed + 1,
            lamCapped := st.lamCapped || lc,
            jmaxBinding := st.jmaxBinding || decide (db.is.length > cfg.jmax),
            pmaxBinding := st.pmaxBinding || decide (db.rs.length > cfg.pmax),
            fams := max st.fams nf,
            pfams := max st.pfams np }
          if fresh == 0 then (db', st') else go fuel db' db st'
  let (db, st) := go cfg.rounds db0 empty {}
  (db, { st with rsSize := db.rs.length, isSize := db.is.length })

end FRJ.Search
