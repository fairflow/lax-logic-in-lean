/-
# FRJX — the PATCHED FRJ(◯) saturation engine (untyped probe)

Probe for repairing the FRJ(◯) incompleteness witnesses #80/#81
(cells ρ12 ⊢? ρ9 and ρ13 ⊢? ρ6, both kernel-refuted by `RNDB.sepM`,
both closed cap-free by the Profile engine).

The failure analysis (this session) traced both cells to ONE mechanism:
the ∨-join's conclusion context keeps a second-zone implication `Y ⊃ Z`
only when `Y ∈ Υ` (the paper's `Θ^⊃/Υ` restriction), and the goal's
antecedent (ρ12 resp. ρ13) is an implication forced VACUOUSLY at the
countermodel's root — its own antecedent ι is refuted at the root, in
the crucial cases with the root itself as witness.  `Cl` cannot see
vacuous forcing, and Υ knows only the premises' right formulas.

## The patch, one relaxation applied at the BARREN joins

Replace every "refuted at the new root" test `X ∈ Υ` by membership in
`RefAt(Υ, ctx)`, the closure of Υ under refutations the new root can
certify from its own shape:

    X ∈ Υ                                        (the premise mechanism)
    ⊥ ∈ RefAt                                    (a join root is infallible)
    A ⊃ B ∈ RefAt  if  A ∈ Cl(ctx) ∧ B ∈ RefAt   (the root itself witnesses)
    ◯Z ∈ RefAt     if  Z ∈ RefAt                 (BARREN roots only: the
                                                  modal cone is the root)
    Z₁ ∨ Z₂ ∈ RefAt if both ∈ RefAt;  Z₁ ∧ Z₂ if either

used in (i) the `Θ^⊃` retention filter — kept antecedents feed `Cl(ctx)`,
so the context is a monotone FIXPOINT — and (ii) the ∨-join's `hC` and
the modal join's `hZ`.  Promise and fallible joins are UNTOUCHED in this
probe (their cones are not the root alone, so the ◯-clause is unsound
there; the rest would be sound but is not needed for #80/#81).

Soundness of each clause is a per-clause semantic argument recorded in
the session report; nothing here is trusted — this engine exists to test
whether the patched calculus DERIVES the two cells and to sweep the
462-cell ρ-order for regressions against the kernel ground truth.

`patch := false` must reproduce the reference engine `FRJ.Search.saturate`
row for row — that differential is the transcription check.

Run: `lake env lean --run wip/frjx.lean [diff|cells|sweep]`
-/
import FRJ.Search.Engine
import FRJ.Bridge
import LaxLogic.RN.Rho

open FRJ FRJ.Search Form

namespace FRJX

/-! ## Rows, untyped -/

structure R where
  t : Tag
  ctx : List Form
  rhs : Form
  deriving Repr

structure I where
  stab : List Form
  th : List Form
  rhs : Form
  deriving Repr

/-! ## Zone helpers over a family given as head-and-rest -/

def fam (a : I) (rest : List I) : List I := a :: rest

def unionZ (f : I → List Form) (l : List I) : List Form := l.flatMap f

/-- `⋂` over a nonempty family, mirroring `FRJ.interAll` (filter the
head by membership in every member). -/
def interZ (f : I → List Form) (a : I) (rest : List I) : List Form :=
  (f a).filter (fun x => rest.all (fun i => decide (x ∈ f i)))

def ups (a : I) (rest : List I) : List Form := (fam a rest).map (·.rhs)

/-! ## RefAt and the fixpoint context -/

/-- `X ∈ RefAt(Υ, ctx)` for a BARREN root (`barren := true` enables the
`◯`-clause). -/
def refAtB (barren : Bool) (Υ ctx : List Form) : Form → Bool
  | .bot => true
  | .imp A B =>
      decide (Form.imp A B ∈ Υ) || (cloB ctx A && refAtB barren Υ ctx B)
  | .circ Z => decide (Form.circ Z ∈ Υ) || (barren && refAtB barren Υ ctx Z)
  | .or Z₁ Z₂ =>
      decide (Form.or Z₁ Z₂ ∈ Υ) ||
        (refAtB barren Υ ctx Z₁ && refAtB barren Υ ctx Z₂)
  | .and Z₁ Z₂ =>
      decide (Form.and Z₁ Z₂ ∈ Υ) ||
        refAtB barren Υ ctx Z₁ || refAtB barren Υ ctx Z₂
  | X => decide (X ∈ Υ)

/-- One retention pass: `base` plus the second-zone implications whose
antecedent the current context certifies refuted. -/
def ctxStep (patch : Bool) (Υ base thImps ctx : List Form) : List Form :=
  base ++ thImps.filter (fun f =>
    match f with
    | .imp A _ => if patch then refAtB true Υ ctx A else decide (A ∈ Υ)
    | _ => false)

/-- The (fixpoint) conclusion context of a barren join: with the patch
off this is ONE pass, i.e. exactly the paper's `Θ^⊃/Υ`; with it on,
iterate to the (monotone, bounded) fixpoint. -/
def ctxFix (patch : Bool) (Υ base thImps : List Form) : List Form :=
  if patch then
    (List.range (thImps.length + 1)).foldl
      (fun ctx _ => ctxStep patch Υ base thImps ctx)
      (ctxStep patch Υ base thImps base)
  else ctxStep patch Υ base thImps base

/-- `joinCtxAt`, patched: `Σ^at, Θ^at \ F, Σ^imp, Θ^imp/RefAt`. -/
def joinCtxAtX (patch : Bool) (a : I) (rest : List I) (F : Form) : List Form :=
  let base := atPart (unionZ (·.stab) (fam a rest)) ++
    FRJ.rm (interZ (fun i => atPart i.th) a rest) F ++
    impPart (unionZ (·.stab) (fam a rest))
  ctxFix patch (ups a rest) base (impPart (interZ (·.th) a rest))

/-- `joinCtxOr`, patched: `Σ^at, Θ^at, Σ^imp, Θ^imp/RefAt`. -/
def joinCtxOrX (patch : Bool) (a : I) (rest : List I) : List Form :=
  let base := atPart (unionZ (·.stab) (fam a rest)) ++
    interZ (fun i => atPart i.th) a rest ++
    impPart (unionZ (·.stab) (fam a rest))
  ctxFix patch (ups a rest) base (impPart (interZ (·.th) a rest))

/-! ## Seeds (mirroring `FRJ.Search.seedsR/I/IC`) -/

def seedsR (G : Form) : List R :=
  (sfR G).filterMap (fun F =>
    if F.isPrime then some ⟨.barren, FRJ.rm (gAt G) F, F⟩ else none)

def seedsI (G : Form) : List I :=
  (sfR G).filterMap (fun F =>
    if F.isPrime then
      some ⟨[], (FRJ.rm (gAt G) F) ++ gImp G ++ gCirc G, F⟩
    else none)

def seedsIC (G : Form) : List I :=
  (sfR G).flatMap (fun C =>
    match C with
    | .circ F =>
        let vals := if (gAt G).length ≤ 4 then (gAt G).sublists
          else [[], gAt G, FRJ.rm (gAt G) F]
        vals.filterMap (fun ats =>
          if subB ats (gAt G) && !classForce ats F then
            some ⟨[], vacZoneA G ats, .circ F⟩
          else none)
    | _ => [])

/-! ## Single-premise rules -/

def tagOKB (Γ : List Form) (t : Tag) (Z : Form) : Bool :=
  match t with
  | .barren => true
  | .chain W => coversB Γ W Z
  | .blocked => false

def stepR1 (G : Form) (r : R) : List R :=
  (sfR G).filterMap (fun T =>
    match T with
    | .and A B =>
        if r.rhs = A || r.rhs = B then some ⟨r.t, r.ctx, .and A B⟩ else none
    | .imp A B =>
        if r.rhs = B && cloB r.ctx A then some ⟨r.t, r.ctx, .imp A B⟩ else none
    | .circ Z =>
        if r.rhs = Z && tagOKB r.ctx r.t Z then some ⟨r.t, r.ctx, .circ Z⟩
        else none
    | _ => none)

def stepI1 (G : Form) (i : I) : List I :=
  (sfR G).filterMap (fun T =>
    match T with
    | .and A B =>
        if i.rhs = A || i.rhs = B then some ⟨i.stab, i.th, .and A B⟩ else none
    | _ => none)

def stepOrI (G : Form) (i1 i2 : I) : List I :=
  (sfR G).filterMap (fun T =>
    match T with
    | .or C₁ C₂ =>
        if i1.rhs = C₁ && i2.rhs = C₂ &&
            subB i1.stab (i2.stab ++ i2.th) && subB i2.stab (i1.stab ++ i1.th)
        then some ⟨i1.stab ++ i2.stab, FRJ.cap i1.th i2.th, .or C₁ C₂⟩
        else none
    | _ => none)

def stepImpInI (G : Form) (lamCap : Nat) (i : I) : List I × Bool :=
  let (lams, capped) := lamCandidates i.th lamCap
  (((sfR G).flatMap (fun T =>
    match T with
    | .imp A B =>
        if i.rhs = B then
          lams.filterMap (fun Λ =>
            if subB Λ i.th && cloB (i.stab ++ Λ) A then
              some ⟨i.stab ++ Λ, FRJ.sdiff i.th Λ, .imp A B⟩
            else none)
        else []
    | _ => [])), capped)

def stepNotIn (G : Form) (r : R) : List I :=
  (sfR G).flatMap (fun T =>
    match T with
    | .imp A B =>
        if r.rhs = B && cloB r.ctx A then
          (thetaCandidates G r.ctx A).filterMap (fun l =>
            let Θ := l.filter (fun x => decide (x ∈ gHat G))
            if Θ.all (fun X => cloB r.ctx X) && !cloB Θ A then
              some ⟨[], Θ, .imp A B⟩
            else none)
        else []
    | .circ Z =>
        if r.rhs = Z && tagOKB r.ctx r.t Z then
          [⟨[], (gHat G).filter (fun X => cloB r.ctx X), .circ Z⟩]
        else []
    | _ => [])

/-! ## Joins -/

def j1B (a : I) (rest : List I) : Bool :=
  let l := fam a rest
  -- the i = j instances hold trivially (Σ ⊆ Σ ++ Θ), so quantify over all pairs
  l.all (fun i => l.all (fun j => subB i.stab (j.stab ++ j.th)))

def j2B (a : I) (rest : List I) : Bool :=
  (impPart (unionZ (·.stab) (fam a rest))).all (fun f =>
    match f with
    | .imp A _ => decide (A ∈ ups a rest)
    | _ => true)

/-- The barren joins.  With `patch := true`, the ∨- and ◯-targets test
membership in `RefAt` rather than in Υ, and the context is the fixpoint. -/
def mkJoinBarren (patch : Bool) (G : Form) (a : I) (rest : List I) : List R :=
  if j1B a rest && j2B a rest &&
      (circPart (unionZ (·.stab) (fam a rest))).isEmpty then
    let Υ := ups a rest
    ((sfR G).filterMap (fun F =>
      if F.isPrime && !decide (F ∈ atPart (unionZ (·.stab) (fam a rest))) then
        some ⟨.barren, joinCtxAtX patch a rest F, F⟩
      else none)) ++
    ((sfR G).filterMap (fun T =>
      let ctxO := joinCtxOrX patch a rest
      let hit : Form → Bool := fun C =>
        if patch then refAtB true Υ ctxO C else decide (C ∈ Υ)
      match T with
      | .or C₁ C₂ =>
          if hit C₁ && hit C₂ then some ⟨.barren, ctxO, .or C₁ C₂⟩ else none
      | .circ Z =>
          if hit Z then some ⟨.barren, ctxO, .circ Z⟩ else none
      | _ => none))
  else []

/-- The fallible joins — UNPATCHED (the fallible successor forces every
body, so no `RefAt` clause beyond Υ is sound at that cone). -/
def mkJoinF (G : Form) (a : I) (rest : List I) : List R :=
  if j1B a rest && j2B a rest then
    let circF := circPart (unionZ (·.stab) (fam a rest)) ++
      interZ (fun i => circPart i.th) a rest
    ((sfR G).filterMap (fun F =>
      if F.isPrime && !decide (F ∈ atPart (unionZ (·.stab) (fam a rest))) then
        some ⟨.blocked, joinCtxAtX false a rest F ++ circF, F⟩
      else none)) ++
    ((sfR G).filterMap (fun T =>
      match T with
      | .or C₁ C₂ =>
          if decide (C₁ ∈ ups a rest) && decide (C₂ ∈ ups a rest) then
            some ⟨.blocked, joinCtxOrX false a rest ++ circF, .or C₁ C₂⟩
          else none
      | _ => none))
  else []

/-- Promise-join context: `restrictP (barren ctx ++ (Σ^◯, Θ^◯/Cl(Δ⃗)))`,
mirroring `joinCtxOrP`/`joinCtxAtP` over the list family. -/
def pCtx (base : List Form) (a : I) (rest : List I) (ps : List R) : List Form :=
  let circKeep := circPart (unionZ (·.stab) (fam a rest)) ++
    (interZ (fun i => circPart i.th) a rest).filter (fun f =>
      match f with
      | .circ Y => ps.any (fun p => cloB p.ctx Y)
      | _ => false)
  (base ++ circKeep).filter (fun X => ps.all (fun p => cloB p.ctx X))

/-- The promise joins — UNPATCHED. -/
def mkJoinP (G : Form) (a : I) (rest : List I) (p : R) (prest : List R) : List R :=
  if j1B a rest && j2B a rest then
    let ps := p :: prest
    if (circPart (unionZ (·.stab) (fam a rest))).all (fun f =>
        match f with
        | .circ Y => ps.any (fun q => cloB q.ctx Y)
        | _ => true) &&
      (fam a rest).all (fun i => i.stab.all (fun X =>
        ps.all (fun q => cloB q.ctx X)))
    then
      let chainOK := ps.all (fun q =>
        decide (q.rhs = p.rhs) && tagOKB q.ctx q.t p.rhs)
      let tags : List Tag :=
        .blocked :: (if chainOK then [.chain p.rhs] else [])
      (tags.flatMap (fun tg =>
        ((sfR G).filterMap (fun F =>
          if F.isPrime && !decide (F ∈ atPart (unionZ (·.stab) (fam a rest))) then
            some ⟨tg, pCtx (joinCtxAtX false a rest F) a rest ps, F⟩
          else none)) ++
        ((sfR G).filterMap (fun T =>
          match T with
          | .or C₁ C₂ =>
              if decide (C₁ ∈ ups a rest) && decide (C₂ ∈ ups a rest) then
                some ⟨tg, pCtx (joinCtxOrX false a rest) a rest ps, .or C₁ C₂⟩
              else none
          | _ => none)))) ++
      -- ⋈^◯,p: every promise component pledges the body
      ((sfR G).filterMap (fun T =>
        match T with
        | .circ Z =>
            if decide (Z ∈ ups a rest) &&
                ps.all (fun q => decide (q.rhs = Z) && tagOKB q.ctx q.t Z) then
              some ⟨.chain Z, pCtx (joinCtxOrX false a rest) a rest ps, .circ Z⟩
            else none
        | _ => none))
    else []
  else []

def modalContent (a : I) (rest : List I) : Bool :=
  !(circPart (unionZ (·.stab) (fam a rest))).isEmpty ||
    !(interZ (fun i => circPart i.th) a rest).isEmpty

/-! ## Subsumption and the loop (mirroring the reference engine) -/

def rsLe (r r' : R) : Bool :=
  decide (r.rhs = r'.rhs) && tagLeB r.t r'.t && subB r.ctx r'.ctx

def isLe (i i' : I) : Bool :=
  decide (i.rhs = i'.rhs) && subB i.stab i'.stab && subB i'.stab i.stab
    && subB i.th i'.th

structure DB where
  rs : List R
  is : List I

def insertR (db : DB) (r : R) : DB × Bool :=
  if db.rs.any (fun e => rsLe r e) then (db, false)
  else ({ db with rs := r :: db.rs.filter (fun e => !(rsLe e r)) }, true)

def insertI (db : DB) (i : I) : DB × Bool :=
  if db.is.any (fun e => isLe i e) then (db, false)
  else ({ db with is := i :: db.is.filter (fun e => !(isLe e i)) }, true)

def insertAllR (db : DB) (l : List R) : DB × Nat :=
  l.foldl (fun (acc : DB × Nat) r =>
    let (db', new) := insertR acc.1 r
    (db', acc.2 + (if new then 1 else 0))) (db, 0)

def insertAllI (db : DB) (l : List I) : DB × Nat :=
  l.foldl (fun (acc : DB × Nat) i =>
    let (db', new) := insertI acc.1 i
    (db', acc.2 + (if new then 1 else 0))) (db, 0)

def roundStep (patch : Bool) (G : Form) (cfg : Config) (db : DB) :
    DB × Nat × Bool :=
  let newR1 := db.rs.flatMap (fun r => stepR1 G r)
  let newI1 := db.rs.flatMap (fun r => stepNotIn G r)
  let newI2 := db.is.flatMap (fun i => stepI1 G i)
  let newI3 := db.is.flatMap (fun i1 => db.is.flatMap (fun i2 => stepOrI G i1 i2))
  let impRes := db.is.map (fun i => stepImpInI G cfg.lamCap i)
  let newI4 := impRes.flatMap (·.1)
  let lamCapped := impRes.any (·.2)
  let fams := famsUpTo db.is cfg.jmax
  let newJB := fams.flatMap (fun (a, rest) => mkJoinBarren patch G a rest)
  let newJF := fams.flatMap (fun (a, rest) =>
    if modalContent a rest then mkJoinF G a rest else [])
  let pfams := famsUpTo db.rs cfg.pmax
  let newJP := fams.flatMap (fun (a, rest) =>
    if modalContent a rest then
      pfams.flatMap (fun (p, prest) => mkJoinP G a rest p prest)
    else [])
  let (db1, n1) := insertAllR db (newR1 ++ newJB ++ newJF ++ newJP)
  let (db2, n2) := insertAllI db1 (newI1 ++ newI2 ++ newI3 ++ newI4)
  (db2, n1 + n2, lamCapped)

def saturate (patch : Bool) (G : Form) (cfg : Config) : DB × Stats :=
  let db0 : DB := { rs := seedsR G, is := seedsI G ++ seedsIC G }
  let rec go : Nat → DB → Stats → DB × Stats
    | 0, db, st => (db, st)
    | fuel + 1, db, st =>
        if db.rs.length > cfg.maxRS || db.is.length > cfg.maxIS then
          (db, { st with dbCapped := true })
        else
          let (db', fresh, lc) := roundStep patch G cfg db
          let st' := { st with
            roundsUsed := st.roundsUsed + 1,
            lamCapped := st.lamCapped || lc,
            jmaxBinding := st.jmaxBinding || decide (db.is.length > cfg.jmax),
            pmaxBinding := st.pmaxBinding || decide (db.rs.length > cfg.pmax) }
          if fresh == 0 then (db', st') else go fuel db' st'
  let (db, st) := go cfg.rounds db0 {}
  (db, { st with rsSize := db.rs.length, isSize := db.is.length })

def derivable (G : Form) (db : DB) : Bool :=
  db.rs.any (fun r => decide (r.rhs = G))

end FRJX
