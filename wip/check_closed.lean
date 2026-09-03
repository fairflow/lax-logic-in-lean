/-
# `checkClosed`: the verified certificate of an engine store

The practical decider (docs/checkclosed-checks.md) is the discover-then-pin
pattern: an UNTRUSTED engine (`FRJ.Search.W.wOps`, bounded join arity)
proposes a store of FRJW disproofs; a VERIFIED Boolean check certifies
that the store is closed under the rules; the closure theorem then decides
`G`.  This file assembles the check from its two halves,

  * `chkScan` (`wip/check_scan.lean`) — the thirteen non-join clauses,
  * `chkJoins` (`wip/check_join.lean`) — the eight join clauses at the
    distinct-goal / hitting-set arities of `DBClosedDG`,

with the duplicate-freeness the join half needs, and proves

    checkClosed G db = true  →  DBClosedDG G db   (`checkClosed_sound`)

so that, through `dbClosed_of_dg` (`wip/dbclosed_dg.lean`) and
`decideGbuW_of_dbClosed` (FRJ/Gbu/W/Closure.lean),

    checkClosed G db = true  →  ProvableGbuC G ⊕' DisprovableW G.

`rowsOfDBO` carries an engine store (`DBO (wOps G)`) into the row type
the contract speaks about; `decideByEngine` is the end-to-end untrusted
engine + verified checker + closure theorem.  The objects stored are
DISPROOFS in the sense of FRJW (never "proofs"); a `none` from
`decideByEngine` is `not-closed-within-bound`, never a verdict.
-/
import wip.check_scan
import wip.check_join
import FRJ.Search.OpsW

open FRJ Form FRJ.Gbu FRJ.Gbu.W FRJ.Search FRJ.Search.W

namespace FRJ.Arity

/-! ## 1. The check -/

/-- The verified certificate: duplicate-free sequents (the join half's
reindexing needs it), the thirteen scan clauses, the eight join
clauses. -/
def checkClosed (G : Form) (db : List (WRow G)) : Bool :=
  decide ((db.map (·.s)).Nodup) && chkScan G db && chkJoins G db

theorem checkClosed_parts {G : Form} {db : List (WRow G)}
    (h : checkClosed G db = true) :
    (db.map (·.s)).Nodup ∧ chkScan G db = true ∧ chkJoins G db = true := by
  simp only [checkClosed, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## 2. Soundness -/

/-- **`checkClosed` is sound for the restricted contract.** -/
theorem checkClosed_sound {G : Form} {db : List (WRow G)}
    (h : checkClosed G db = true) : DBClosedDG G db := by
  obtain ⟨hnd, hs, hj⟩ := checkClosed_parts h
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
    chkScan_sound hs
  obtain ⟨jAt, jOr, jCirc, jAtF, jOrF, jAtP, jOrP, jCircP⟩ := chkJoins_split hj
  exact
    { axR := p1, andR1 := p2, andR2 := p3, impIn := p4, circIn := p5,
      joinAt := chkJoinAt_sound hnd jAt,
      joinOr := chkJoinOr_sound hnd jOr,
      joinCirc := chkJoinCirc_sound hnd jCirc,
      joinAtP := chkJoinAtP_sound hnd jAtF jAtP,
      joinOrP := chkJoinOrP_sound hnd jOrF jOrP,
      joinCircP := chkJoinCircP_sound hnd jCircP,
      joinAtF := chkJoinAtF_sound hnd jAtF,
      joinOrF := chkJoinOrF_sound hnd jOrF,
      axI := p6, andI1 := p7, andI2 := p8, orI := p9, impInI := p10,
      lift := p11, circNotIn := p12, axIC := p13 }

/-- **`checkClosed` is sound for the full contract.** -/
theorem dbClosed_of_check {G : Form} {db : List (WRow G)}
    (h : checkClosed G db = true) : DBClosed G db :=
  dbClosed_of_dg (checkClosed_sound h)

/-! ## 3. The decision from a certified store -/

/-- **The decision from any store the check certifies.**  The store may
come from anywhere — the verified saturation, the untrusted engine, a
file — only the certificate matters. -/
def decideGbuW_of_check {G : Form} (db : List (WRow G))
    (h : checkClosed G db = true) : ProvableGbuC G ⊕' DisprovableW G :=
  decideGbuW_of_dbClosed db (dbClosed_of_check h)

/-! ## 4. The engine store as rows -/

/-- An engine store (`DBO (wOps G)`) as contract rows: the regular rows
then the irregular ones, each carrying its `FRJWr`/`FRJWi` derivation. -/
def rowsOfDBO (G : Form) (db : DBO (wOps G)) : List (WRow G) :=
  db.rs.map (fun (r : WRS G) => ⟨.reg r.t r.ctx r.rhs, r.der⟩) ++
    db.is.map (fun (i : WIS G) => ⟨.irr i.stab i.th i.rhs, i.der⟩)

/-- The untrusted engine's store for `G` under `cfg`, as contract rows. -/
def engineRows (G : Form) (cfg : Config) : List (WRow G) :=
  rowsOfDBO G (saturateO (wOps G) cfg).1

/-- **End to end**: run the untrusted engine, certify its store, decide.
`none` means the engine's store did not pass the check within `cfg`
(a join-arity bound too small, or a round/size cap) — a
`not-closed-within-bound`, never a verdict about `G`. -/
def decideByEngine (G : Form) (cfg : Config) :
    Option (ProvableGbuC G ⊕' DisprovableW G) :=
  let db := engineRows G cfg
  if h : checkClosed G db = true then some (decideGbuW_of_check db h) else none

/-- The DATA decision from a certified engine store (`decideOfStore` at
the certificate): the derivations themselves, which is what the output
layer (proof terms, countermodels) consumes.  `none` as in
`decideByEngine`. -/
def decideDataByEngine (G : Form) (cfg : Config) :
    Option (GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)) :=
  let db := engineRows G cfg
  if h : checkClosed G db = true then
    some (decideOfStore db (dbClosed_of_check h))
  else none

/-! ## Pins -/

/-- info: 'FRJ.Arity.checkClosed_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkClosed_sound

/-- info: 'FRJ.Arity.dbClosed_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dbClosed_of_check

/-- info: 'FRJ.Arity.decideGbuW_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decideGbuW_of_check

/-- info: 'FRJ.Arity.decideByEngine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decideByEngine

/-- info: 'FRJ.Arity.decideDataByEngine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decideDataByEngine

end FRJ.Arity
