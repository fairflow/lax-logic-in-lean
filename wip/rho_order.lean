/-
# The order on the 22 closed-fragment classes — and the sweep re-run
with the repaired normalisation pipeline

`docs/pcll-closed-fragment-catalogue.md` certifies 22 pairwise-distinct
`DerivU`-classes with a representative of `crank ≤ 7`, and then says
explicitly that the new nodes are NOT placed: "placing the new nodes
needs their order cells, not yet computed."  Eight of the 22 are sweep
discoveries (ρ13 and the seven combination classes ρ15–ρ21); their
position relative to the fifteen dictionary classes, and relative to
each other, has never been computed.

This file computes it: the full 22 × 22 derivability matrix for
`ConfluentU.DerivU`, and the covering relation extracted from it.

NEW FILE — nothing existing is edited (`wip/closed_frag.lean` and the
whole `LJF*` family are imported read-only; another agent is working
in the LJF tree concurrently).

## Verdicts, per repo doctrine

* **⊢** — `ρi ⊢ ρj` certified by the positive tier ladder
  (`decidePosT`, then the `escalate` ladder).  Sound for `DerivU` by
  `RNC.derivU_of_proved`.
* **⊬** — a mutually confluent countermodel on the battery: a world
  forcing `ρi` but not `ρj`.  Exactly what
  `RNC.not_derivU_of_checkConf` consumes, so kernel-escalatable cell
  by cell; `mode pin` emits the pin lines.
* **flag** — no separation on the battery and no proof within budget.
  Never dropped; re-run at a raised budget.

The battery is `wip/closed_frag.lean`'s: ALL well-formed mutually
confluent frames on ≤ 4 worlds, plus the canonical rooted 5-world
orbits.

## Modes

    rhoorder norm      -- the pipeline's effect on the sweep's own cells
    rhoorder matrix    -- the 22 × 22 order (the main run)
    rhoorder pin       -- matrix, plus a pin line per certified ⊬
-/
import LaxLogic.PLLSearch
import LaxLogic.PLLConfluentComplete
import LaxLogic.PLLSearchConf
import Rewrite

/-! ## The sweep's machinery, transcribed

`wip/closed_frag.lean` defines a root-level `main`, so importing it
into another executable is impossible.  Rather than edit that file —
which is out of bounds this session — its battery, vector, tier-ladder
and normalisation machinery is transcribed VERBATIM below into
namespace `PLLND.RNC.CFX` (only the namespace name differs).  Keep the
two in step: if `closed_frag.lean` changes, re-transcribe. -/

open PLLFormula

namespace PLLND
namespace RNC
namespace CFX

/-! ## Toolkit, copied verbatim from `wip/rnc_probe.lean`

(That module carries its own `def main`, so it cannot be imported into
an exe root; the searcher/battery toolkit below is its §§ "confluent
battery" / "positive tiers" / "rooted 5-world battery", unchanged, in
namespace `PLLND.RNC.CF` instead of `PLLND.RNC`.  `confB` and the
certificate theorems come from the library, `LaxLogic/PLLSearchConf.lean`.) -/

/-- The 15 PLL representatives of wip/rnDict.lean. -/
def q0 : PLLFormula := .falsePLL
def q1 : PLLFormula := (.ifThen q0 q0)
def q2 : PLLFormula := (.somehow q0)
def q3 : PLLFormula := (.ifThen q2 q0)
def q4 : PLLFormula := (.or q2 q3)
def q5 : PLLFormula := (.somehow q3)
def q6 : PLLFormula := (.ifThen q3 q0)
def q7 : PLLFormula := (.or q3 q6)
def q8 : PLLFormula := (.ifThen q5 q4)
def q9 : PLLFormula := (.or q5 q6)
def q10 : PLLFormula := (.ifThen q6 q2)
def q11 : PLLFormula := (.or q6 q10)
def q12 : PLLFormula := (.somehow q7)
def q13 : PLLFormula := (.somehow q8)
def q14 : PLLFormula := (.ifThen q10 q5)

/-- The four closure witnesses (wip/rnDictRefute.lean). -/
def w15 : PLLFormula := q8.and q10
def w16 : PLLFormula := q9.ifThen q4
def w17 : PLLFormula := q12.ifThen q4
def w18 : PLLFormula := q14.ifThen q4

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as => (subsets as) ++ (subsets as).map (a :: ·)

def pairsOf (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun a =>
    (List.range n).filterMap fun b => if a = b then none else some (a, b)

def memP (r : List (Nat × Nat)) (p : Nat × Nat) : Bool := decide (p ∈ r)

def transL (r : List (Nat × Nat)) : Bool :=
  r.all fun p => r.all fun q =>
    !(decide (p.2 = q.1)) || memP r (p.1, q.2)

def antisymL (r : List (Nat × Nat)) : Bool :=
  r.all fun p => !(memP r (p.2, p.1))

def upClosedL (r : List (Nat × Nat)) (s : List Nat) : Bool :=
  s.all fun w => r.all fun p =>
    !(decide (p.1 = w)) || decide (p.2 ∈ s)

def framesN (n : Nat) : List FinCM :=
  ((subsets (pairsOf n)).filter fun ri => transL ri && antisymL ri).flatMap
    fun ri =>
      ((subsets ri).filter transL).flatMap fun rm =>
        ((subsets (List.range n)).filter (upClosedL ri)).filterMap fun fall =>
          let M : FinCM := ⟨n, ri, rm, fall, []⟩
          if M.wellB && confB M then some M else none

def battery : Array FinCM :=
  (framesN 1 ++ framesN 2 ++ framesN 3 ++ framesN 4).toArray

def subsF : PLLFormula → List PLLFormula
  | .and A B => .and A B :: (subsF A ++ subsF B)
  | .or A B => .or A B :: (subsF A ++ subsF B)
  | .ifThen A B => .ifThen A B :: (subsF A ++ subsF B)
  | .somehow A => .somehow A :: subsF A
  | F => [F]

def closureL (l : List PLLFormula) : List PLLFormula :=
  (l.flatMap subsF).eraseDups

def orPairs (l : List PLLFormula) : List (PLLFormula × PLLFormula) :=
  l.filterMap fun φ =>
    match φ with
    | .or A B => some (A, B)
    | _ => none

/-- The four disjunctions generating the fragment's ∨-structure. -/
def canon4 : List (PLLFormula × PLLFormula) :=
  [(q2, q3), (q3, q6), (q5, q6), (q6, q10)]

def tier1 (X Y : PLLFormula) : List (PLLFormula × PLLFormula) :=
  (orPairs (closureL [X, Y]) ++ canon4).eraseDups

def distsOf (ps : List (PLLFormula × PLLFormula)) : List PLLFormula :=
  ps.map fun p => ConfluentU.distF p.1 p.2

/-- Strip a chain of top-level implications. -/
def stripImp : PLLFormula → List PLLFormula × PLLFormula
  | .ifThen A B => let (as, h) := stripImp B; (A :: as, h)
  | C => ([], C)

/-- Cheap syntactic derivability guard (see rnc_probe). -/
def trivHead (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  let (as, h) := stripImp C
  decide (h ∈ Γ) || decide (h ∈ as) || decide (h = q1)

def andParts : PLLFormula → List PLLFormula
  | .and A B => andParts A ++ andParts B
  | F => [F]

/-- Sound sequent preprocessing: uncurry the goal's ⊃-chain, split
∧-premises. -/
def preprocess : List PLLFormula → PLLFormula → List PLLFormula × PLLFormula
  | Γ, .ifThen A B => preprocess (A :: Γ) B
  | Γ, C => (Γ.flatMap andParts, C)

def provedAt (b : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  trivHead Γ C ||
  (let (Γ', C') := preprocess Γ C
   decide (C' ∈ Γ') ||
   match Search.decide { findBudget := some b, emitClosureCap := 0 } Γ' C' with
   | .proved _ => true
   | _ => false)

inductive Verd where
  | proved (tier : Nat)
  | refuted (fi : Nat) (w : Nat)
  | unknown
deriving Repr, DecidableEq

def Verd.tag : Verd → String
  | .proved t => s!"P{t}"
  | .refuted fi w => s!"R[{fi}.{w}]"
  | .unknown => "?"

/-- ONE application of distribution, cut-style. -/
def provedDist1 (b : Nat) (X Y : PLLFormula) : Bool :=
  (tier1 X Y).any fun p =>
    let mid := (somehow p.1).or (somehow p.2)
    provedAt b [X] (somehow (p.1.or p.2)) && provedAt b [mid, X] Y

/-- Two nested applications of distribution, cut-style. -/
def provedDist2 (b : Nat) (X Y : PLLFormula) : Bool :=
  (tier1 X Y).any fun p =>
    let mid := (somehow p.1).or (somehow p.2)
    provedAt b [X] (somehow (p.1.or p.2)) &&
      ((tier1 mid Y).any fun q =>
        let mid2 := (somehow q.1).or (somehow q.2)
        provedAt b [mid, X] (somehow (q.1.or q.2)) &&
          provedAt b [mid2, mid, X] Y)

/-- Tier ladder (rnc_probe's `decidePosT`). -/
def decidePosT (cap : Nat) (X Y : PLLFormula) : Verd :=
  if provedAt 20000 [X] Y then .proved 0
  else if cap ≥ 1 && provedDist1 15000 X Y then .proved 1
  else if cap ≥ 2 && provedDist2 12000 X Y then .proved 2
  else if cap ≥ 3 &&
      (tier1 X Y).any (fun p => provedAt 8000 [X, ConfluentU.distF p.1 p.2] Y) then
    .proved 3
  else if cap ≥ 4 && provedAt 40000 (X :: distsOf (tier1 X Y)) Y then .proved 4
  else .unknown

/-! Rooted 5-world confluent battery (canonical orbits). -/

def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a < b then true else if b < a then false else ltKey as bs

def keyOf (r : List (Nat × Nat)) : List Nat :=
  (r.map fun q => q.1 * 16 + q.2).mergeSort (fun a b => a ≤ b)

def pairKey (ri rm : List (Nat × Nat)) : List Nat :=
  keyOf ri ++ [999] ++ keyOf rm

def applyPerm (p : List Nat) (k : Nat) : Nat :=
  if k = 0 then 0 else p.getD (k - 1) k

def isCanon (ri4 rm : List (Nat × Nat)) : Bool :=
  let k0 := pairKey ri4 rm
  ([1, 2, 3, 4].permutations).all fun p =>
    let ri' := ri4.map fun q => (applyPerm p q.1, applyPerm p q.2)
    let rm' := rm.map fun q => (applyPerm p q.1, applyPerm p q.2)
    !(ltKey (pairKey ri' rm') k0)

def framesRooted5 : List FinCM :=
  let inner := (pairsOf 4).map fun q => (q.1 + 1, q.2 + 1)
  ((subsets inner).filter fun ri4 => transL ri4 && antisymL ri4).flatMap
    fun ri4 =>
      let ri := ((List.range 4).map fun k => (0, k + 1)) ++ ri4
      (((subsets ri).filter transL).filter (isCanon ri4)).flatMap fun rm =>
        if confB ⟨5, ri, rm, [], []⟩ then
          ((subsets (List.range 5)).filter (upClosedL ri)).filterMap
            fun fall =>
              let M : FinCM := ⟨5, ri, rm, fall, []⟩
              if M.wellB && confB M then some M else none
        else []

def vecOf (M : FinCM) (φ : PLLFormula) : Array Bool :=
  (Array.range M.n).map fun w => M.forceB w φ

/-! ## End of the copied toolkit -/

/-- `SemUI.crank`, restated locally (avoids the `PLLSemUILayered`
import): atoms/⊥ 0, ∧/∨ max, ⊃ +1, ◯ +2. -/
def crankL : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and a b => max (crankL a) (crankL b)
  | .or a b => max (crankL a) (crankL b)
  | .ifThen a b => max (crankL a) (crankL b) + 1
  | .somehow a => crankL a + 2

def sizeF : PLLFormula → Nat
  | .and a b => sizeF a + sizeF b + 1
  | .or a b => sizeF a + sizeF b + 1
  | .ifThen a b => sizeF a + sizeF b + 1
  | .somehow a => sizeF a + 1
  | _ => 1

/-- Injective string key (prefix code) — the canonical order for the
∧/∨ argument sort and the seen-set. -/
def keyF : PLLFormula → String
  | .falsePLL => "F"
  | .prop s => "P" ++ s ++ ";"
  | .and a b => "A" ++ keyF a ++ "," ++ keyF b ++ ";"
  | .or a b => "O" ++ keyF a ++ "," ++ keyF b ++ ";"
  | .ifThen a b => "I" ++ keyF a ++ "," ++ keyF b ++ ";"
  | .somehow a => "S" ++ keyF a ++ ";"

/-! ## The normalizer (all rewrites are plain-PLL interderivabilities) -/

def mkAnd (a b : PLLFormula) : PLLFormula :=
  if a = falsePLL ∨ b = falsePLL then falsePLL
  else if a = truePLL then b
  else if b = truePLL then a
  else if a = b then a
  else if keyF a ≤ keyF b then .and a b else .and b a

def mkOr (a b : PLLFormula) : PLLFormula :=
  if a = falsePLL then b
  else if b = falsePLL then a
  else if a = truePLL ∨ b = truePLL then truePLL
  else if a = b then a
  else if keyF a ≤ keyF b then .or a b else .or b a

def mkImp (a b : PLLFormula) : PLLFormula :=
  if a = falsePLL then truePLL
  else if b = truePLL then truePLL
  else if a = truePLL then b
  else if a = b then truePLL
  else .ifThen a b

/-- `◯⊤ = ⊤` (`⊤ ⊢ ◯⊤` by `laxIntro`; `◯⊤ ⊃ ⊤` trivially) and
`◯◯φ = ◯φ` (unit and join of the lax modality). -/
def mkBox (a : PLLFormula) : PLLFormula :=
  if a = truePLL then truePLL
  else match a with
    | .somehow _ => a
    | _ => .somehow a

def nfc : PLLFormula → PLLFormula
  | .and a b => mkAnd (nfc a) (nfc b)
  | .or a b => mkOr (nfc a) (nfc b)
  | .ifThen a b => mkImp (nfc a) (nfc b)
  | .somehow a => mkBox (nfc a)
  | F => F

/-! ## Display -/

mutual
partial def ppA (F : PLLFormula) : String :=
  match F with
  | .falsePLL => "⊥"
  | .prop s => s
  | .ifThen _ _ => if F = truePLL then "⊤" else s!"({pp F})"
  | .somehow a => s!"◯{ppA a}"
  | _ => s!"({pp F})"

partial def pp (F : PLLFormula) : String :=
  match F with
  | .falsePLL => "⊥"
  | .prop s => s
  | .and a b => s!"{ppA a} ∧ {ppA b}"
  | .or a b => s!"{ppA a} ∨ {ppA b}"
  | .ifThen a b =>
    if F = truePLL then "⊤"
    else if b = falsePLL then s!"¬{ppA a}"
    else s!"{ppA a} ⊃ {ppA b}"
  | .somehow a => s!"◯{ppA a}"
end

/-! ## Classification -/

structure RepC where
  name : String
  F : PLLFormula
  rk : Nat                       -- crank at discovery (minimal, see header)
  vec : Array (Array Bool)       -- forcing vectors over the battery

instance : Inhabited RepC := ⟨⟨"", falsePLL, 0, #[]⟩⟩

inductive Cls where
  | newClass
  | member (idx t1 t2 : Nat)
  | flagged (idx : Nat) (d1 d2 : String)

/-- Vector shortlist, then the positive tier ladder.  Representatives
are pairwise vector-distinct, so at most one can agree with `F`. -/
def classifyF (bat : Array FinCM) (reps : Array RepC) (F : PLLFormula) :
    Cls × Array (Array Bool) :=
  let vF := bat.map fun M => vecOf M F
  match (List.range reps.size).filter
      (fun c => decide ((reps.getD c default).vec = vF)) with
  | [] => (.newClass, vF)
  | c :: _ =>
    let r := reps.getD c default
    match decidePosT 2 F r.F, decidePosT 2 r.F F with
    | .proved t1, .proved t2 => (.member c t1 t2, vF)
    | d1, d2 => (.flagged c d1.tag d2.tag, vF)

/-- One-step connective closure over the representatives, capped at
`crank ≤ rcap`, normalized. -/
def genFrom (reps : Array RepC) (rcap : Nat) : List PLLFormula :=
  let rl := reps.toList.map (·.F)
  let uns :=
    (rl.map fun a => nfc (.somehow a)) ++
    (rl.flatMap fun a => rl.flatMap fun b =>
      [nfc (.and a b), nfc (.or a b), nfc (.ifThen a b)])
  (uns.filter fun F => crankL F ≤ rcap).eraseDups

def sortCands (l : List PLLFormula) : List PLLFormula :=
  l.mergeSort fun a b =>
    let (ca, cb) := (crankL a, crankL b)
    if ca ≠ cb then decide (ca < cb)
    else
      let (sa, sb) := (sizeF a, sizeF b)
      if sa ≠ sb then decide (sa < sb) else decide (keyF a ≤ keyF b)

/-- The escalation ladder of `phaseR` (one positive push per unproved
direction of a flagged cell). -/
def escalate (X Y : PLLFormula) : Option String :=
  if provedAt 100000 [X] Y then some "plain PLL, budget 100000"
  else if provedDist1 60000 X Y then some "one dist application, budget 60000"
  else if provedDist2 40000 X Y then some "two dist applications, budget 40000"
  else if (tier1 X Y).any
      (fun p => provedAt 60000 [X, ConfluentU.distF p.1 p.2] Y) then
    some "single instance premise, budget 60000"
  else if provedAt 100000 (X :: distsOf (tier1 X Y)) Y then
    some "full tier-1 premise list, budget 100000"
  else none

/-- First battery cell separating `F` from `G` (a world forcing `F` but
not `G`): a mutually confluent countermodel to `[F] ⊢ G`. -/
def firstSep (bat : Array FinCM) (vF vG : Array (Array Bool)) :
    Option (Nat × Nat) := Id.run do
  for fi in [0:bat.size] do
    let a := vF.getD fi #[]
    let b := vG.getD fi #[]
    for w in [0:a.size] do
      if a.getD w false && !(b.getD w false) then
        return some (fi, w)
  return none

def pinLine (bat : Array FinCM) (fi w : Nat) (X Y : PLLFormula) : String :=
  let M := bat.getD fi ⟨0, [], [], [], []⟩
  s!"    pin: ¬ ConfluentU.DerivU [{pp X}] ({pp Y}) := not_derivU_of_checkConf (M := {Search.srcOfCM M}) (w := {w}) (by decide) (by decide)"

/-! ## The sweep -/

def dictSeeds : List (String × PLLFormula) :=
  [("q0", q0), ("q1", q1), ("q2", q2), ("q3", q3), ("q4", q4),
   ("q5", q5), ("q6", q6), ("q7", q7), ("q8", q8), ("q9", q9),
   ("q10", q10), ("q11", q11), ("q12", q12), ("q13", q13), ("q14", q14),
   ("w15", w15), ("w16", w16), ("w17", w17), ("w18", w18)]

end CFX
end RNC
end PLLND

open PLLND PLLND.RNC PLLND.RNC.CFX PLLFormula
open Rewrite (simplifyWith fullSetC canon)

namespace RhoOrder

abbrev F := PLLFormula

/-! ## The 22 representatives, in the catalogue's ρ-numbering

Transcribed from the catalogue's "was" column, so every one of these
is the formula the 680-cell sweep actually classified. -/

def r13 : F := q10.ifThen q4
def w1  : F := w16

def rhos : List (String × F) :=
  [ ("ρ0",  q0),                ("ρ1",  q1),
    ("ρ2",  q2),                ("ρ3",  q3),
    ("ρ4",  q4),                ("ρ5",  q6),
    ("ρ6",  q7),                ("ρ7",  q5),
    ("ρ8",  q10),               ("ρ9",  q9),
    ("ρ10", q11),               ("ρ11", q8),
    ("ρ12", q14),               ("ρ13", r13),
    ("ρ14", w1),                ("ρ15", q8.or q5),
    ("ρ16", w1.or q5),          ("ρ17", q6.or w1),
    ("ρ18", w1.or q9),          ("ρ19", q8.ifThen q5),
    ("ρ20", q8.ifThen q7),      ("ρ21", w1.ifThen q5) ]

/-- The eight sweep discoveries — the classes the catalogue never
placed.  ρ13 is a new SHAPE; ρ15–ρ21 are combinations. -/
def discovered : List Nat := [13, 15, 16, 17, 18, 19, 20, 21]

def rhoF (i : Nat) : F := (rhos.getD i ("", q0)).2
def rhoN (i : Nat) : String := (rhos.getD i ("", q0)).1

def n : Nat := rhos.length

/-! ## Part A — what the repaired pipeline does to the sweep's cells

The sweep quotients candidates by `nfc`, a purely syntactic folding.
The certified simpset is a strictly stronger quotient: same soundness
(every step is an `Interd`), but it also knows 236 kernel-checked
dictionary cells.  This part measures the difference on the sweep's
OWN generated stream rather than on a synthetic corpus. -/

def fuel : Nat := 60

def simp (φ : F) : F := simplifyWith fullSetC fuel φ

/-- The sweep's one-step closure, as `genFrom` builds it, but from the
22 representatives and without a crank cap — the cells a stratum-8
continuation would have to classify. -/
def sweepCells : List F :=
  let rl := rhos.map (·.2)
  (rl.map (fun a => PLLFormula.somehow a)) ++
  (rl.flatMap fun a => rl.flatMap fun b =>
    [PLLFormula.and a b, PLLFormula.or a b, PLLFormula.ifThen a b])

def normReport : IO Unit := do
  let cells := sweepCells
  let rawD := (cells.map keyF).eraseDups.length
  let nfcD := (cells.map (fun c => keyF (nfc c))).eraseDups.length
  let simD := (cells.map (fun c => keyF (simp c))).eraseDups.length
  let rawC := cells.foldl (fun a c => a + crankL c) 0
  let nfcC := cells.foldl (fun a c => a + crankL (nfc c)) 0
  let simC := cells.foldl (fun a c => a + crankL (simp c)) 0
  IO.println "=== Part A: the sweep's own closure cells under each normaliser ==="
  IO.println s!"cells generated from the 22 representatives: {cells.length}"
  IO.println s!"  distinct raw            : {rawD}"
  IO.println s!"  distinct after nfc      : {nfcD}   (the sweep's syntactic folding)"
  IO.println s!"  distinct after simplify : {simD}   (certified simpset, 237 rules)"
  IO.println s!"  total crank  raw {rawC}   nfc {nfcC}   simplify {simC}"
  let saved := nfcD - simD
  IO.println s!"CELLS THE SWEEP WOULD NOT HAVE TO CLASSIFY: {saved} of {nfcD} ({saved * 100 / (max nfcD 1)}%)"
  -- The soundness check that matters: the pipeline must NOT identify
  -- two representatives.  They are certified pairwise distinct, so a
  -- collision here would be a defect in the simpset, not a discovery.
  let repNF := rhos.map (fun p => keyF (simp p.2))
  let d := repNF.eraseDups.length
  IO.println s!"representatives distinct after simplify: {d}/{n}"
  if d != n then
    IO.println "  *** COLLISION — the simpset identifies certified-distinct classes: DEFECT ***"
    for (a, i) in repNF.zipIdx do
      for (b, j) in repNF.zipIdx do
        if i < j && a == b then
          IO.println s!"    {rhoN i} and {rhoN j} share a normal form"

/-! ## Part A′ — the sweep itself, re-run with the repaired pipeline

Transcribed from `mainSweep` (`wip/closed_frag.lean`) with ONE change:
the normaliser is `Rewrite.simplifyWith Rewrite.fullSetC` instead of
the purely syntactic `nfc`.  Both are sound — every `simplify` step is
a certified `Interd`, so quotienting by it loses no class and cannot
raise `crank` — but the simpset also knows 236 kernel-checked
dictionary cells, so it identifies candidates `nfc` leaves distinct.

The class count is the check that matters: a normaliser that lost a
class would report FEWER than 22, and one that was unsound could
report a class as a member of the wrong one.  Anything other than the
same 22 classes is a defect report. -/

/-- `genFrom` with the certified simpset. -/
def genFromS (reps : Array RepC) (rcap : Nat) : List PLLFormula :=
  let rl := reps.toList.map (·.F)
  let uns :=
    (rl.map fun a => simp (PLLFormula.somehow a)) ++
    (rl.flatMap fun a => rl.flatMap fun b =>
      [simp (PLLFormula.and a b), simp (PLLFormula.or a b),
       simp (PLLFormula.ifThen a b)])
  (uns.filter fun F => crankL F ≤ rcap).eraseDups

def sweepRun : IO Unit := do
  let out ← IO.getStdout
  let t0 ← IO.monoMsNow
  IO.println "=== closed fragment of PCLL, RE-RUN with the certified simpset in place of nfc ==="
  let b4 := battery
  let b5 := framesRooted5.toArray
  let bat := b4 ++ b5
  IO.println s!"confluent battery: {b4.size} frames (ALL well-formed confluent ≤4 worlds) + {b5.size} rooted 5-world canonical orbits"
  -- dictionary seeds outside the cap: reported, not silently dropped
  for (nm, F) in dictSeeds do
    let F' := simp F
    if crankL F' > 7 then
      IO.println s!"SKIP seed {nm} = {pp F'} (crank {crankL F'} > cap 7)"
  out.flush
  let mut reps : Array RepC := #[]
  let mut seen : List String := []
  let mut flags : Array (PLLFormula × Nat × String × String) := #[]
  let mut newAt : Array (Nat × String) := #[]   -- (stratum, rep name)
  for R in [0:8] do
    let mut fresh := true
    let mut rounds := 0
    for _ in [0:6] do
      if fresh then
        fresh := false
        rounds := rounds + 1
        let base : List PLLFormula := if reps.isEmpty then [falsePLL] else []
        let seeds := (dictSeeds.map fun s => simp s.2).filter fun F => crankL F = R
        let cands0 := (base ++ seeds ++ genFromS reps R).eraseDups
        let cands := sortCands (cands0.filter fun F => !(seen.contains (keyF F)))
        for F in cands do
          seen := keyF F :: seen
          let ts ← IO.monoMsNow
          let (cl, vF) := classifyF bat reps F
          let te ← IO.monoMsNow
          let slow := if te - ts > 3000 then s!"  [{te - ts} ms]" else ""
          match cl with
          | .newClass =>
            let nm := s!"r{reps.size}"
            IO.println s!"NEW  {nm} := {pp F}   crank={crankL F}{slow}"
            reps := reps.push ⟨nm, F, crankL F, vF⟩
            newAt := newAt.push (R, nm)
            fresh := true
          | .member c t1 t2 =>
            IO.println s!"MEM  {pp F} ≡ {(reps.getD c default).name} (tiers {t1}/{t2})   crank={crankL F}{slow}"
          | .flagged c d1 d2 =>
            IO.println s!"FLAG {pp F} ?≡ {(reps.getD c default).name} ({d1}/{d2})   crank={crankL F}{slow}"
            flags := flags.push (F, c, d1, d2)
          out.flush
    if fresh then
      IO.println s!"CAP  stratum {R}: round cap 6 hit with new classes still appearing"
    let newHere := (newAt.toList.filter (·.1 = R)).map (·.2)
    IO.println s!"STRATUM {R}: rounds={rounds} classes-so-far={reps.size} new-at-this-crank={newHere} flags-so-far={flags.size}"
    out.flush
  let t1 ← IO.monoMsNow
  IO.println s!"sweep done in {t1 - t0} ms"
  IO.println "RHO-SWEEP-DONE"

/-! ## Part B — the 22 × 22 order matrix -/

inductive Cell where
  | derives (tier : String)
  | separated (fi w : Nat)
  | flag
deriving Repr, DecidableEq

def Cell.glyph : Cell → String
  | .derives _ => "1"
  | .separated _ _ => "."
  | .flag => "?"

/-- Decide `ρi ⊢ ρj`.  Separation first: it is far cheaper, and a
separation is a certificate, so no search is wasted on cells the
battery already settles. -/
def cellOf (bat : Array FinCM) (vecs : Array (Array (Array Bool)))
    (i j : Nat) : Cell :=
  match firstSep bat (vecs.getD i #[]) (vecs.getD j #[]) with
  | some (fi, w) => .separated fi w
  | none =>
      match decidePosT 4 (rhoF i) (rhoF j) with
      | .proved t => .derives s!"tier {t}"
      | _ =>
        match escalate (rhoF i) (rhoF j) with
        | some why => .derives why
        | none => .flag

def matrixRun (pin : Bool) : IO Unit := do
  let out ← IO.getStdout
  let bat := battery ++ framesRooted5.toArray
  IO.println "=== Part B: the 22 × 22 DerivU order matrix ==="
  IO.println s!"battery: {bat.size} mutually confluent frames (all ≤4 worlds + rooted 5-world orbits)"
  IO.println s!"classes: {n}"
  out.flush
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  -- the catalogue's own claim, re-checked: pairwise vector-distinct
  let mut dupes := 0
  for i in [0:n] do
    for j in [0:n] do
      if i < j && vecs.getD i #[] == vecs.getD j #[] then
        dupes := dupes + 1
        IO.println s!"  vector-identical: {rhoN i} and {rhoN j} (catalogue says distinct)"
  IO.println s!"pairwise vector-distinct: {if dupes == 0 then "yes (22 classes confirmed on this battery)" else s!"NO — {dupes} collisions"}"
  out.flush
  let mut rows : Array (Array Cell) := #[]
  let mut flags : List String := []
  let mut pins : List String := []
  for i in [0:n] do
    let mut row : Array Cell := #[]
    for j in [0:n] do
      if i == j then row := row.push (.derives "refl")
      else
        let c := cellOf bat vecs i j
        row := row.push c
        match c with
        | .flag => flags := s!"{rhoN i} ⊢ {rhoN j}" :: flags
        | .separated fi w =>
            if pin then
              pins := pinLine bat fi w (rhoF i) (rhoF j) :: pins
        | _ => pure ()
    rows := rows.push row
    IO.println s!"row {rhoN i}: {String.join ((row.toList.map (·.glyph)))}"
    out.flush
  IO.println ""
  IO.println "matrix (row ⊢ column):  1 = certified derivable, . = certified NOT (countermodel), ? = flag"
  IO.println (s!"        " ++ String.join ((List.range n).map fun j => s!"{j % 10}"))
  for i in [0:n] do
    let r := rows.getD i #[]
    IO.println (s!"{rhoN i}".push ' ' |>.append (String.join (r.toList.map (·.glyph))))
  IO.println ""
  IO.println s!"flags: {flags.length}"
  for f in flags.reverse do IO.println s!"  FLAG {f}"
  -- ── the covering relation ──
  let le := fun i j => match (rows.getD i #[]).getD j .flag with
    | .derives _ => true | _ => false
  IO.println ""
  IO.println "=== the covering relation (Hasse edges: i < j with nothing strictly between) ==="
  let mut edges : List (Nat × Nat) := []
  for i in [0:n] do
    for j in [0:n] do
      if i != j && le i j && !(le j i) then
        -- strict i < j; is it a cover?
        let mid := (List.range n).any fun k =>
          k != i && k != j && le i k && !(le k i) && le k j && !(le j k)
        if !mid then edges := (i, j) :: edges
  for (i, j) in edges.reverse do
    IO.println s!"  {rhoN i}  <  {rhoN j}"
  IO.println s!"cover edges: {edges.length}"
  -- ── where the eight discoveries sit ──
  IO.println ""
  IO.println "=== position of the eight sweep discoveries ==="
  for d in discovered do
    let below := (List.range n).filter fun k => k != d && le k d && !(le d k)
    let above := (List.range n).filter fun k => k != d && le d k && !(le k d)
    let incomp := (List.range n).filter fun k =>
      k != d && !(le k d) && !(le d k)
    IO.println s!"  {rhoN d}: {below.length} below, {above.length} above, {incomp.length} incomparable"
    IO.println s!"      covers   : {String.intercalate ", " ((edges.filter fun e => e.2 == d).map fun e => rhoN e.1)}"
    IO.println s!"      covered by: {String.intercalate ", " ((edges.filter fun e => e.1 == d).map fun e => rhoN e.2)}"
    if !incomp.isEmpty then
      IO.println s!"      incomparable to: {String.intercalate ", " (incomp.map rhoN)}"
  if pin then
    IO.println ""
    IO.println "=== pin lines for the certified non-derivabilities ==="
    for p in pins.reverse do IO.println p
  IO.println "RHO-ORDER-DONE"

/-! ## Part B′ — the two flags, escalated

Repo doctrine: a flag is a frontier marker, re-run at a raised budget
and never dropped.  Both flags matter for the DIAGRAM, not just the
matrix: each is a strict `<` if it resolves positively (the converse
cell is a certified `⊬` in both cases), and in both cases no third
class lies between, so each would add one cover edge. -/

def flagCells : List (Nat × Nat) := [(12, 15), (20, 10)]

def flagRun (budgets : List Nat) : IO Unit := do
  let out ← IO.getStdout
  IO.println "=== the two flags, escalated ==="
  for (i, j) in flagCells do
    IO.println s!"cell {rhoN i} ⊢ {rhoN j}   ({pp (rhoF i)}  ⊢  {pp (rhoF j)})"
    out.flush
    let mut settled := false
    for b in budgets do
      if !settled then
        let t0 ← IO.monoMsNow
        let hit :=
          provedAt b [rhoF i] (rhoF j) ||
          provedDist1 b (rhoF i) (rhoF j) ||
          provedDist2 b (rhoF i) (rhoF j) ||
          (tier1 (rhoF i) (rhoF j)).any
            (fun p => provedAt b [rhoF i, ConfluentU.distF p.1 p.2] (rhoF j)) ||
          provedAt b (rhoF i :: distsOf (tier1 (rhoF i) (rhoF j))) (rhoF j)
        let t1 ← IO.monoMsNow
        IO.println s!"  budget {b}: {if hit then "PROVED" else "not found"}  [{t1 - t0} ms]"
        out.flush
        if hit then
          settled := true
          IO.println s!"  ⇒ {rhoN i} < {rhoN j} is a strict cover edge (converse is a certified ⊬)"
    if !settled then
      IO.println s!"  STILL FLAGGED at budget {budgets.max?.getD 0} — reported, not dropped"
  IO.println "RHO-FLAGS-DONE"

def main (args : List String) : IO Unit := do
  match args with
  | ["sweep"] => sweepRun
  | ["flags"] => flagRun [200000, 500000, 1000000]
  | ["norm"] => normReport
  | ["pin"] => matrixRun true
  | _ => do normReport; IO.println ""; matrixRun false

end RhoOrder

