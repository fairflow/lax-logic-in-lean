/-
# RNDB exporter — spike S1 of the F0 database audit (2026-10-21)

READ-ONLY.  Walks `RNDB.allEntries` source list by source list, the
frontier lists and the ρ/q representatives, and writes JSON Lines.
Nothing under `RNDB/`, `Rewrite/`, `wip/` or `LaxLogic/` is changed; this
module only imports them.

Rows (`kind` field):

* `entry` — one per element of `allEntries`, in order: id, source list,
  position, relation, both sides printed raw and through `Rewrite.canon`,
  formula sizes, scope (named `rhoScope` or `RNReps.reps` when it equals
  one of them, with its length), `Claim.wellScopedB`, and the evidence
  (kind, engine, worlds, parents, rule).
* `example_entry` — the four worked entries of `RNDB/Examples.lean`,
  which are NOT in `allEntries`.
* `frontier` — every claim of `frontierOrder`, `frontier79` and
  `exampleFrontier`.
* `rep` — the ρ representatives (`LaxLogic/RN/Rho.lean`) and the q
  representatives (`LaxLogic/RN/Reps.lean`), each with the index of its
  syntactic twin in the other family, if any.
* `meta` — counts, and the two self-checks below.

Printing.  `pp` writes the library notation (◯ ∧ ∨ ↠ ⊥, `⊤` for `⊥ ↠ ⊥`,
`¬A` for `A ↠ ⊥`; `∧` binds tighter than `∨`, `∨` tighter than `↠`, and
`↠` associates to the right) and parenthesises every child whose
precedence does not determine the parse, so the printed string is an
injective function of the syntax tree.  Self-check 1 tests this on every
formula printed, against `Rewrite.keyF` (an injective prefix code): a
printed string that arises from two different trees is reported in the
`meta` row.  Self-check 2 lists the DISTINCT formulas on which
`Rewrite.canon` is not idempotent (`canon (canon φ) ≠ canon φ`), which
matters for its use as a key.

Gate watch: `rndbexport --gate-watch` runs self-check 1 with a
deliberately lossy printer (`ppFlat`, no parentheses) and requires it to
report collisions, and `pp` to report none.

Run (bounded, built binary, never a rebuild under the deadline):

    lake build rndbexport
    gtimeout 300 .lake/build/bin/rndbexport _out/rndb-export.jsonl
    gtimeout 300 .lake/build/bin/rndbexport --gate-watch
-/
import RNDB.DB
import RNDB.Frontier79
import RNDB.Examples
import Rewrite.Canon
import LaxLogic.RN.Rho
import Lean.Data.Json
import Std.Data.HashMap

open Lean (Json toJson)

namespace RNDBExport

/-! ## Printing -/

/-- Binding strength: 0 = `↠`, 1 = `∨`, 2 = `∧`, 3 = prefix and atoms.
`⊤` and `¬A` are prefix-strength. -/
def prec : PLLFormula → Nat
  | .ifThen .falsePLL .falsePLL => 3
  | .ifThen _ .falsePLL => 3
  | .ifThen _ _ => 0
  | .or _ _ => 1
  | .and _ _ => 2
  | _ => 3

def par (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

/-- Injective printer in the library notation.  `↠` associates to the
right; a child of `∧` or `∨` of equal or weaker strength is always
parenthesised, so `(a ∧ b) ∧ c` and `a ∧ (b ∧ c)` print differently. -/
def pp : PLLFormula → String
  | .prop s => s
  | .falsePLL => "⊥"
  | .ifThen .falsePLL .falsePLL => "⊤"
  | .ifThen a .falsePLL => "¬" ++ par (prec a < 3) (pp a)
  | .ifThen a b => par (prec a == 0) (pp a) ++ " ↠ " ++ pp b
  | .or a b => par (prec a ≤ 1) (pp a) ++ " ∨ " ++ par (prec b ≤ 1) (pp b)
  | .and a b => par (prec a ≤ 2) (pp a) ++ " ∧ " ++ par (prec b ≤ 2) (pp b)
  | .somehow a => "◯" ++ par (prec a < 3) (pp a)

/-- A deliberately LOSSY printer (no parentheses), used only by
`--gate-watch` to watch the injectivity check fail. -/
def ppFlat : PLLFormula → String
  | .prop s => s
  | .falsePLL => "⊥"
  | .ifThen a b => ppFlat a ++ " ↠ " ++ ppFlat b
  | .or a b => ppFlat a ++ " ∨ " ++ ppFlat b
  | .and a b => ppFlat a ++ " ∧ " ++ ppFlat b
  | .somehow a => "◯" ++ ppFlat a

/-- Number of constructor nodes. -/
def size : PLLFormula → Nat
  | .and a b | .or a b | .ifThen a b => size a + size b + 1
  | .somehow a => size a + 1
  | _ => 1

/-- How many formulas of `fs` print to a string already produced by a
DIFFERENT tree (trees compared by `Rewrite.keyF`). -/
def collisions (pr : PLLFormula → String) (fs : List PLLFormula) : Nat := Id.run do
  let mut seen : Std.HashMap String String := {}
  let mut n := 0
  for φ in fs do
    let s := pr φ
    let k := Rewrite.keyF φ
    match seen.get? s with
    | some k' => if k' != k then n := n + 1
    | none => seen := seen.insert s k
  return n

/-! ## Field encoders -/

def js (s : String) : Json := Json.str s

def relName : RNDB.Rel → String
  | .le => "le"
  | .interd => "interd"
  | .nle => "nle"

def engineName : RNDB.Engine → String
  | .finCM => "finCM"
  | .frj => "frj"
  | .twoSided => "twoSided"
  | .frjv => "frjv"
  | .hand => "hand"

def ruleName : RNDB.DerivRule → String
  | .trans => "trans"
  | .symm => "symm"

/-- The scope is stored BY VALUE in each claim; it is named here only
when it equals one of the two shared lists as they stand today. -/
def scopeName : Option (List PLLFormula) → String
  | none => "none"
  | some s =>
      if s == RNDB.rhoScope then "rhoScope"
      else if s == RNReps.reps then "RNReps.reps"
      else s!"other{s.length}"

def scopeSize : Option (List PLLFormula) → Json
  | none => Json.null
  | some s => toJson s.length

def evFields : RNDB.Evidence → List (String × Json)
  | .proof e =>
      [("ev", js "proof"), ("engine", js (engineName e)), ("worlds", Json.null),
       ("parents", Json.arr #[]), ("rule", Json.null)]
  | .countermodel e w =>
      [("ev", js "countermodel"), ("engine", js (engineName e)), ("worlds", toJson w),
       ("parents", Json.arr #[]), ("rule", Json.null)]
  | .derived ps r =>
      [("ev", js "derived"), ("engine", Json.null), ("worlds", Json.null),
       ("parents", Json.arr (ps.map Json.str).toArray), ("rule", js (ruleName r))]

/-- The four formula fields of one side of a claim. -/
def sideFields (pfx : String) (φ : PLLFormula) : List (String × Json) :=
  let c := Rewrite.canon φ
  [(pfx, js (pp φ)), (pfx ++ "_canon", js (pp c)),
   (pfx ++ "_size", toJson (size φ)), (pfx ++ "_canon_size", toJson (size c))]

def claimFields (c : RNDB.Claim) : List (String × Json) :=
  [("rel", js (relName c.rel))] ++ sideFields "lhs" c.lhs ++ sideFields "rhs" c.rhs ++
  [("scope", js (scopeName c.scope)), ("scope_size", scopeSize c.scope),
   ("well_scoped", toJson c.wellScopedB)]

/-! ## The sources, in `allEntries` order -/

def sources : List (String × List RNDB.Entry) :=
  [ ("rho", RNDB.rhoEntries), ("dictR1", RNDB.dictEntriesR1),
    ("dictR2", RNDB.dictEntriesR2), ("frjCert", RNDB.frjCertEntries),
    ("derived", RNDB.derivedEntries), ("esc", RNDB.escEntries),
    ("order", RNDB.orderEntries), ("sep", RNDB.sepEntries) ]

def frontiers : List (String × List RNDB.Claim) :=
  [ ("frontierOrder", RNDB.frontierOrder), ("frontier79", RNDB.frontier79),
    ("exampleFrontier", RNDB.exampleFrontier) ]

/-! ## Self-checks over every printed formula -/

structure Checks where
  /-- printed string ↦ `keyF` of the tree it came from -/
  seen : Std.HashMap String String := {}
  ppCollisions : Array String := #[]
  canonNonIdem : Nat := 0
  canonNonIdemEx : Array String := #[]
  formulas : Nat := 0

def Checks.note (ch : Checks) (φ : PLLFormula) : Checks := Id.run do
  let mut ch := ch
  let fresh := !(ch.seen.contains (pp φ))
  for ψ in [φ, Rewrite.canon φ] do
    let s := pp ψ
    let k := Rewrite.keyF ψ
    match ch.seen.get? s with
    | some k' =>
        if k' != k && ch.ppCollisions.size < 20 then
          ch := { ch with ppCollisions := ch.ppCollisions.push s }
    | none => ch := { ch with seen := ch.seen.insert s k, formulas := ch.formulas + 1 }
  let c := Rewrite.canon φ
  let cc := Rewrite.canon c
  if fresh && cc != c then
    ch := { ch with canonNonIdem := ch.canonNonIdem + 1 }
    if ch.canonNonIdemEx.size < 20 then
      ch := { ch with canonNonIdemEx :=
        ch.canonNonIdemEx.push (pp φ ++ "  =canon=>  " ++ pp c ++ "  =canon=>  " ++ pp cc) }
  return ch

/-! ## Main -/

def row (fields : List (String × Json)) : String := (Json.mkObj fields).compress

def gateWatch : IO UInt32 := do
  let fs := RNDB.allEntries.flatMap fun e =>
    [e.claim.lhs, e.claim.rhs, Rewrite.canon e.claim.lhs, Rewrite.canon e.claim.rhs]
  let bad := collisions ppFlat fs
  let good := collisions pp fs
  IO.println s!"gate watch over {fs.length} printed formulas: lossy printer collisions {bad} (must be > 0); pp collisions {good} (must be 0)"
  return (if bad > 0 && good == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if args.contains "--gate-watch" then return (← gateWatch)
  let path := args.headD "_out/rndb-export.jsonl"
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  let mut ch : Checks := {}
  let mut pos := 0
  let mut srcCounts : Array (String × Nat) := #[]
  let mut walkedIds : Array String := #[]
  -- entries
  for (src, es) in sources do
    srcCounts := srcCounts.push (src, es.length)
    for e in es do
      h.putStrLn <| row <|
        [("kind", js "entry"), ("id", js e.id), ("source", js src), ("pos", toJson pos)] ++
        claimFields e.claim ++ evFields e.ev
      ch := (ch.note e.claim.lhs).note e.claim.rhs
      walkedIds := walkedIds.push e.id
      pos := pos + 1
  -- the walk must BE allEntries: same length, same ids, same order
  let allIds := (RNDB.allEntries.map (·.id)).toArray
  let walkOk := allIds == walkedIds
  -- worked examples (not in allEntries)
  for e in RNDB.exampleEntries do
    h.putStrLn <| row <|
      [("kind", js "example_entry"), ("id", js e.id), ("source", js "examples")] ++
      claimFields e.claim ++ evFields e.ev
    ch := (ch.note e.claim.lhs).note e.claim.rhs
  -- frontier lists
  for (name, fr) in frontiers do
    let mut i := 0
    for c in fr do
      h.putStrLn <| row <|
        [("kind", js "frontier"), ("list", js name), ("index", toJson i)] ++ claimFields c
      ch := (ch.note c.lhs).note c.rhs
      i := i + 1
  -- representatives and the ρ ↔ q cross-map (syntactic identity)
  for i in List.range RhoOrder.n do
    let φ := RhoOrder.rhoF i
    let q := RNReps.reps.findIdx? (· == φ)
    h.putStrLn <| row
      [("kind", js "rep"), ("family", js "rho"), ("index", toJson i),
       ("name", js (RhoOrder.rhoN i)), ("formula", js (pp φ)),
       ("canon", js (pp (Rewrite.canon φ))), ("size", toJson (size φ)), ("twin", toJson q)]
    ch := ch.note φ
  for k in List.range RNReps.reps.length do
    let φ := RNReps.reps.getD k .falsePLL
    let r := (List.range RhoOrder.n).find? (fun i => RhoOrder.rhoF i == φ)
    h.putStrLn <| row
      [("kind", js "rep"), ("family", js "q"), ("index", toJson k),
       ("name", js s!"q{k}"), ("formula", js (pp φ)),
       ("canon", js (pp (Rewrite.canon φ))), ("size", toJson (size φ)), ("twin", toJson r)]
    ch := ch.note φ
  -- meta
  h.putStrLn <| row
    [("kind", js "meta"),
     ("allEntries_length", toJson RNDB.allEntries.length),
     ("walk_equals_allEntries", toJson walkOk),
     ("source_counts", Json.mkObj (srcCounts.toList.map fun (s, n) => (s, toJson n))),
     ("rho_count", toJson RhoOrder.n), ("q_count", toJson RNReps.reps.length),
     ("distinct_printed_formulas", toJson ch.formulas),
     ("pp_collisions", Json.arr (ch.ppCollisions.map Json.str)),
     ("canon_non_idempotent_distinct", toJson ch.canonNonIdem),
     ("canon_non_idempotent_examples", Json.arr (ch.canonNonIdemEx.map Json.str))]
  h.flush
  IO.println s!"rndbexport: {pos} entries ({RNDB.allEntries.length} in allEntries, walk ok = {walkOk}); {ch.formulas} distinct printed formulas; pp collisions {ch.ppCollisions.size}; canon non-idempotent on {ch.canonNonIdem} distinct formulas; wrote {path}"
  return (if walkOk && ch.ppCollisions.isEmpty then 0 else 1)

end RNDBExport

def main (args : List String) : IO UInt32 := RNDBExport.main args
