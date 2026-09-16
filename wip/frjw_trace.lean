/-
# `frjw_trace`: SEARCH-STATE traces of `decideGbuWData`, untrusted evidence

This file is `#eval`-level engineering evidence for the stage-4
explainer.  It TAINTS NOTHING and PROVES NOTHING: the kernel gates of
this development are the `#guard_msgs` axiom pins in
`FRJ/Gbu/W/Saturate.lean` (`decideGbuWData`, `decideGbuW`,
`decidePLL`, `closureDB_closed`, all `[propext, Quot.sound]`).  What is
below is printing machinery, run through the interpreter.  Its printers
are free to leak `Classical.choice`; nothing downstream depends on them.

Two traces are provided, for the two sides of the dichotomy.

* `store` re-runs the saturation of `FRJ/Gbu/W/Saturate.lean` one
  ROUND at a time, from the empty store, printing the rows each round
  adds with the FRJW rule (constructor) that produced them, then the
  root scan `rootDisproof?` and, when it hits, the whole FRJW disproof
  tree.  The loop is `sat`'s own body, spelled out: `db₀ = []`,
  `db_{k+1} = insertNew G (stepNew G db_k) db_k`, stopping when
  `stepNew` is empty.  `roundsEq` below is a `rfl` check that the round
  decomposition used here is verbatim `stepNew`'s definition, and the
  driver additionally compares its final store against `closureDB G`
  sequent by sequent.

* `tree` runs `decideGbuWData G` and prints WHAT IT RETURNED: on `.inl`
  the `Gbu◯` derivation, on `.inr` the FRJW disproof.  Nothing is
  reconstructed by hand; every line comes from a pattern match on the
  returned term.

Gbu◯ nodes carry the search state the well-founded recursion of
`searchW` (`FRJ/Gbu/W/Search.lean`) runs on: the cell `(reg?, Ψ, C)`,
the measure `wgC G reg Ψ C = (unclosed G Ψ, tpC reg C, seqSize Ψ C)`
computed by the repository's own functions, and the guards the searcher
branches on: `cloB Ψ A` at an `⊃`-goal, whether `Ψ ⊆ Ĝ` (the critical
test of the irregular clause), whether `Ψ` has a `◯`-member, and the
context member the rule focused on.

Usage:  `lake env lean --run wip/frjw_trace.lean <unit|circp_p|G2> <store|tree>`
-/
import FRJ.Gbu.W.Saturate

open FRJ FRJ.Gbu FRJ.Gbu.W

namespace FrjwTrace

/-! ## Pretty-printers

Precedence levels: `⊃` 1 (right), `∨` 2, `∧` 3, `◯` 4, atoms 5.
Parentheses only where the level demands them. -/

def ppFAux : Nat → Form → String
  | _, .atom s => s
  | _, .bot => "⊥"
  | p, .and a b =>
      let s := ppFAux 3 a ++ " ∧ " ++ ppFAux 4 b
      if p > 3 then "(" ++ s ++ ")" else s
  | p, .or a b =>
      let s := ppFAux 2 a ++ " ∨ " ++ ppFAux 3 b
      if p > 2 then "(" ++ s ++ ")" else s
  | p, .imp a b =>
      let s := ppFAux 2 a ++ " ⊃ " ++ ppFAux 1 b
      if p > 1 then "(" ++ s ++ ")" else s
  | _, .circ a => "◯" ++ ppFAux 4 a

def ppF (A : Form) : String := ppFAux 0 A

def ppL (l : List Form) : String :=
  "[" ++ String.intercalate ", " (l.map ppF) ++ "]"

def ppTag : Tag → String
  | .barren => "barren"
  | .chain D => s!"chain {ppF D}"
  | .blocked => "blocked"

def ppSeq : WSeq → String
  | .reg t Γ C => s!"{ppTag t} : {ppL Γ} ⇒ {ppF C}"
  | .irr St Th C => s!"{ppL St} ; {ppL Th} → {ppF C}"

def ind (n : Nat) : String := String.ofList (List.replicate n ' ')

/-! ## Rule names: the head constructor of a disproof -/

def ruleNameR {G : Form} {t : Tag} {Γ : List Form} {C : Form} :
    FRJWr G t Γ C → String
  | .axR .. => "axR"
  | .andR1 .. => "andR1"
  | .andR2 .. => "andR2"
  | .impIn .. => "impIn"
  | .circIn .. => "circIn"
  | .joinAt .. => "joinAt"
  | .joinAtP .. => "joinAtP"
  | .joinAtF .. => "joinAtF"
  | .joinOr .. => "joinOr"
  | .joinOrP .. => "joinOrP"
  | .joinOrF .. => "joinOrF"
  | .joinCirc .. => "joinCirc"
  | .joinCircP .. => "joinCircP"

def ruleNameI {G : Form} {St Th : List Form} {C : Form} :
    FRJWi G St Th C → String
  | .axI .. => "axI"
  | .andI1 .. => "andI1"
  | .andI2 .. => "andI2"
  | .orI .. => "orI"
  | .impInI .. => "impInI"
  | .lift .. => "lift"
  | .circNotIn .. => "circNotIn"
  | .axIC .. => "axIC"

def rowRule {G : Form} : ∀ s : WSeq, WDer G s → String
  | .reg _ _ _, d => ruleNameR d
  | .irr _ _ _, d => ruleNameI d

/-! ## The FRJW disproof tree

`rule | sequent`, premises indented.  Every premise of a join family is
printed, labelled by its index. -/

def fLineR (pad : Nat) (nm : String) (t : Tag) (Γ : List Form) (C : Form) :
    String :=
  s!"{ind pad}{nm} | {ppSeq (.reg t Γ C)}"

def fLineI (pad : Nat) (nm : String) (St Th : List Form) (C : Form) : String :=
  s!"{ind pad}{nm} | {ppSeq (.irr St Th C)}"

mutual

def dumpR {G : Form} {t : Tag} {Γ : List Form} {C : Form} (pad : Nat) :
    FRJWr G t Γ C → List String
  | .axR .. => [fLineR pad "axR" t Γ C]
  | .andR1 d .. => fLineR pad "andR1" t Γ C :: dumpR (pad + 2) d
  | .andR2 d .. => fLineR pad "andR2" t Γ C :: dumpR (pad + 2) d
  | .impIn d .. => fLineR pad "impIn" t Γ C :: dumpR (pad + 2) d
  | .circIn d .. => fLineR pad "circIn" t Γ C :: dumpR (pad + 2) d
  | .joinAt (n := n) prem .. =>
      fLineR pad s!"joinAt[irr {n + 1}]" t Γ C ::
        ((List.finRange (n + 1)).map (fun j =>
          (ind (pad + 2) ++ s!"· irr premise j={j.val}") ::
            dumpI (pad + 4) (prem j))).flatten
  | .joinAtF (n := n) prem .. =>
      fLineR pad s!"joinAtF[irr {n + 1}]" t Γ C ::
        ((List.finRange (n + 1)).map (fun j =>
          (ind (pad + 2) ++ s!"· irr premise j={j.val}") ::
            dumpI (pad + 4) (prem j))).flatten
  | .joinOr (n := n) prem .. =>
      fLineR pad s!"joinOr[irr {n + 1}]" t Γ C ::
        ((List.finRange (n + 1)).map (fun j =>
          (ind (pad + 2) ++ s!"· irr premise j={j.val}") ::
            dumpI (pad + 4) (prem j))).flatten
  | .joinOrF (n := n) prem .. =>
      fLineR pad s!"joinOrF[irr {n + 1}]" t Γ C ::
        ((List.finRange (n + 1)).map (fun j =>
          (ind (pad + 2) ++ s!"· irr premise j={j.val}") ::
            dumpI (pad + 4) (prem j))).flatten
  | .joinCirc (n := n) prem .. =>
      fLineR pad s!"joinCirc[irr {n + 1}]" t Γ C ::
        ((List.finRange (n + 1)).map (fun j =>
          (ind (pad + 2) ++ s!"· irr premise j={j.val}") ::
            dumpI (pad + 4) (prem j))).flatten
  | .joinAtP (n := n) (k := k) prem dps .. =>
      fLineR pad s!"joinAtP[irr {n + 1}; promise {k + 1}]" t Γ C ::
        (((List.finRange (n + 1)).map (fun j =>
            (ind (pad + 2) ++ s!"· irr premise j={j.val}") ::
              dumpI (pad + 4) (prem j))).flatten
          ++ ((List.finRange (k + 1)).map (fun i =>
            (ind (pad + 2) ++ s!"· promise premise i={i.val}") ::
              dumpR (pad + 4) (dps i))).flatten)
  | .joinOrP (n := n) (k := k) prem dps .. =>
      fLineR pad s!"joinOrP[irr {n + 1}; promise {k + 1}]" t Γ C ::
        (((List.finRange (n + 1)).map (fun j =>
            (ind (pad + 2) ++ s!"· irr premise j={j.val}") ::
              dumpI (pad + 4) (prem j))).flatten
          ++ ((List.finRange (k + 1)).map (fun i =>
            (ind (pad + 2) ++ s!"· promise premise i={i.val}") ::
              dumpR (pad + 4) (dps i))).flatten)
  | .joinCircP (n := n) (k := k) prem dps .. =>
      fLineR pad s!"joinCircP[irr {n + 1}; promise {k + 1}]" t Γ C ::
        (((List.finRange (n + 1)).map (fun j =>
            (ind (pad + 2) ++ s!"· irr premise j={j.val}") ::
              dumpI (pad + 4) (prem j))).flatten
          ++ ((List.finRange (k + 1)).map (fun i =>
            (ind (pad + 2) ++ s!"· promise premise i={i.val}") ::
              dumpR (pad + 4) (dps i))).flatten)

def dumpI {G : Form} {St Th : List Form} {C : Form} (pad : Nat) :
    FRJWi G St Th C → List String
  | .axI .. => [fLineI pad "axI" St Th C]
  | .axIC .. => [fLineI pad "axIC" St Th C]
  | .andI1 d .. => fLineI pad "andI1" St Th C :: dumpI (pad + 2) d
  | .andI2 d .. => fLineI pad "andI2" St Th C :: dumpI (pad + 2) d
  | .orI d₁ d₂ .. =>
      fLineI pad "orI" St Th C ::
        (dumpI (pad + 2) d₁ ++ dumpI (pad + 2) d₂)
  | .impInI d .. => fLineI pad "impInI" St Th C :: dumpI (pad + 2) d
  | .lift d .. => fLineI pad "lift" St Th C :: dumpR (pad + 2) d
  | .circNotIn d .. => fLineI pad "circNotIn" St Th C :: dumpR (pad + 2) d

end

/-! ## The Gbu◯ derivation tree, with the search state at every node -/

def cellStr (reg : Bool) (Ψ : List Form) (C : Form) : String :=
  if reg then s!"(reg, {ppL Ψ}, {ppF C})" else s!"(irr, {ppL Ψ}, {ppF C})"

def wgStr (G : Form) (reg : Bool) (Ψ : List Form) (C : Form) : String :=
  let w := wgC G reg Ψ C
  s!"wgC=({w.1}, {w.2.1}, {w.2.2})"

/-- The guards the searcher branches on, at this cell. -/
def guardStr (G : Form) (Ψ : List Form) (C : Form) (focus : Option Form) :
    String :=
  let cl := match C with
    | .imp A _ => s!"cloB Ψ {ppF A}={cloB Ψ A}"
    | _ => "cloB=n/a"
  let hat := s!"Ψ⊆Ĝ={Ψ.all (fun X => decide (X ∈ gHat G))}"
  let cir := s!"◯∈Ψ={Ψ.any Form.isCirc}"
  let foc := match focus with
    | some A => s!"focus={ppF A}"
    | none => "focus=-"
  s!"{cl}  {hat}  {cir}  {foc}"

def gLine (G : Form) (pad : Nat) (nm : String) (reg : Bool) (Ψ : List Form)
    (C : Form) (focus : Option Form) : String :=
  s!"{ind pad}{nm} | {cellStr reg Ψ C} | {wgStr G reg Ψ C} | {guardStr G Ψ C focus}"

mutual

def dumpGR {G : Form} {Γ : List Form} {C : Form} (pad : Nat) :
    GbuRC G Γ C → List String
  | .ax A .. => [gLine G pad "ax" true Γ C (some A)]
  | .lbot .. => [gLine G pad "lbot" true Γ C (some .bot)]
  | .landL (A := A) (B := B) d .. =>
      gLine G pad "landL" true Γ C (some (.and A B)) :: dumpGR (pad + 2) d
  | .randR d₁ d₂ =>
      gLine G pad "randR" true Γ C none ::
        (dumpGR (pad + 2) d₁ ++ dumpGR (pad + 2) d₂)
  | .lorL (A := A) (B := B) d₁ d₂ .. =>
      gLine G pad "lorL" true Γ C (some (.or A B)) ::
        (dumpGR (pad + 2) d₁ ++ dumpGR (pad + 2) d₂)
  | .rorR1 d => gLine G pad "rorR1" true Γ C none :: dumpGI (pad + 2) d
  | .rorR2 d => gLine G pad "rorR2" true Γ C none :: dumpGI (pad + 2) d
  | .limpL (A := A) (B := B) d₁ d₂ .. =>
      gLine G pad "limpL" true Γ C (some (.imp A B)) ::
        (dumpGI (pad + 2) d₁ ++ dumpGR (pad + 2) d₂)
  | .rimpI d .. => gLine G pad "rimpI" true Γ C none :: dumpGR (pad + 2) d
  | .rimpNI d .. => gLine G pad "rimpNI" true Γ C none :: dumpGR (pad + 2) d
  | .lcirc (Z := Z) d .. =>
      gLine G pad "lcirc" true Γ C (some (.circ Z)) :: dumpGR (pad + 2) d
  | .rcirc d .. => gLine G pad "rcirc" true Γ C none :: dumpGI (pad + 2) d

def dumpGI {G : Form} {Γ : List Form} {C : Form} (pad : Nat) :
    GbuIC G Γ C → List String
  | .ax A .. => [gLine G pad "axI" false Γ C (some A)]
  | .randI d₁ d₂ =>
      gLine G pad "randI" false Γ C none ::
        (dumpGI (pad + 2) d₁ ++ dumpGI (pad + 2) d₂)
  | .rorI1 d => gLine G pad "rorI1" false Γ C none :: dumpGI (pad + 2) d
  | .rorI2 d => gLine G pad "rorI2" false Γ C none :: dumpGI (pad + 2) d
  | .rimpII d .. => gLine G pad "rimpII" false Γ C none :: dumpGI (pad + 2) d
  | .rimpNII d .. => gLine G pad "rimpNII" false Γ C none :: dumpGR (pad + 2) d
  | .lcircI (Z := Z) d .. =>
      gLine G pad "lcircI" false Γ C (some (.circ Z)) :: dumpGI (pad + 2) d
  | .limpLI (A := A) (B := B) d₁ d₂ .. =>
      gLine G pad "limpLI" false Γ C (some (.imp A B)) ::
        (dumpGI (pad + 2) d₁ ++ dumpGI (pad + 2) d₂)
  | .lbotI .. => [gLine G pad "lbotI" false Γ C (some .bot)]
  | .landLI (A := A) (B := B) d .. =>
      gLine G pad "landLI" false Γ C (some (.and A B)) :: dumpGI (pad + 2) d
  | .lorLI (A := A) (B := B) d₁ d₂ .. =>
      gLine G pad "lorLI" false Γ C (some (.or A B)) ::
        (dumpGI (pad + 2) d₁ ++ dumpGI (pad + 2) d₂)
  | .rcircI d .. => gLine G pad "rcircI" false Γ C none :: dumpGI (pad + 2) d

end

/-! ## The round decomposition is the engine's own

`stepNew` is `stepAll` filtered by key freshness; the driver below
spells the filter out so that one `stepAll` serves both the emitted
count and the fresh rows.  This is a kernel check that the spelling is
verbatim. -/

theorem roundsEq (G : Form) (db : List (WRow G)) :
    stepNew G db
      = (stepAll G db).filter (fun r => decide (keyOf G r ∉ keysOf G db)) :=
  rfl

/-! ## Drivers -/

def cells : List (String × Form) := [
  ("unit",    .imp (.atom "p") (.circ (.atom "p"))),
  ("circp_p", .imp (.circ (.atom "p")) (.atom "p")),
  ("G2",      .imp (.circ (.atom "p"))
                (.and (.circ (.atom "p")) (.circ (.atom "p"))))
]

def header (name : String) (G : Form) : IO Unit := do
  IO.println s!"cell     {name}"
  IO.println s!"G        {ppF G}"
  IO.println s!"Sf^L G   {ppL (sfL G)}"
  IO.println s!"Sf^R G   {ppL (sfR G)}"
  IO.println s!"Ĝ        {ppL (gHat G)}"
  IO.println ""

/-- One round of the saturation, printed; the recursion is `sat`'s body. -/
def roundsLoop (G : Form) : Nat → Nat → List (WRow G) → IO (List (WRow G))
  | 0, k, db => do
      IO.println s!"round {k}: FUEL EXHAUSTED (no fixpoint reached): FLAG"
      return db
  | fuel + 1, k, db => do
      let all := stepAll G db
      let new := all.filter (fun r => decide (keyOf G r ∉ keysOf G db))
      if new.isEmpty then
        IO.println s!"round {k}: stepAll emitted {all.length} rows, 0 fresh: FIXPOINT"
        return db
      else
        let db' := insertNew G new db
        let added := (db'.take (db'.length - db.length)).reverse
        IO.println s!"round {k}: stepAll emitted {all.length} rows, {new.length} fresh, {added.length} stored"
        for r in added do
          IO.println s!"    {rowRule r.s r.d}  |  {ppSeq r.s}"
        IO.println s!"    store now {db'.length} rows"
        roundsLoop G fuel (k + 1) db'

def runStore (name : String) (G : Form) : IO Unit := do
  header name G
  IO.println "=== saturation, round by round (db₀ = [], db_{k+1} = insertNew G (stepNew G db_k) db_k) ==="
  let db ← roundsLoop G 200 1 []
  IO.println ""
  IO.println s!"final store: {db.length} rows"
  let ref := closureDB G
  let same := (db.map (fun r => ppSeq r.s)) == (ref.map (fun r => ppSeq r.s))
  IO.println s!"closureDB G: {ref.length} rows; sequent lists identical: {same}"
  IO.println ""
  IO.println "=== root scan: rootDisproof? (closureDB G) ==="
  match rootDisproof? db with
  | none =>
      IO.println "rootDisproof? = none: no regular root row with goal G;"
      IO.println "  decideOfStore therefore runs searchW and returns a Gbu◯ derivation."
  | some ⟨t, Γ, d⟩ =>
      IO.println s!"rootDisproof? = some: tag {ppTag t}, |Γ|={Γ.length}, Γ = {ppL Γ}"
      IO.println s!"head rule: {ruleNameR d}"
      IO.println ""
      IO.println "=== the FRJW disproof of the root, whole tree ==="
      for l in dumpR 0 d do IO.println l

def runTree (name : String) (G : Form) : IO Unit := do
  header name G
  IO.println "=== decideGbuWData G ==="
  match decideGbuWData G with
  | .inl d =>
      IO.println ".inl: a Gbu◯ derivation of [] ⇒ G.  PROOF side."
      IO.println "node format: rule | cell (reg?, Ψ, C) | wgC=(unclosed, tpC, seqSize) | guards"
      IO.println ""
      for l in dumpGR 0 d do IO.println l
  | .inr ⟨t, Γ, d⟩ =>
      IO.println s!".inr: an FRJW disproof of G.  DISPROOF side.  tag {ppTag t}, |Γ|={Γ.length}"
      IO.println ""
      for l in dumpR 0 d do IO.println l

def main (args : List String) : IO Unit := do
  match args with
  | [name, mode] =>
      match cells.find? (fun c => c.1 == name) with
      | none => IO.println s!"unknown cell {name}"
      | some (n, G) =>
          match mode with
          | "store" => runStore n G
          | "tree" => runTree n G
          | _ => IO.println s!"unknown mode {mode} (store | tree)"
  | _ => IO.println "usage: --run wip/frjw_trace.lean <unit|circp_p|G2> <store|tree>"

end FrjwTrace

def main (args : List String) : IO Unit := FrjwTrace.main args
