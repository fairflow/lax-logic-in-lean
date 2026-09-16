/-
COPY, not a move.  The `wip/` original is left in place unchanged so that
other branches still compile; this file is the maintained version.  Do not
edit the `wip/` twin — it is stale by construction (2026-08-21).
-/
/-
# `frjcert` — sequent in, Lean-checked certificate out, ONE command

    lake exe frjcert "q10 ⊢ q10 ∧ q13" --out docs/cert

Takes the sequent claimed underivable, runs the FRJ(◯) forward-saturation
search on it, keeps the countermodel the derivation builds, minimises it,
writes a self-contained Lean certificate, RUNS LEAN ON THAT FILE, and
writes the SVG.  Nothing is copied by hand and nothing is reported as
checked that this process did not itself check: the verdict line carries
Lean's own exit code and the `#print axioms` output it produced.

Syntax accepted:  `⊥ ⊤ ¬ ◯ ∧ ∨ ⊃ ( ) ,` with ASCII fallbacks
`~ # & | -> |-`, identifiers `q0 … q14` for the RN(◯,{}) representatives
and any other identifier as a propositional atom.  The hypothesis list is
comma-separated and the turnstile is `⊢`.
-/
import FRJ.Search.Fast
import FRJ.Search.Pin
import LaxLogic.RN.Reps

open FRJ

namespace FrjCert

/-! ## 1. The sequent parser -/

inductive Tok where
  | lp | rp | comma | turn
  | bot | top | neg | box | conj | disj | imp
  | id (s : String)
deriving Repr, DecidableEq

private def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

partial def tokenize (cs : List Char) : Except String (List Tok) :=
  match cs with
  | [] => .ok []
  | c :: rest =>
    if c == ' ' || c == '\t' then tokenize rest
    else if c == '(' then (tokenize rest).map (.lp :: ·)
    else if c == ')' then (tokenize rest).map (.rp :: ·)
    else if c == ',' then (tokenize rest).map (.comma :: ·)
    else if c == '⊢' then (tokenize rest).map (.turn :: ·)
    else if c == '⊥' then (tokenize rest).map (.bot :: ·)
    else if c == '⊤' then (tokenize rest).map (.top :: ·)
    else if c == '¬' || c == '~' then (tokenize rest).map (.neg :: ·)
    else if c == '◯' || c == '#' then (tokenize rest).map (.box :: ·)
    else if c == '∧' || c == '&' then (tokenize rest).map (.conj :: ·)
    else if c == '⊃' || c == '→' then (tokenize rest).map (.imp :: ·)
    else if c == '∨' then (tokenize rest).map (.disj :: ·)
    else if c == '|' then
      match rest with
      | '-' :: r => (tokenize r).map (.turn :: ·)
      | _ => (tokenize rest).map (.disj :: ·)
    else if c == '-' then
      match rest with
      | '>' :: r => (tokenize r).map (.imp :: ·)
      | _ => .error "stray '-'"
    else if isIdChar c then
      let name := String.ofList (c :: rest.takeWhile isIdChar)
      (tokenize (rest.dropWhile isIdChar)).map (.id name :: ·)
    else .error s!"unexpected character '{c}'"

/-- Every `q<k>` token in the input must name a real representative.
Before this check, `q99` resolved SILENTLY to a fresh propositional
ATOM — so a typo became a new variable and the search then succeeded
trivially, reporting a countermodel for a formula nobody asked about. -/
def badQIndex (src : String) : Option String := Id.run do
  let cs := src.toList
  let mut i := 0
  let mut out : Option String := none
  let arr := cs.toArray
  while i < arr.size do
    if arr[i]! == 'q' && (i == 0 || !(arr[i-1]!.isAlphanum)) then
      let mut j := i + 1
      let mut ds := ""
      while j < arr.size && arr[j]!.isDigit do
        ds := ds.push arr[j]!; j := j + 1
      if ds != "" then
        match ds.toNat? with
        | some k => if k ≥ RNReps.reps.length && out.isNone then
                      out := some s!"q{ds}"
        | none => pure ()
      i := j
    else i := i + 1
  return out

/-- `q0 … q15` name the RN(◯,{}) representatives; anything else is an atom.
Guarded by `badQIndex` at the entry point. -/
def resolve (s : String) : Form :=
  if s.startsWith "q" then
    match (s.drop 1).toNat? with
    | some k => match RNReps.reps[k]? with
                | some φ => ofPLL φ
                | none => .atom s
    | none => .atom s
  else .atom s

mutual

partial def pImp (ts : List Tok) : Except String (Form × List Tok) := do
  let (a, ts) ← pDisj ts
  match ts with
  | .imp :: r => let (b, r) ← pImp r; pure (.imp a b, r)
  | _ => pure (a, ts)

partial def pDisj (ts : List Tok) : Except String (Form × List Tok) := do
  let (a, ts) ← pConj ts
  match ts with
  | .disj :: r => let (b, r) ← pDisj r; pure (.or a b, r)
  | _ => pure (a, ts)

partial def pConj (ts : List Tok) : Except String (Form × List Tok) := do
  let (a, ts) ← pUn ts
  match ts with
  | .conj :: r => let (b, r) ← pConj r; pure (.and a b, r)
  | _ => pure (a, ts)

partial def pUn (ts : List Tok) : Except String (Form × List Tok) := do
  match ts with
  | .neg :: r => let (a, r) ← pUn r; pure (.imp a .bot, r)
  | .box :: r => let (a, r) ← pUn r; pure (.circ a, r)
  | .bot :: r => pure (.bot, r)
  | .top :: r => pure (.imp .bot .bot, r)
  | .id s :: r => pure (resolve s, r)
  | .lp :: r => do
      let (a, r) ← pImp r
      match r with
      | .rp :: r' => pure (a, r')
      | _ => .error "expected ')'"
  | _ => .error "expected a formula"

end

partial def parseHyps (l : List Tok) : Except String (List Form) :=
  if l.isEmpty then .ok [] else do
    let (a, r) ← pImp l
    match r with
    | [] => pure [a]
    | .comma :: r' => (parseHyps r').map (a :: ·)
    | _ => .error "expected ',' in the hypothesis list"

/-- `Γ ⊢ φ`, with `Γ` possibly empty and the turnstile optional. -/
def parseSequent (s : String) : Except String (List Form × Form) := do
  let ts ← tokenize s.toList
  let (before, after) :=
    match ts.idxOf? .turn with
    | some i => (ts.take i, ts.drop (i+1))
    | none => ([], ts)
  let goal ← do
    let (g, r) ← pImp after
    if r.isEmpty then pure g else .error "trailing tokens after the goal"
  let Γ ← parseHyps before
  pure (Γ, goal)

/-! ## 2. Rendering -/

def ppF : Form → String
  | .atom p => p
  | .bot => "⊥"
  | .and a b => s!"({ppF a} ∧ {ppF b})"
  | .or a b => s!"({ppF a} ∨ {ppF b})"
  | .imp .bot .bot => "⊤"
  | .imp a .bot => s!"¬{ppF a}"
  | .imp a b => s!"({ppF a} ⊃ {ppF b})"
  | .circ a => s!"◯{ppF a}"

/-- Fully expanded source: every constructor named in full.  Dot notation
is unqualified: the generated file does `open PLLFormula`, which keeps the
term legible and lets it be read against the docstring as a cross-check on
both.  (Dot-chaining was tried and rejected — `.falsePLL.somehow` is not a
legal chain, caught by this tool's own Lean run.) -/
def srcPLL : Form → String
  | .atom p => s!"(prop \"{p}\")"
  | .bot => "falsePLL"
  | .and a b => s!"(and {srcPLL a} {srcPLL b})"
  | .or a b => s!"(or {srcPLL a} {srcPLL b})"
  | .imp a b => s!"(ifThen {srcPLL a} {srcPLL b})"
  | .circ a => s!"(somehow {srcPLL a})"

/-- Source that prefers the dictionary NAME wherever a subformula is one
of the RN(◯,{}) representatives.  This is what theorem 1 is stated in. -/
def srcNamed (A : Form) : String :=
  match (List.range RNReps.reps.length).find?
          (fun k => match RNReps.reps[k]? with
                    | some φ => decide (ofPLL φ = A)
                    | none => false) with
  | some k => s!"q{k}"
  | none =>
    match A with
    | .atom p => s!"(prop \"{p}\")"
    | .bot => "falsePLL"
    | .and a b => s!"(and {srcNamed a} {srcNamed b})"
    | .or a b => s!"(or {srcNamed a} {srcNamed b})"
    | .imp a b => s!"(ifThen {srcNamed a} {srcNamed b})"
    | .circ a => s!"(somehow {srcNamed a})"

def subs : Form → List Form
  | .atom p => [.atom p]
  | .bot => [.bot]
  | .and a b => .and a b :: (subs a ++ subs b)
  | .or a b => .or a b :: (subs a ++ subs b)
  | .imp a b => .imp a b :: (subs a ++ subs b)
  | .circ a => .circ a :: subs a

/-! ## 3. The SVG, with the vertices labelled by what they force -/

def forcesAt (T : Search.Tab) (w : Nat) (A : Form) : Bool :=
  match T.toKripke? with
  | none => false
  | some K => match K.elems[w]? with
              | none => false
              | some a => decide (K.force a A)

/-- Every subformula of the goal the world forces — the vertex label. -/
def labelOf (T : Search.Tab) (G : Form) (w : Nat) : String :=
  let ss := (subs G).eraseDups
  let held := ss.filter (fun A => forcesAt T w A)
  if T.falT.getD w false then "⊥ (fallible)"
  else if held.isEmpty then "⊮ every subformula"
  else String.intercalate ", " (held.map ppF)

/-- Transitive reduction of `≤`, so the picture is a Hasse diagram. -/
def hasse (T : Search.Tab) : List (Nat × Nat) :=
  let le := fun a b => (T.leT.getD a []).getD b false
  (List.range T.n).flatMap fun a =>
    (List.range T.n).filterMap fun b =>
      if a != b && le a b &&
         !((List.range T.n).any (fun c => c != a && c != b && le a c && le c b))
      then some (a, b) else none

/-- Layer = the longest `≤`-chain below the world. -/
def layerOf (T : Search.Tab) (w : Nat) : Nat :=
  let le := fun a b => (T.leT.getD a []).getD b false
  ((List.range T.n).filter (fun c => c != w && le c w)).length

def toSvg (T : Search.Tab) (G : Form) : String :=
  let rowH := 110
  let colW := 460
  let layers := (List.range T.n).map (layerOf T)
  let maxL := layers.foldl Nat.max 0
  let posOf : Nat → Nat × Nat := fun w =>
    let l := layers.getD w 0
    let peers := (List.range T.n).filter (fun v => layers.getD v 0 == l)
    let k := peers.idxOf w
    (60 + k * colW, 60 + (maxL - l) * rowH)
  -- wide enough for the longest label at its own x, so nothing is clipped
  let width := (List.range T.n).foldl (fun acc w =>
      Nat.max acc ((posOf w).1 + 30 + 7 * (labelOf T G w).length)) 400
  let height := 140 + rowH * maxL
  let edge := fun (a b : Nat) (dashed : Bool) =>
    let (x1, y1) := posOf a
    let (x2, y2) := posOf b
    s!"<line x1=\"{x1}\" y1=\"{y1}\" x2=\"{x2}\" y2=\"{y2}\" stroke=\"{if dashed then "#2266cc" else "#999"}\" stroke-width=\"{if dashed then 2 else 1}\"{if dashed then " stroke-dasharray=\"6,4\"" else ""} />"
  let les := (hasse T).map (fun p => edge p.1 p.2 false)
  let rms := ((List.range T.n).flatMap fun a =>
      (List.range T.n).filterMap fun b =>
        if a != b && (T.rmT.getD a []).getD b false then some (a, b) else none).map
      (fun p => edge p.1 p.2 true)
  let nodes := (List.range T.n).map fun w =>
    let (x, y) := posOf w
    let isRoot := w == T.root
    s!"<circle cx=\"{x}\" cy=\"{y}\" r=\"9\" fill=\"{if isRoot then "#cc2222" else "#333"}\" />" ++
    s!"<text x=\"{x + 14}\" y=\"{y - 6}\" font-family=\"sans-serif\" font-size=\"13\" font-weight=\"bold\">w{w}{if isRoot then " (root)" else ""}</text>" ++
    s!"<text x=\"{x + 14}\" y=\"{y + 12}\" font-family=\"sans-serif\" font-size=\"12\" fill=\"#444\">{labelOf T G w}</text>"
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\" viewBox=\"0 0 {width} {height}\">\n" ++
  "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>\n" ++
  String.intercalate "\n" (les ++ rms ++ nodes) ++
  s!"\n<text x=\"20\" y=\"{height - 20}\" font-family=\"sans-serif\" font-size=\"12\" fill=\"#666\">grey = ≤ (Hasse), blue dashed = Rm; labels list the subformulae of {ppF G} each world forces</text>\n" ++
  "</svg>\n"

/-! ## 4. The certificate file -/

def certFile (T : Search.Tab) (nm : String) (Γ : List Form) (φ G : Form)
    (pins : Option (String × String)) : String :=
  -- Theorem 1 is stated with the dictionary names, theorem 2 with every
  -- abbreviation expanded.  The second is proved BY the first: `qk` is a
  -- `def`, so the two statements are definitionally equal and no reader
  -- has to scroll back to look a name up.
  let mkStmt := fun (src : Form → String) (suffix : String) =>
    match Γ with
    | [] => s!"theorem {nm}{suffix} : ([] : List PLLFormula) ⊬ {src φ}"
    | [γ] => s!"theorem {nm}{suffix} : [{src γ}] ⊬ {src φ}"
    | _ => s!"theorem {nm}{suffix} : ([] : List PLLFormula) ⊬ {src G}"
  let proof := match Γ with
    | [_] => s!"  not_entails_of_countermodel K_{nm} {nm}_force"
    | _ => s!"  not_derivable_of_countermodel K_{nm} {nm}_force"
  let stmt :=
    s!"/-- **{String.intercalate ", " (Γ.map ppF)} ⊬ {ppF φ}** — stated with the\n" ++
    s!"    RN(◯) dictionary names.  `{nm}_expanded` below says the same thing\n" ++
    "    with every name written out. -/\n" ++
    mkStmt srcNamed "" ++ " :=\n" ++ proof ++ "\n\n" ++
    s!"/-- The SAME statement, every abbreviation expanded — nothing to look up.\n" ++
    s!"    Definitionally equal to `{nm}`, so the proof is `{nm}` itself. -/\n" ++
    mkStmt srcPLL "_expanded" ++ s!" :=\n  {nm}"
  "/- GENERATED by `lake exe frjcert`.  Do not edit. -/\n" ++
  "import FRJ.Search.Pin\n" ++
  "import LaxLogic.RN.Reps\n\n" ++
  "open FRJ PLLND PLLFormula RNReps\n\n" ++
  s!"/-- The sequent: `{String.intercalate ", " (Γ.map ppF)} ⊢ {ppF φ}`,\n" ++
  s!"    searched as the goal `{ppF G}`. -/\n" ++
  Search.render T s!"cm_{nm}" ++ "\n" ++
  s!"theorem cm_{nm}_ok : (cm_{nm}).okB = true := by decide\n" ++
  s!"theorem cm_{nm}_root : (cm_{nm}).root < (cm_{nm}).n := by decide\n\n" ++
  s!"def K_{nm} : Kripke := (cm_{nm}).toKripke cm_{nm}_ok cm_{nm}_root\n\n" ++
  "set_option maxRecDepth 1000000 in\n" ++
  s!"theorem {nm}_force :\n" ++
  s!"    ¬ (K_{nm}).force (K_{nm}).root (ofPLL ({srcPLL G} : PLLFormula)) := by decide\n\n" ++
  stmt ++ "\n\n" ++
  "/-- Control: the model is not degenerate — it still forces `⊤`. -/\n" ++
  s!"theorem cm_{nm}_control :\n" ++
  s!"    (K_{nm}).force (K_{nm}).root (ofPLL (PLLFormula.ifThen PLLFormula.falsePLL PLLFormula.falsePLL)) := by decide\n\n" ++
  (match pins with
   | none =>
       -- FIRST PASS: unguarded, because the axiom strings are not known
       -- until Lean has been run.  Never left in this state (below).
       s!"#print axioms {nm}\n" ++ s!"#print axioms {nm}_expanded\n"
   | some (p1, p2) =>
       -- SECOND PASS: the strings Lean ITSELF printed, now CHECKED.  An
       -- unguarded `#print axioms` prints into a log and verifies
       -- nothing; a repo-wide scan on 2026-08-21 found 142 such pins, 39
       -- of them in `wip/rnFRJCerts.lean` — all emitted by this tool.
       s!"/-- info: {p1} -/\n#guard_msgs in\n#print axioms {nm}\n\n" ++
       s!"/-- info: {p2} -/\n#guard_msgs in\n#print axioms {nm}_expanded\n")

/-! ## 5. The driver -/

/-- Pull the payload out of one of Lean's own axiom lines.  Accepts both
shapes: `lake build` prefixes `file:line:col: info: `, a bare
`lake env lean` does not. -/
def axiomPayload (l : String) : Option String :=
  if (l.splitOn "depends on axioms:").length > 1
     || (l.splitOn "does not depend on any axioms").length > 1 then
    match l.splitOn "'" with
    | _ :: nm :: rest => some ("'" ++ nm ++ "'" ++ String.intercalate "'" rest)
    | _ => none
  else none

def hitModel (G : Form) (cfg : Search.Config) : Option Kripke :=
  let (db, _) := Search.saturateFast G cfg
  (db.rs.find? (fun x => decide (x.rhs = G))).map (fun x => modR x.der)

/-- **Exit codes are distinct, and this matters.**  Before 2026-08-21 a
frontier marker ("no derivation at this budget") and an engine defect
("Lean rejected the certificate this tool generated") both returned 1, so
no caller could tell a limitation from a bug.

    0  CHECKED — certificate emitted, and Lean accepted it
    1  LEAN REJECTED the generated certificate — an ENGINE DEFECT
    2  parse error in the sequent
    3  no derivation at this budget — a FRONTIER MARKER, not a verdict
    4  unknown `q<k>` index — a typo, refused rather than silently
       reinterpreted as an atom
    5  the emitted `#guard_msgs` pin did not match — a TOOL defect -/
def run (seq : String) (out : String) (cfg : Search.Config) : IO UInt32 := do
  match badQIndex seq with
  | some bad =>
      IO.println s!"ERROR: {bad} is not a representative — \
`LaxLogic/RN/Reps.lean` defines q0 … q{RNReps.reps.length - 1}.  Refusing: \
an unknown index used to become a fresh ATOM, which makes the search \
succeed on a formula you did not ask about."
      pure 4
  | none =>
  match parseSequent seq with
  | .error e => IO.println s!"parse error: {e}"; pure 2
  | .ok (Γ, φ) =>
    let G := Γ.foldr (fun γ acc => Form.imp γ acc) φ
    IO.println s!"sequent   {String.intercalate ", " (Γ.map ppF)} ⊢ {ppF φ}"
    IO.println s!"goal      {ppF G}"
    if Γ.length > 1 then
      IO.println s!"NOTE: {Γ.length} hypotheses — the certificate states the implication \
        form, not the sequent form (the bridge lemmas cover 0 and 1 hypotheses)."
    let t0 ← IO.monoMsNow
    match hitModel G cfg with
    | none =>
        let t1 ← IO.monoMsNow
        IO.println s!"NO DERIVATION at this budget [{t1-t0} ms] (rounds={cfg.rounds}, \
          jmax={cfg.jmax}, pmax={cfg.pmax}, lamCap={cfg.lamCap}, maxRS={cfg.maxRS}, \
          maxIS={cfg.maxIS}) — a frontier marker, not a verdict."
        pure 3
    | some K =>
        let t1 ← IO.monoMsNow
        let T0 := Search.tabOf K (Search.atomsOf G)
        let T := T0.minimise G
        IO.println s!"search    {t1-t0} ms; model {T0.n} worlds → minimised {T.n}, \
          frame-ok={T.okB}, refutes={T.refutes G}"
        -- With more than one hypothesis the bridge lemmas do not reach the
        -- SEQUENT form, so the certificate states the IMPLICATION.  The
        -- name now says so: a file outlives the run that printed the NOTE.
        let base := ((out.splitOn "/").getLastD out).replace "-" "_"
        let nm := if Γ.length > 1 then base ++ "_implForm" else base
        let leanPath := out ++ ".lean"
        let svgPath := out ++ ".svg"
        IO.FS.writeFile leanPath (certFile T nm Γ φ G none)
        IO.FS.writeFile svgPath (toSvg T G)
        IO.println s!"wrote     {leanPath}, {svgPath}"
        IO.println "checking with Lean (pass 1: unguarded pins) …"
        let r ← IO.Process.output { cmd := "lake", args := #["env", "lean", leanPath] }
        let txt := r.stdout ++ r.stderr
        IO.println s!"lean exit {r.exitCode}"
        for l in txt.splitOn "\n" do
          if !l.isEmpty then IO.println s!"  | {l}"
        if r.exitCode != 0 then
          IO.println s!"VERDICT   LEAN REJECTED the generated certificate (exit {r.exitCode})."
          IO.println "          That is an ENGINE DEFECT, not a search limitation."
          pure 1
        else
          -- PASS 2: re-emit with the axiom strings Lean itself printed,
          -- now under `#guard_msgs`, and re-check.  Without this the
          -- committed file's pin is unchecked forever after.
          match (txt.splitOn "\n").filterMap axiomPayload with
          | p1 :: p2 :: _ =>
              IO.FS.writeFile leanPath (certFile T nm Γ φ G (some (p1, p2)))
              IO.println "checking with Lean (pass 2: #guard_msgs-checked pins) …"
              let r2 ← IO.Process.output { cmd := "lake", args := #["env", "lean", leanPath] }
              let txt2 := r2.stdout ++ r2.stderr
              for l in txt2.splitOn "\n" do
                if !l.isEmpty then IO.println s!"  | {l}"
              if r2.exitCode == 0 then
                IO.println s!"VERDICT   CHECKED — {nm} holds, sorry-free, pins GUARDED."
                pure 0
              else
                IO.println s!"VERDICT   the emitted #guard_msgs pin did not match \
(exit {r2.exitCode}) — a TOOL defect, not a result."
                pure 5
          | _ =>
              IO.println "VERDICT   Lean accepted the certificate but printed no axiom \
lines to guard — emitter defect."
              pure 5

end FrjCert

def main (args : List String) : IO UInt32 := do
  let seq := args.getD 0 "q10 ⊢ q10 ∧ q13"
  let out := args.getD 1 "docs/frjcert-out"
  let rounds := ((args.getD 2 "10").toNat?).getD 10
  FrjCert.run seq out { rounds := rounds }
